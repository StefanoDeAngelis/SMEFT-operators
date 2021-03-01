(* ::Package:: *)

(* ::Chapter:: *)
(*GraphGenerator*)


BeginPackage["GraphGenerator`"]


(* ::Section:: *)
(*Messages*)


PermutationsOfPartitions::usage = "..."
PermutationMatrix::usage = "..."
IsLoopLessDoable::usage = "..."
AssignLines::usage = "..."
AllGraphs::usage = "..."
IsGraphNonIntesercting::usage = "..."
AllNonIntersectionGraphs::usage = "..."
SchoutenCrossing::usage = "..."
DrawAdjacencyGraph::usage = "..."


(* ::Section:: *)
(*Private*)


Begin["`Private`"]


(* ::Subsection::Closed:: *)
(*Permutations of Partitions*)


PermutationsOfPartitions[counting_,length_]:= (*this function generates the permutations of partitions of a give integer number counting_ into length_ elements (with zeros)*)
	Flatten[
		Map[
			Permutations,
				Map[
					PadRight[#,length]&, (*PadRight inserts additional zero (if needed) such that the results permutation of a given partition gives length_ elem*)
					IntegerPartitions[counting,length] (*The second argument is necessary in the case we more edges than vertices*)
				]
		],
		1
	]


(* ::Subsection::Closed:: *)
(*Permutation Matrix*)


PermutationMatrix[p_List]:=IdentityMatrix[Length[p]][[p]]


(* ::Subsection:: *)
(*Is a loop-less graph doable?*)


IsLoopLessDoable[lines_List]:= (*given the list of lines coming out from each point, this function tests if a loopless diagram is doable*)
	Module[{totalines},

		totalines=Sum[lines[[i]],{i,Length[lines]}];

		If[
			(*(And@@NonNegative[lines])&&*) (*to make sense, the number of lines cannot be negative*)
			(And@@
			(LessEqual[#,totalines/2]&/@lines) (*the number of lines coming out of one point cannot be greater than the number of lines coming out of all the remaining points*)
			),

			Return[lines],

			Return[Nothing]
		]
	]


(* ::Subsection::Closed:: *)
(*Lines assignment*)


AssignLines[{assignedlines_List,availablelines_List}]:=
	Module[{withoutfirst,newavailablelines,newassignedlines,adjacencymatrix,combinations},

		If[
			Length[availablelines]>2, (*the case with two points is trivial and we deal with it separately*)

			withoutfirst=Drop[availablelines,1]; (*consider the first point and drop it from the initial list*)
			newassignedlines=PermutationsOfPartitions[availablelines[[1]],Length[availablelines]-1]; (*the lines of the first point can be assigned to the remaing points in all the possible combinations, given by the permutations of partitions*)

			newavailablelines=IsLoopLessDoable[withoutfirst-#]&/@newassignedlines; (*not all the combinations are allowed*)
			(*these are the remaining lines per point*)
			combinations=Length[newavailablelines];

			newassignedlines=(withoutfirst-#)&/@newavailablelines;
			newassignedlines=Table[Join[assignedlines,{newassignedlines[[i]]}],{i,1,combinations}]; (*append the combination in which the lines have been distributed to the list of combinations at higher points*)

			adjacencymatrix=Table[{newassignedlines[[i]],newavailablelines[[i]]},{i,1,combinations}]; (*all the rows of the adjacency matrices*)
			Return[adjacencymatrix],
			
			If[
				availablelines[[1]]==availablelines[[2]],(*if the number of lines from two points are different, the graph is not possible*)

				(adjacencymatrix={Join[assignedlines,{{availablelines[[1]]}(*,{}*)(*the void list is needed with the present GraphToMatrix function, but it has to be eliminated with the previous version*)}]};
				Return[adjacencymatrix];),

				Return[Nothing];
			]
		]
	]


(* ::Subsection::Closed:: *)
(*Graph to Matrix*)


GraphToMatrix[list_List]:= (*from the graph (the assigned lines), this gives the adjacency matrix*)
	Table[
			If[j==i,
				0,(*no loops, please!*)
				If[j>i,
					list[[i,j-i]],
					(*0*)list[[j,i-j]] (*we considered so fare the adjacency matrix to be symmetric in this case, because direction (which fixes the overall sign of the diagram) is not needed when we look at the independent combinations*)
				]
			],
			{i,1,Length[list]+1},
			{j,1,Length[list[[1]]]+1}
		]
(*GraphToMatrix[list_List]:=(#+Transpose[#])&@(PadLeft[#,Length[list[[1]]]+1]&/@list)*)


(* ::Subsection:: *)
(*All graphs*)


AllGraphs[lines_List]:=
	Module[{adjacencymatrices,perm=PermutationMatrix[Ordering[lines]],locallines=Sort[DeleteCases[lines,0]],i},
	
		(*If[locallines==={},Return[{Table[0,#,#]&@Count[lines,0]}]];*)
		(*If[locallines==={},Return[{{0}}]];*)
		If[locallines==={},Return[{SparseArray[{},{#,#}]&@Count[lines,0]}]];

		adjacencymatrices=AssignLines[{{},locallines}];

		For[i=1,i<=Length[locallines]-2,i++,
			adjacencymatrices=Flatten[AssignLines/@adjacencymatrices,1];
		]; (*repeat the procedure above until all the lines coming out all the points are assigned*)
		
		adjacencymatrices=ArrayPad[#,{Count[lines,0],0}]&/@(GraphToMatrix/@adjacencymatrices);
		
		adjacencymatrices=(Inverse[perm] . # . perm)&/@adjacencymatrices;
		
		adjacencymatrices=SparseArray/@UpperTriangularize/@adjacencymatrices;

		Return[adjacencymatrices];
	]


(* ::Subsection::Closed:: *)
(*Is the graph without crossings?*)


(* ::Text:: *)
(*TODO: How to generate planar graphs without additional conditions?*)


Options[IsGraphNonIntesercting]={"Intersecting"->False};

IsGraphNonIntesercting[adjacencymatrix_?(MatrixQ[#]&),OptionsPattern[]]:=
	Module[{matrixdim=Length[adjacencymatrix],i,j},
		For[i=1,i<=matrixdim,i++,
			For[j=i+2,j<=matrixdim-1,j++,
				If[
					adjacencymatrix[[i,j]]!=0, (*the non-intersection condition translated to the matrix language*)
					If[
						Sum[adjacencymatrix[[k,l]],{k,i+1,j-1},{l,j+1,matrixdim}]!=0,
						If[
							OptionValue["Intersecting"],
							Return[adjacencymatrix],
							Return[Nothing]
						];
					]
				]
			]
		];
		If[
			OptionValue["Intersecting"],
			Return[Nothing],
			Return[adjacencymatrix]
		]
	]


(* ::Subsection::Closed:: *)
(*All the Non-Intersecting Graphs*)


AllNonIntersectionGraphs[lines_List]:=
	IsGraphNonIntesercting/@AllGraphs[lines]


(* ::Subsection::Closed:: *)
(*Schouten = loosen crossings*)


(*This function loosen ONE of the crossings in the graphs.*)


SchoutenCrossing[adjacencymatrix_List]:=
	Module[{matrixdim=Length[adjacencymatrix],positions={},matrix1,matrix2},
		Do[
			If[
				adjacencymatrix[[i,j]]!=0,
				If[
					adjacencymatrix[[k,l]]!=0,
					positions={i,k,j,l};
					Break[];
				]
			],
			{i,1,matrixdim},
			{j,i+2,matrixdim-1},
			{k,i+1,j-1},
			{l,j+1,matrixdim}
		];
		
		If[
			positions!={},
			
			matrix1=adjacencymatrix;
			matrix1[[positions[[1]],positions[[3]]]]+=-1;
			matrix1[[positions[[2]],positions[[4]]]]+=-1;
			matrix2=matrix1;
			matrix1[[positions[[1]],positions[[2]]]]++;
			matrix1[[positions[[3]],positions[[4]]]]++;
			matrix2[[positions[[1]],positions[[4]]]]++;
			matrix2[[positions[[2]],positions[[3]]]]++;
			
			Return[{matrix1,matrix2}],
			
			Return[adjacencymatrix]
		];
	]


(*Instead of untie recursively all the crossings we can choose to untie the first one for all the graphs (this gives an loosening rule) and then substitute recursively. Slower (about x10): count the intersections as Sum[adjacencymatrix[[k,l]]] / use the IsGraphNonIntersecting, and apply recursively the SchoutenCrossing.*)


(* ::Subsection::Closed:: *)
(*Draw graph*)


ellipseLayout[n_,{a_,b_}]:=Table[{a Cos[Pi-2 Pi/n *u],b Sin[Pi-2 Pi/n* u]},{u,1,n}];

DrawAdjacencyGraph[adjacencymatrix_]:=(AdjacencyGraph[#,VertexCoordinates->ellipseLayout[Length[#],{1,1}]])&@adjacencymatrix


End[]


(* ::Section:: *)
(*Attributes*)


Protect@@Names["GraphGenerator`*"]


EndPackage[]
