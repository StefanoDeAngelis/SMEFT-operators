(* ::Package:: *)

(* ::Chapter:: *)
(*Helicity Structures*)


BeginPackage["HelicityStructures`",{"SpinorHelicity6D`","GraphGenerator`","YoungSymm`"}]


(* ::Section:: *)
(*Messages*)


PrimaryAmplitudeHelicityFields::usage = "..."
PrimaryAmplitudeHelicity::usage = "..."
AmplitudesStructure::usage = "..."
AmplitudesScalars::usage = "..."

IndependentFormFactors::usage = "..."
IndependentHelicityFactors::usage = "..."

SchoutenIdentities::usage = "..."
SingleStructureIdentities::usage = "..."
AllIdentities::usage = "..."


(* ::Section:: *)
(*Classification*)


Begin["`Private`"]


(* ::Subsection:: *)
(*General structures*)


(* ::Subsubsection::Closed:: *)
(*Primary Amplitudes (spin classification)*)


PrimaryAmplitudeHelicityFields[d_]:= (*This function generates all the possible combination of helicity-charged fields compatible with the dimension of the operator*)
	Flatten[
		Table[
			If[(2*i+3/2*j)<= d,{i,j(*,h*)},Nothing], (*The condition for the field number is 2*#gluons + 3/2*#fermions \[LessEqual] dimension of the operator*)
			{i,0,IntegerPart[d/2]},{j,0,IntegerPart[2*d/3],2}
		],
	1]


(* ::Subsubsection::Closed:: *)
(*Primary Amplitudes (helicity configuration)*)


PrimaryAmplitudeHelicity[d_]:= (*A more refined version of the previous function which distinguishes between helicity configurations*)
	Sort[
		Flatten[
			Table[
				If[
					((3/2*(fermM+fermP)+2*(gluonsM+gluonsP))<= d)(*&&(gluonsM+1/2*fermM>=gluonsP+1/2*fermP)*), (*The second condition is the restiction to the configurations for which the total helicity is non-positive*)
					{{gluonsM,gluonsP},{fermM,fermP}},
					Nothing
				],
				{gluonsM,0,IntegerPart[d/2]},{gluonsP,0,IntegerPart[d/2]},{fermM,0,IntegerPart[2*d/3]},{fermP,0,IntegerPart[2*d/3]}
			],
		3]
	]


(* ::Subsubsection::Closed:: *)
(*Amplitude structures (with derivatives)*)


AmplitudesStructure[d_]:= (*This function assign all the compatible derivative number of the operator to the previously generated helicity configurations*)
	Flatten[
		Map[
			Table[
				If[
					(EvenQ[der+#[[2,1]]])&& (*The first four conditions come from the representation theory and they check whether is possible to form a Lorentz singlet*)
						(EvenQ[der+#[[2,2]]])&&
						(#[[1,1]]!=1||((#[[2,1]]+der )>=1))&&
						(#[[1,2]]!=1||((#[[2,2]]+der )>=1))&&
						(der<d-1)&&(*The operator has to have at least two fields in it*)
						((d-#[[1,1]]-#[[1,2]]-1/2*#[[2,1]]-1/2*#[[2,2]]-der)>3||der==0)(*three- and two- point minimal form factor do not contribute due to three-point kinematics and IBP+on-shellness respectively*),
					Append[#,der],
					Nothing
				],
			{der,0,IntegerPart[d-2*(#[[1,1]]+#[[1,2]])-3/2*(#[[2,1]]+#[[2,2]])]}]&,
			PrimaryAmplitudeHelicity[d]
		],
	1]


(* ::Subsubsection::Closed:: *)
(*Amplitudes structures (with scalars)*)


AmplitudesScalars[d_]:=
	Module[{structures=AmplitudesStructure[d],i},
		For[i=1,i<=Length[structures],i++,
			structures[[i,3]]=d-2*(structures[[i,1,1]]+structures[[i,1,2]])-3/2*(structures[[i,2,1]]+structures[[i,2,2]])-structures[[i,3]]
		];
		Return[structures];
	]


(* ::Subsubsection::Closed:: *)
(*Number of fields*)


NumberFields[d_][{{gM_,gP_},{fM_,fP_},der_}]:=d-gM-gP-1/2*(fM+fP)-der


(* ::Subsection:: *)
(*Helicity and momentum structures*)


(* ::Subsubsection::Closed:: *)
(*Helicity structure*)


HelicityStructure[d_][{{gluonsM_,gluonsP_},{fermM_,fermP_},ders_}]:=
	Module[{angles,squares},

		angles=
			Flatten[
				Join[
					Table[{i,i},{i,1,gluonsM}], (*couples of gluon labels for the helicity structure*)
					Table[{j},{j,gluonsM+gluonsP+1,gluonsM+gluonsP+fermM}] (*single fermion label for each fermion*)
				],
			2];

		squares=
			Flatten[
				Join[
					Table[{i,i},{i,gluonsM+1,gluonsM+gluonsP}],
					Table[{j},{j,gluonsM+gluonsP+fermM+1,gluonsM+gluonsP+fermM+fermP}]
				],
			2];

		Return[{angles,squares}];

	]


(* ::Subsubsection::Closed:: *)
(*Partition of momenta*)


PartitionMomenta[moms_List,partition_List]:= (*Given a certain partition and a list of momenta of certain fields (e.g. helicity minus gluons), this function repeat and order the momenta according to the partition*) (*in the following function, this function will encounter some zeros, instead of a list associated to a partition. In this case it gives Nothing*)
		Flatten[
			Table[
				moms[[i]],
				{i,1,Length[partition]},
				{j,1,partition[[i]]} (*repeat the corresponding object as many times as it says the element of the partition*)
			] (*do it for all the elements of the partition*)
		]


(* ::Subsubsection::Closed:: *)
(*Momenta Selection*)


MomentaSelection[d_][{{gluonsM_,gluonsP_},{fermM_,fermP_},ders_}]:= (*generates all the independent momenta, their corresponding partitions of partitions and assign all of them to the lists of momenta*)
	Module[{scals=d-2(gluonsM+gluonsP)-3/2*(fermM+fermP)-ders,moms,partitions,numberfields},
		If[scals<0,Message[MomentaSelection::negative];Return[Null]];
		numberfields=gluonsM+gluonsP+fermM+fermP+scals;
		moms=Table[i,{i,1,numberfields-1}];(*momentum conservation is not taken into account simply by eliminating the last momentum. There are cases (for d\[GreaterEqual]7) where the last momentum gives automatically zero,
		and then we need to exclude the second last momentum, and so forth.*)
		partitions=
			Flatten[
				Permutations/@
					(PadRight[#,numberfields-1]&/@
						IntegerPartitions[ders,numberfields-1]),
				1
			];
		moms=PartitionMomenta[moms,#]&/@partitions;
		Return[moms]
]


MomentaSelection::negative="The number of scalars is negative"


(* ::Subsubsection::Closed:: *)
(*Spinor structures*)


SpinorStructure[d_Integer][{{gluonsM_Integer,gluonsP_Integer},{fermM_Integer,fermP_Integer},ders_Integer}]:= (*appends the list of momenta to both the angles and the squares bracket lists*)
	Module[{helicity,momentas,spinors},
		helicity=HelicityStructure[d][{{gluonsM,gluonsP},{fermM,fermP},ders}];
		momentas=MomentaSelection[d][{{gluonsM,gluonsP},{fermM,fermP},ders}];
		spinors=
			Table[
				Join[momentas[[n]],#]&/@helicity,
				{n,1,Length[momentas]}
			];
		spinors=
			Map[
				Sort[#]&,
				spinors,
				{2}
			];
		Return[spinors];
	]


(* ::Subsubsection::Closed:: *)
(*Is a singlet doable?*)


(* ::Text:: *)
(*This function can be suppressed in the future to speed up the computation. The momenta and the helicity structures can be generated simply with numbers associated to each leg, as in IndependentHelicityFactors.*)


IsSingletDoable[n_][{List1_List,List2_List}]:= (*the counting of one element can never exceed half of the total number of countings*)
	Module[{test1,test2,zeros},
		(*List1 and List2 are made of repeated elements, for example {1,1,1,2,2,3,3,6}*)
		
		zeros=Map[{#,0}&,{Complement[#,List1],Complement[#,List2]}&@Range[n],{2}];
		
		test1=
			And@@
				Table[
					#1[[i]]<=#2/2 ,
					{i,1,Length[#1]}
				]&[Counts[List1],Length[List1]];

		test2=
			And@@
				Table[
					#1[[i]]<=#2/2 ,
					{i,1,Length[#1]}
				]&[Counts[List2],Length[List2]];

		If[
			test1&&test2,
			Return[Sort/@Join@@@Transpose[{{Tally[List1],Tally[List2]},zeros}]],
			Return[Nothing];
		];
	]


(* ::Section:: *)
(*Form Factors & Helicity Factors*)


(* ::Subsubsection::Closed:: *)
(*From Adjacency Matrices to Spinor Formula*)


FromMatrixToSpinorsAngle[adjAngle_?MatrixQ,labels_List]:=
	Times@@
		(SpinorAngleBracket[labels[[#[[1,1]]]],labels[[#[[1,2]]]]]^#[[2]]&/@Transpose[{adjAngle["NonzeroPositions"],adjAngle["NonzeroValues"]}])
		
FromMatrixToSpinorsSquare[adjSquare_?MatrixQ,labels_List]:=
	Times@@
		(SpinorSquareBracket[labels[[#[[1,1]]]],labels[[#[[1,2]]]]]^#[[2]]&/@Transpose[{adjSquare["NonzeroPositions"],adjSquare["NonzeroValues"]}])

FromMatrixToSpinors[{adjAngle_?MatrixQ,adjSquare_?MatrixQ},labels_List]:=
	Times@@
		(SpinorAngleBracket[labels[[#[[1,1]]]],labels[[#[[1,2]]]]]^#[[2]]&/@Transpose[{adjAngle["NonzeroPositions"],adjAngle["NonzeroValues"]}])*
	Times@@
		(SpinorSquareBracket[labels[[#[[1,1]]]],labels[[#[[1,2]]]]]^#[[2]]&/@Transpose[{adjSquare["NonzeroPositions"],adjSquare["NonzeroValues"]}])


(* ::Subsubsection::Closed:: *)
(*Momentum Conservation*)


PlanarMomentumConservation[{angles_,squares_}]:=
	Module[{nonzeroangles=angles["NonzeroPositions"],nonzerosquares=squares["NonzeroPositions"],n=Length[angles]},
		If[
			(MemberQ[nonzeroangles,{1,n-1}]&&MemberQ[nonzerosquares,{1,n-1}])||
			(MemberQ[nonzeroangles,{n-1,n}]&&MemberQ[nonzerosquares,{_,n-1}])||
			(MemberQ[nonzerosquares,{n-1,n}]&&MemberQ[nonzeroangles,{_,n-1}])||
			(MemberQ[nonzerosquares,{1,n}]&&MemberQ[nonzeroangles,{1,n-1}])||
			(MemberQ[nonzerosquares,{1,n-1}]&&MemberQ[nonzeroangles,{1,n}]),
			Return[Nothing],
			Return[{angles,squares}]
		]
	]


(* ::Subsubsection:: *)
(*From structure to Angles&Squares structures*)


Options[HelicityStructures]={"MomentumConservation"->True}

HelicityStructures[{anglestructure_List,squarestructure_List},OptionsPattern[]]:=
	Module[{formfactors,angles,squares},

		angles=AllNonIntersectingGraphs[Part[#,2]&/@anglestructure];
		squares=AllNonIntersectingGraphs[Part[#,2]&/@squarestructure];

		formfactors=Tuples[{angles,squares}];
		
		If[TrueQ@OptionValue["MomentumConservation"],
			If[
				anglestructure[[-2,2]]+squarestructure[[-2,2]]!=0||anglestructure[[1,2]]+squarestructure[[1,2]]!=0,
				formfactors=PlanarMomentumConservation/@formfactors
			]
		];
	
		formfactors=FromMatrixToSpinors[#,Part[#,1]&/@anglestructure]&/@formfactors;
	
		Return[formfactors];
	]


(* ::Subsection::Closed:: *)
(*Independent Form Factors*)


Options[IndependentFormFactors]={"MatterContent"->True}

IndependentFormFactors[d_Integer,OptionsPattern[]]:=
	Module[{structures},
		
		structures=IsSingletDoable[#1][#2]&@@@Thread[{NumberFields[d][#],SpinorStructure[d][#]}]&/@AmplitudesStructure[d];

		If[
			OptionValue["MatterContent"],
			
			structures=Thread[{(*List/@*)Flatten/@AmplitudesScalars[d],structures}];
			structures=MapAt[HelicityStructures,#,{2,All}]&/@structures;
			structures=(*Tuples@*)(MapAt[Flatten,#,2]&/@structures),
			
			structures=Flatten[structures,1];
			structures=Flatten[HelicityStructures[#]&/@structures]
		]
	]


(* ::Subsection::Closed:: *)
(*Independent Helicity Factors*)


Options[IndependentHelicityFactors]={"MomentumConservation"->True}

IndependentHelicityFactors[dim_Integer,OptionsPattern[]][list__?(Length[#]==2 && IntegerQ[2*#[[2]]]&)]:=
	Module[{labels=Part[#,1]&/@{list},angles,squares,structures},
	
		{angles,squares}={Abs[#]-#,Abs[#]+#}&@(Part[#,2]&/@{list});
		
		If[
			TrueQ@OptionValue["MomentumConservation"],
			structures=Append[#,0]&/@PermutationsOfPartitions[dim-Total[angles]/2-Total[squares]/2,Length[angles]-1],
			structures=PermutationsOfPartitions[dim-Total[angles]/2-Total[squares]/2,Length[angles]]
		];
		
		structures={angles+#,squares+#}&/@structures;
		
		structures=If[Length[#]<2,Nothing,#]&/@Map[IsLoopLessDoable,structures,{2}];
		
		structures=HelicityStructures[#,"MomentumConservation"->OptionValue["MomentumConservation"]]&/@Map[Thread[{labels,#}]&,structures,{2}];
		
		Return[Flatten@structures]
	]


(* ::Subsection:: *)
(*All Identities*)


(* ::Subsubsection::Closed:: *)
(*Schouten Identities*)


Options[SchoutenIdentities]={"Bracket"->"Null"}

SchoutenIdentities[{lines__Integer},labels_List,OptionsPattern[]]:=
	Block[{intersecting,numberinter,nonintersecting,numbernoninter,replacements,graphlabels,x,y},
		
		intersecting=AllGraphs[{lines}]; (*generate all graphs*)

		nonintersecting=AllNonIntersectingGraphs[{lines}]; (*select non-intersecting graphs*)

		intersecting=Complement[intersecting,nonintersecting]; (*complement to select the intersecting graphs*)
		numberinter=Length[intersecting];
		numbernoninter=Length[nonintersecting];
		
		graphlabels=
			Join[
				Table[
					{intersecting[[i]],x[i]}, (*assign labels to intersecting and intersecting graphs*)
					{i,1,numberinter}
				],
				Table[
					{nonintersecting[[i]],y[i]}, (*assign labels to intersecting and non-intersecting graphs*)
					{i,1,numbernoninter}
				]
			];

		replacements=
			Table[
				x[i]->If[OptionValue["Bracket"]==="Null",#,Total[#]]&@(SchoutenCrossing[intersecting[[i]]]/.(Rule@@@graphlabels)),
				{i,1,numberinter}
			];
			
		If[
			OptionValue["Bracket"]==="Angle",
			graphlabels=MapAt[FromMatrixToSpinorsAngle[#,labels]&,#,{1}]&/@graphlabels,
			If[
				OptionValue["Bracket"]==="Square",
				graphlabels=MapAt[FromMatrixToSpinorsSquare[#,labels]&,#,{1}]&/@graphlabels
			]
		];
		
		graphlabels=Reverse/@Rule@@@graphlabels;
			
		replacements=
			Join[
				Table[
					{y[i],y[i]}/.graphlabels,
					{i,1,numbernoninter}
				],
				Table[
					{x[i] , Flatten[x[i]//.replacements]}/.graphlabels,
					{i,1,numberinter}
				]
			]; (*placing the repeated replacements inside the list speeds the function up*)

		Return[replacements];

]


(* ::Subsubsection::Closed:: *)
(*Schouten + Momentum conservation for a single structure*)


SingleStructureIdentities[{{linesAngles__Integer},{linesSquares__Integer}},labels_List]:= (*for the momentum identities to work fine, it is necessary that the labels are ordered*)
	Block[{allstructures,schoutened,Simp,length=Length[labels]},
	
		allstructures=AllGraphs/@{{linesAngles},{linesSquares}};
		allstructures=
			{FromMatrixToSpinorsAngle[#,labels]&/@allstructures[[1]],
			FromMatrixToSpinorsSquare[#,labels]&/@allstructures[[2]]};
		(*allstructures=
			MapAt[FromMatrixToSpinorsAngle[#,labels]&/@#&,#,{1}]&@allstructures;
		allstructures=
			MapAt[FromMatrixToSpinorsSquare[#,labels]&/@#&,#,{2}]&@allstructures;*)
		
		allstructures=Tuples@allstructures;
		schoutened=allstructures;
		allstructures=Times@@@allstructures;
		
		(*If[
			{linesAngles}[[-1]]!=0&&{linesSquares}[[-1]]!=0,
			schoutened=Times@@@schoutened;
			schoutened=
				Expand/@
					ReplaceRepeated[
						schoutened,
						Flatten@(
							Table[
								SpinorAngleBracket[i,#1]^a_. SpinorSquareBracket[j,#1]^b_.:>Evaluate[(Sum[-SpinorAngleBracket[i,k]SpinorSquareBracket[j,k],{k,#2}])^Min[a,b] SpinorAngleBracket[i,#1]^Max[a-b,0] SpinorSquareBracket[j,#1]^Max[b-a,0]],
								{i,#2},{j,#2}
							]&[labels[[-1]],Drop[labels,-1]]
						)
					];
			Return[Transpose[{allstructures,schoutened}]]
		];*)
		
		Set@@@
			(MapAt[Simp,#,{1}]&/@
				Join[
				SchoutenIdentities[{linesAngles},labels,"Bracket"->"Angle"],
				SchoutenIdentities[{linesSquares},labels,"Bracket"->"Square"]
			]);
		
		schoutened=Times@@@Map[Simp,schoutened,{2}];
		schoutened=Expand/@schoutened; (*very slow step*)
		
		(*Set@@@Transpose[{Simp/@allstructures,schoutened}];*)(*this step is not needed because after momentum conservation the
		resulting structures are not those given by {{linesAngles,linesSquares}}*)
		
		If[
			{linesAngles}[[-2]]!=0&&{linesSquares}[[-2]]!=0,
			If[
				{linesSquares}[[-1]]!=0,
				schoutened=
					Expand/@
						ReplaceRepeated[
							schoutened,
							Table[
								SpinorAngleBracket[i,#1]^\[Alpha]_. SpinorSquareBracket[#1,#2]^\[Beta]_.:>Evaluate[Sum[-SpinorAngleBracket[i,j]SpinorSquareBracket[j,#2],{j,#3}]^Min[\[Alpha],\[Beta]]*SpinorAngleBracket[i,#1]^Max[\[Alpha]-\[Beta],0] SpinorSquareBracket[#1,#2]^Max[\[Beta]-\[Alpha],0]],
								{i,#3}
							]&[labels[[-2]],labels[[-1]],Drop[labels,-2]]
						]
			];
			If[
				{linesAngles}[[-1]]!=0,
				schoutened=
					Expand/@
						ReplaceRepeated[
							schoutened,
							Table[
								SpinorSquareBracket[i,#1]^a_. SpinorAngleBracket[#1,#2]^b_.:>Evaluate[Sum[-SpinorSquareBracket[i,j]SpinorAngleBracket[j,#2],{j,#3}]^Min[a,b]*SpinorSquareBracket[i,#1]^Max[a-b,0] SpinorAngleBracket[#1,#2]^Max[b-a,0]],
								{i,#3}
							]&[labels[[-2]],labels[[-1]],Drop[labels,-2]]
						]
			];
			If[
				{linesAngles}[[1]]!=0&&{linesSquares}[[1]]!=0,
				schoutened=
					ReplaceAll[
						schoutened,
						SpinorAngleBracket[#1,#2]^a_. SpinorSquareBracket[#1,#2]^b_.:>Evaluate[(1/2*Sum[-SpinorAngleBracket[i,j]SpinorSquareBracket[i,j],{i,#3},{j,#3}]-Sum[SpinorAngleBracket[#1,j]SpinorSquareBracket[#1,j],{j,Drop[#3,-1]}])^Min[a,b] SpinorAngleBracket[#1,#2]^Max[a-b,0] SpinorSquareBracket[#1,#2]^Max[b-a,0]]
					]&[labels[[1]],labels[[-2]],Drop[RotateLeft[labels],-2]]
			]
		];
		
		If[
			{linesAngles}[[1]]!=0&&{linesSquares}[[1]]!=0&&({linesAngles}[[-1]]!=0||{linesSquares}[[-1]]!=0),
			If[
				{linesAngles}[[-1]]==0,
				schoutened=
					ReplaceAll[
						schoutened,
						SpinorAngleBracket[#1,#2]^a_.*SpinorSquareBracket[#1,#3]^b_.:>Evaluate[Sum[-SpinorAngleBracket[j,#2]*SpinorSquareBracket[j,#3],{j,#4}]^Min[a,b] SpinorAngleBracket[#1,#2]^Max[a-b,0]*SpinorSquareBracket[#1,#3]^Max[b-a,0]]
					]&[labels[[1]],labels[[-2]],labels[[-1]],Drop[RotateLeft[labels],-3]],
				schoutened=
					ReplaceAll[
						schoutened,
						SpinorSquareBracket[#1,#2]^a_.*SpinorAngleBracket[#1,#3]^b_.:>Evaluate[Sum[-SpinorSquareBracket[j,#2]*SpinorAngleBracket[j,#3],{j,#4}]^Min[a,b] SpinorSquareBracket[#1,#2]^Max[a-b,0]*SpinorAngleBracket[#1,#3]^Max[b-a,0]]
					]&[labels[[1]],labels[[-2]],labels[[-1]],Drop[RotateLeft[labels],-3]]
			]
		];
		
		Return[Transpose[{allstructures,Expand/@schoutened}]]
	]


(* ::Subsubsection::Closed:: *)
(*All Identities*)


(* ::Text:: *)
(*TODO: regardless of the order in which the labels are given, we should make  them ordered*)


AllIdentities[dim_Integer][list__?(Length[#]==2 && IntegerQ[2*#[[2]]]&)]:=
	Block[{labels=Part[#,1]&/@{list},angles,squares,structures,Simp},

		{angles,squares}={Abs[#]-#,Abs[#]+#}&@(Part[#,2]&/@{list});

		structures=Append[#,0]&/@PermutationsOfPartitions[dim-Total[angles]/2-Total[squares]/2,Length[angles]-1];

		structures={angles+#,squares+#}&/@structures;

		structures=If[Length[#]<2,Nothing,#]&/@Map[IsLoopLessDoable,structures,{2}];

		structures=SingleStructureIdentities[#,labels]&/@structures;
		
		structures=Join@@structures;
		
		Simp[x_Plus]:=Plus@@(Simp/@List@@x);
		Simp[Times[N_*a___]]/;NumberQ[N]:=Expand[N*Simp[Times[a]]];
		
		Set@@@(MapAt[Simp,#,1]&/@structures);
		
		structures=MapAt[Simp,#,2]&/@structures (*this step could be very slow, it could be interesting to see if
		mapping twice Simp in the expression to simplify could be faster, skipping the 'Simp' part of this function*)
	]


End[]


(* ::Section:: *)
(*Attributes*)


Protect@@Names["HelicityStructures`*"]


EndPackage[]
