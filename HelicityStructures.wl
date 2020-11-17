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
HelicityStructure::usage = "..."
PartitionMomenta::usage = "..."
MomentaSelection::usage = "..."
SpinorStructure::usage = "..."
CountsToList::usage = "..."
IsSingletDoable::usage = "..."

BracketBox::usage = "..."
Bracket::usage = "..."
FromMatrixToSpinors::usage = "..."
FromStructuresToSpinors::usage = "..."
AnglesAndSquares::usage = "..."


(* ::Section:: *)
(*Classification*)


Begin["`Classification`"]


(* ::Subsection:: *)
(*General structures*)


(* ::Subsubsection:: *)
(*Primary Amplitudes (spin classification)*)


PrimaryAmplitudeHelicityFields[d_]:= (*This function generates all the possible combination of helicity-charged fields compatible with the dimension of the operator*)
	Flatten[
		Table[
			If[(2*i+3/2*j)<= d,{i,j(*,h*)},Nothing], (*The condition for the field number is 2*#gluons + 3/2*#fermions \[LessEqual] dimension of the operator*)
			{i,0,IntegerPart[d/2]},{j,0,IntegerPart[2*d/3],2}
		],
	1]


(* ::Subsubsection:: *)
(*Primary Amplitudes (helicity configuration)*)


PrimaryAmplitudeHelicity[d_]:= (*A more refined version of the previous function which distinguishes between helicity configurations*)
	Flatten[
		Table[
			If[
				((3/2*(fermM+fermP)+2*(gluonsM+gluonsP))<= d)&&(gluonsM+1/2*fermM>=gluonsP+1/2*fermP), (*The second condition is the restiction to the configurations for which the total helicity is non-positive*)
				{{gluonsM,gluonsP},{fermM,fermP}},
				Nothing
			],
			{gluonsM,0,IntegerPart[d/2]},{gluonsP,0,IntegerPart[d/2]},{fermM,0,IntegerPart[2*d/3]},{fermP,0,IntegerPart[2*d/3]}
		],
	3]


(* ::Subsubsection:: *)
(*Amplitude structures (with derivatives)*)


AmplitudesStructure[d_]:= (*This function assign all the compatible derivative number of the operator to the previously generated helicity configurations*)
	Flatten[
		Map[
			Table[
				If[
					(EvenQ[der+#[[2,1]]])&& (*The first four conditions come from the representation theory and they check wheter is possible to form a Lorentz singlet*)
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


(* ::Subsubsection:: *)
(*Amplitudes structures (with scalars)*)


AmplitudesScalars[d_]:=
	Module[{structures=AmplitudesStructure[d],i},
		For[i=1,i<=Length[structures],i++,
			structures[[i,3]]=d-2*(structures[[i,1,1]]+structures[[i,1,2]])-3/2*(structures[[i,2,1]]+structures[[i,2,2]])-structures[[i,3]]
		];
		Return[structures];
	]


(* ::Subsection:: *)
(*Helicity and momentum structures*)


(* ::Subsubsection:: *)
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


(* ::Subsubsection:: *)
(*Partition of momenta*)


PartitionMomenta[moms_,partition_]:= (*Given a certain partition and a list of momenta of certain fields (e.g. helicity minus gluons), this function repeat and order the momenta according to the partition*)
	If[ListQ[partition], (*in the following function, this function will encounter some zeros, instead of a list associated to a partition. In this case it gives Nothing*)
		Flatten[
			Table[
				moms[[i]],
				{i,1,Length[partition]},
				{j,1,partition[[i]]} (*repeat the corresponding object as many times as it says the element of the partition*)
			] (*do it for all the elements of the partition*)
		],
		Return[Nothing]
	]


(* ::Subsubsection:: *)
(*Momenta Selection*)


MomentaSelection[d_][{{gluonsM_,gluonsP_},{fermM_,fermP_},ders_}]:= (*generates all the independent momenta, their corresponding partitions of partitions and assign all of them to the lists of momenta*)
	Module[{scals=d-2(gluonsM+gluonsP)-3/2*(fermM+fermP)-ders,moms,partitions,numberfields},
		numberfields=gluonsM+gluonsP+fermM+fermP+scals;
		moms=Table[i,{i,1,numberfields-1}];(*momentum conservation*)
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


(* ::Subsubsection:: *)
(*Spinor structures*)


SpinorStructure[d_][{{gluonsM_,gluonsP_},{fermM_,fermP_},ders_}]:= (*appends the list of momenta to both the angles and the squares bracket lists*)
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


(* ::Subsubsection:: *)
(*Counts to list*)


CountsToList[list_List]:= (*counts the number of times each distinct element appears and transform the association to a list of lists made of two objects, the label of each element and the counting*)
	KeyValueMap[
		List,
		Counts[list]
	]


(* ::Subsubsection:: *)
(*Is a singlet doable?*)


IsSingletDoable[{List1_,List2_}]:= (*the counting of one element can never exceed half of the total number of countings*)
	Module[{counts1=Counts[List1],counts2=Counts[List2],test1,test2},
		(*List1 and List2 are made of repeated elements, for example {1,1,1,2,2,3,3,6}*)

		test1=
			And@@
				Table[
					counts1[[i]]<=Length[List1]/2 ,
					{i,1,Length[counts1]}
				];

		test2=
			And@@
				Table[
					counts2[[i]]<=Length[List2]/2 ,
					{i,1,Length[counts2]}
				];

		If[
			test1&&test2,
			Return[
				{CountsToList[List1],CountsToList[List2]}
			],
			Return[Nothing];
		];
	]


End[]


(* ::Section:: *)
(*Form factors*)


Begin["`FormFactors`"]


(* ::Subsubsection:: *)
(*(Generic) Bracket*)


BracketBox[a_, b_] :=
    TemplateBox[{a, b}, "Bracket",
        DisplayFunction -> (RowBox[{"(",RowBox[{#1,"|",#2}],")"}]&),
        InterpretationFunction -> (RowBox[{"Bracket","[",RowBox[{#1,",",#2}],"]"}]&)]

Bracket /: MakeBoxes[Bracket[a_, b_], StandardForm | TraditionalForm] := BracketBox[ToBoxes[a], ToBoxes[b]]

Bracket[a_,b_]/;\[Not]OrderedQ[{a,b}]:=-Bracket[b,a]


(* ::Subsubsection:: *)
(*From Adjacency Matrix to Spinor Formula*)


FromMatrixToSpinors[adjacencymatrix_List,labels_List]:=
	Module[{numberpoints=Length[labels]},
		Product[
			Power[
				Bracket[labels[[i]],labels[[j]]],
				adjacencymatrix[[i,j]] (*gives a bracket to the power indicated by the number of lines between the two corresponding points*)
			],
			{i,1,numberpoints-1},
			{j,i+1,numberpoints}
		]
	]


(* ::Subsubsection:: *)
(*From structures to brackets*)


FromStructuresToSpinors[pointslines_List]:= (*given the number of labels of the points and the number of lines coming out from each point, this functions generates all the independent bracket structures*)
	Module[{labels,lines,numberpoints,graphs,structures},

		numberpoints=Length[pointslines];
		labels=Table[pointslines[[i,1]],{i,1,numberpoints}];
		lines=Table[pointslines[[i,2]],{i,1,numberpoints}];

		graphs=AllNonIntersectionGraphs[lines];

		structures=FromMatrixToSpinors[#,labels]&/@graphs;
		Return[structures];
	]


(* ::Subsubsection:: *)
(*From bracket to Spinor Helicity*)


AnglesAndSquares[{anglestructure_List,squarestructure_List}]:=
	Module[{formfactors,numberff,angles,squares},

		If[anglestructure=={},
			angles={1},
			angles=ReplaceAll[FromStructuresToSpinors[anglestructure],Bracket->SpinorAngleBracket]
		];
		If[squarestructure=={},
			squares={1},
			squares=ReplaceAll[FromStructuresToSpinors[squarestructure],Bracket->SpinorSquareBracket]
		];

		formfactors=
			Times@@@
				Tuples[
					{angles,squares} (*formfactors so far is a list of {angles,squares}, then Times@@{angles,squares} \[Rule] angles * squares. *)
				];

		Return[formfactors];

	]


End[]


(* ::Section:: *)
(*Attributes*)


SetAttributes[
    {PrimaryAmplitudeHelicityFields,
	PrimaryAmplitudeHelicity,
	AmplitudesStructure,
	AmplitudesScalars,
	HelicityStructure,
	IndependentMomenta,
	PartitionMomenta,
	AllPartitions,
	AllMomentaPartition,
	MomentaSelection,
	SpinorStructure,
	CountsToList,
	IsSingletDoable,
	BracketBox,
	Bracket,
	FromMatrixToSpinors,
	FromStructuresToSpinors,
	AnglesAndSquares
    },
    Protected
]


EndPackage[]
