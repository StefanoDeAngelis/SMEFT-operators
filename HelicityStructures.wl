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
IsSingletDoable::usage = "..."

BracketBox::usage = "..."
Bracket::usage = "..."
FromMatrixToSpinors::usage = "..."
FromStructuresToSpinors::usage = "..."
AnglesAndSquares::usage = "..."
MatterContent::usage = "..."
IndependentHelicityFactors::usage = "..."

SchoutenIdentities::usage = "..."
AngleCount::usage = "..."
SquareCount::usage = "..."
AngleSquareCount::usage = "..."
AngleSquareSchouten::usage = "..."

MomentumConservationIdentities::usage = "..."
IdentitiesBetweenKinematics::usage = "..."
TestMomentumConservation::usage = "..."


(* ::Section:: *)
(*Classification*)


Begin["`Classification`"]


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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
(*Momenta Selection*)


MomentaSelection[d_][{{gluonsM_,gluonsP_},{fermM_,fermP_},ders_}]:= (*generates all the independent momenta, their corresponding partitions of partitions and assign all of them to the lists of momenta*)
	Module[{scals=d-2(gluonsM+gluonsP)-3/2*(fermM+fermP)-ders,moms,partitions,numberfields},
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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
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
				{Tally[List1],Tally[List2]}
			],
			Return[Nothing];
		];
	]


End[]


(* ::Section:: *)
(*Form factors*)


Begin["`FormFactors`"]


(* ::Subsubsection::Closed:: *)
(*(Generic) Bracket*)


BracketBox[a_, b_] :=
    TemplateBox[{a, b}, "Bracket",
        DisplayFunction -> (RowBox[{"(",RowBox[{#1,"|",#2}],")"}]&),
        InterpretationFunction -> (RowBox[{"Bracket","[",RowBox[{#1,",",#2}],"]"}]&)]

Bracket /: MakeBoxes[Bracket[a_, b_], StandardForm | TraditionalForm] := BracketBox[ToBoxes[a], ToBoxes[b]]

Bracket[a_,b_]/;\[Not]OrderedQ[{a,b}]:=-Bracket[b,a]


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
(*Matter Content*)


MatterContent[d_,helicityfactor_]:=
	Module[{matter,hel={-2,2,-1,1},scalars},
		matter=HelicityWeight[helicityfactor];
		matter=Table[Count[matter,_?(MatchQ[#[[2]],hel[[i]]]&)],{i,4}];
		scalars=d-MassDimension[helicityfactor]-Total[matter];
		matter=Append[matter,scalars];
		Return[{matter,helicityfactor}]
	]


(* ::Subsubsection::Closed:: *)
(*Independent Helicity Factors*)


Options[IndependentHelicityFactors]={"MatterContent"->True}

IndependentHelicityFactors[d_,OptionsPattern[]]:=
	Module[{structures},
		structures=Flatten[SpinorStructure[d][#]&/@AmplitudesStructure[d],1];

		structures=IsSingletDoable[#]&/@structures;

		structures=Flatten[AnglesAndSquares[#]&/@structures];

		If[
			OptionValue["MatterContent"],
			structures=MatterContent[d,#]&/@structures;
		];

		Return[structures]
	]


(* ::Subsubsection::Closed:: *)
(*Schouten Identities*)


Options[SchoutenIdentities]={"Substitutions"->True};

SchoutenIdentities[pointslines_List,OptionsPattern[]]:=
	Module[{lines,labels,numberpoints=Length[pointslines],intersecting,numberinter,nonintersecting,numbernoninter,replacements,graphlabels,x,y},
	
		If[pointslines=={},Return[{}]];

		lines=Table[pointslines[[i,2]],{i,1,numberpoints}];
		labels=Table[pointslines[[i,1]],{i,1,numberpoints}];

		numberfundlabels=Count[lines,1];

		intersecting=Map[PadLeft[#,numberpoints]&,Append[#,{}]&/@AllGraphs[lines],{2}]; (*generate all graphs*)

		nonintersecting=IsGraphNonIntesercting/@intersecting; (*generate non-intersecting graphs*)
		numbernoninter=Length[nonintersecting];

		intersecting=Complement[intersecting,nonintersecting]; (*complement to take select the intersecting graphs*)
		numberinter=Length[intersecting];

		graphlabels=
			Join[
				Table[
					intersecting[[i]]->x[i], (*assign labels to intersecting and intersecting graphs*)
					{i,1,numberinter}
				],
				Table[
					nonintersecting[[i]]->y[i], (*assign labels to intersecting and non-intersecting graphs*)
					{i,1,numbernoninter}
				]
			];
		
		(*generators=Product[TauSU2[ILabel[labels[[i]]]][xLabel[labels[[i]],1],xLabel[labels[[i]],2]],{i,numberfundlabels+1,numberpoints}];*) (*senza motivo!*)

		nonintersecting=
			Table[
				y[i]->FromMatrixToSpinors[nonintersecting[[i]],labels],
				{i,1,numbernoninter}
			];

		replacements=
			Table[
				x[i]->Total[SchoutenCrossing[intersecting[[i]]]/.graphlabels],
				{i,1,Length[intersecting]}
			];
			
		replacements=
			Table[
				If[
					OptionValue["Substitutions"],
					FromMatrixToSpinors[intersecting[[i]],labels] -> Expand[x[i]//.replacements]/.nonintersecting,
					FromMatrixToSpinors[intersecting[[i]],labels] - (Expand[x[i]//.replacements]/.nonintersecting)==0 (*some of these are present multiple times, DeleteDuplicates is need or something else. This happens when the angle structures are the same but the squares are different*)
				],
				{i,1,numberinter}
			]; (*placing the repeated replacements inside the list speeds the function up*)

		Return[replacements];

]


(* ::Subsubsection::Closed:: *)
(*Counting angles and squares*)


AngleCount[exp_,label_]:=
	Join[
		Cases[
			{exp},
			HoldPattern[SpinorAngleBracket[label,_]|SpinorAngleBracket[_,label]]:>1,
			\[Infinity]
		](*,
		Cases[
			{exp},
			HoldPattern[S[label,_]|S[_,label]]\[RuleDelayed]1,
			\[Infinity]
		]*)
	]//Length;
	
SquareCount[exp_,label_]:=
	Join[
		Cases[
			{exp},
			HoldPattern[SpinorSquareBracket[label,_]|SpinorSquareBracket[_,label]]:>1,
			\[Infinity]
		](*,
		Cases[
			{exp},
			HoldPattern[S[label,_]|S[_,label]]\[RuleDelayed]1,
			\[Infinity]
		]*)
	]//Length;
	
AngleSquareCount[exp_Plus,length_Integer]:=Sequence@@DeleteDuplicates[AngleSquareCount[#,length]&/@(List@@exp)];

AngleSquareCount[exp_,length_Integer]:=
	Module[{angles,squares},
		angles=
			DeleteCases[
				Table[{i,AngleCount[exp,i]},{i,length}],
				_?(#[[2]]==0&)
			];
		squares=
			DeleteCases[
				Table[{i,SquareCount[exp,i]},{i,length}],
				_?(#[[2]]==0&)
			];
		Return[List[angles,squares]];
	]


(* ::Subsubsection::Closed:: *)
(*Schouten for angles and squares*)


Options[AngleSquareSchouten]={"Substitutions"->True}

AngleSquareSchouten[count_List,OptionsPattern[]]:=
	Module[{schouten},
		schouten=Flatten/@Transpose[Map[SchoutenIdentities[#,"Substitutions"->OptionValue["Substitutions"]]&,count,{2}]];
		schouten[[1]]=schouten[[1]]/.{Bracket->SpinorAngleBracket};
		schouten[[2]]=schouten[[2]]/.{Bracket->SpinorSquareBracket};
		schouten=Flatten[schouten];
		Return[schouten];
	]


(* ::Subsubsection::Closed:: *)
(*Is Momentum Conservation implemented correctly?*)


MomentumConservationIdentities[length_Integer,sign_]:=
	If[
		sign>0,
		Table[Sum[SpinorAngleBracket[i,k]SpinorSquareBracket[k,length],{k,1,length-1}]==0,{i,1,length-1}],
		If[
			sign<0,
			Table[Sum[SpinorAngleBracket[length,k]SpinorSquareBracket[k,i],{k,1,length-1}]==0,{i,1,length-1}],
			{}
		]
	]

(*IdentitiesBetweenKinematics[{{fields_},operators_}]:=
	Module[{num=Total[fields],lasthelicity,helicities={-2,2,-1,1,0},weights={2,2,3/2,3/2,1},schouten,momcons={},dependent={},ders},
		ders=MassDimension[operators[[1]]]+num-Sum[fields[[i]]*weights[[i]],{i,1,5}];
		If[Length[operators]\[Equal]1||ders\[Equal]0,Return[{{fields},dependent}]];
		Do[If[fields[[5-j]]\[NotEqual]0,lasthelicity=5-j;Break[]],{j,0,4}];
		lasthelicity=helicities[[lasthelicity]];
		schouten=AngleSquareCount[#,num]&/@operators;
		schouten=AngleSquareSchouten[DeleteDuplicates[schouten],"Substitutions"\[Rule]False];
		momcons=MomentumConservationIdentities[num,lasthelicity];
		If[ders>2,momcons=Join[momcons,{Sum[\[LeftAngleBracket]j\[MediumSpace]i\[RightAngleBracket][i\[MediumSpace]j],{i,1,num-1},{j,i+1,num-1}]\[Equal]0}]];
		Do[
			If[
				MatchQ[
					Simplify[operators[[i]],Join[Table[operators[[j]]\[Equal]0,{j,1,i-1}],schouten,momcons]],
					0
				],
				AppendTo[dependent,operators[[i]]];
			],
			{i,1,Length[operators]}
		];
		Return[{{fields},dependent}];
	]*)
	
IdentitiesBetweenKinematics[{{fields_},operators_}]:=
	Module[{num=Total[fields],lasthelicity,helicities={-2,2,-1,1,0},weights={2,2,3/2,3/2,1},schouten,momcons={},independent={operators[[1]]},ders},
		ders=MassDimension[operators[[1]]]+num-Sum[fields[[i]]*weights[[i]],{i,1,5}];
		If[Length[operators]==1||ders==0,Return[{{fields},operators}]];
		Do[If[fields[[5-j]]!=0,lasthelicity=5-j;Break[]],{j,0,4}];
		lasthelicity=helicities[[lasthelicity]];
		schouten=AngleSquareCount[#,num]&/@operators;
		schouten=AngleSquareSchouten[DeleteDuplicates[schouten],"Substitutions"->False];
		momcons=MomentumConservationIdentities[num,lasthelicity];
		If[ders>=2,momcons=Join[momcons,{Sum[SpinorAngleBracket[j,i]SpinorSquareBracket[i,j],{i,1,num-1},{j,i+1,num-1}]==0}]];
		Do[
			If[
				\[Not]MatchQ[
					Simplify[operators[[i]],Join[Table[operators[[j]]==0,{j,1,i-1}],schouten,momcons]],
					0
				],
				AppendTo[independent,operators[[i]]];
			],
			{i,2,Length[operators]}
		];
		Return[{{fields},independent}];
	]
	
TestMomentumConservation[d_]:=
	Module[{ff=IndependentHelicityFactors[d]},
		ff=Map[DeleteDuplicates,Transpose/@GatherBy[ff,First],{2}];
		ff=IdentitiesBetweenKinematics/@ff;
		(*ff=If[#[[2]]=={},Nothing,#]&/@ff;*)
		ff=Flatten[Tuples/@ff,1];
		Return[ff]
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
	IsSingletDoable,
	BracketBox,
	Bracket,
	FromMatrixToSpinors,
	FromStructuresToSpinors,
	AnglesAndSquares,
	MatterContent,
	IndependentHelicityFactors,
	SchoutenIdentities,
	AngleCount,
	SquareCount,
	AngleSquareCount,
	AngleSquareSchouten,
	MomentumConservationIdentities,
	IdentitiesBetweenKinematics,
	TestMomentumConservation
    },
    Protected
]


EndPackage[]
