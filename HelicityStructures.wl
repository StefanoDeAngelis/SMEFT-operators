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
IndependentMomenta::usage = "..."
PartitionMomenta::usage = "..."
AllPartitions::usage = "..."
AllMomentaPartition::usage = "..."
MomentaSelection::usage = "..."
SpinorStructure::usage = "..."
CountsToList::usage = "..."
IsSingletDoable::usage = "..."

BracketBox::usage = "..."
Bracket::usage = "..."
FromMatrixToSpinors::usage = "..."
FromStructuresToSpinors::usage = "..."
AnglesAndSquares::usage = "..."
MatterContentStructures::usage = "..."
AreSameFormFactor::usage = "..."
IndependentFormFactors::usage = "..."


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


(* ::Text:: *)
(*(*We want to avoid the repetition of certain operators under permutations of the labels of identical fields: taking the corresponding partition of the integer number of total number of derivatives for a certain number of field (gluonsM, gluonsP, fermM ecc.), we identify each independent operator with the partition of the number of derivates associated to a given particle species.*)*)


(* ::Subsubsection:: *)
(*Independent momenta*)


IndependentMomenta[gluonsM_,gluonsP_,fermM_,fermP_,scals_,ders_]:=
	Module[{moms},
		moms=
		Module[{fields={gluonsM,gluonsP,fermM,fermP,scals},totalfields},
			totalfields=Sum[fields[[n]],{n,1,Length[fields]}];
			Table[
				Table[
					If[(totalfields>3)&&(i==totalfields),Nothing,i],(*The last field can be excluded using MOMENTUM CONSERVATION, if it can be applied (n>3)*)
					{i,
						Sum[fields[[n]],{n,1,j-1}] (*the fields are labelled in order (all gluonsM) \[Rule] (all gluonsP) \[Rule] (all fermsM) \[Rule] (all fermP) \[Rule] (scals)*)
							+1,
						Sum[fields[[n]],{n,1,j-1}]
							+If[fields[[j]]<=ders,fields[[j]],ders] (*For a given species, we can restrict to a number of fields which is less than the total number of derivatives, taking into account the permutations of the labels*)
					}
				],
				{j,1,Length[fields]}
			]
		];
		moms=DeleteCases[moms,{}]; (*delete void lists, because in the following functions the species of the fields are not relevant and we can forget about those that are not contributing*)
		Return[moms];
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
(*All partitions*)


AllPartitions[moms_,ders_]:= (*gives all the permutation of partitions of partitions, given a certain NUMBER of field species contribution to the operator (up to momentum conservation) and number of total derivatives*)
	Module[{lengthmoms=Length[moms],partitions},
		partitions=
			Map[
				IntegerPartitions[#]&,
				IntegerPartitions[ders,lengthmoms],
				{2}
			] (*generates partitions of the partitions of the total number of momenta into the number of momenta of the fields*);
		partitions=
			Flatten[
				Map[
					Permutations,
					Map[
						PadRight[#,lengthmoms]&,
						Flatten[Tuples/@partitions,1]  (*combine the generated partitions of partitions in such a way that we have a list of list which sum of single elements = number of total derivatives.*)
					](*PadRight add zeros such that the number of level 1 elemets of the list is equal to the number of fields in the operator*)
				],
			1];
		Return[partitions];
	]


(* ::Subsubsection:: *)
(*Partition of momenta*)


AllMomentaPartition[moms_,partition_]:= (*given a partition of partition, this function assigns it to list of momenta grouped according to the field species*)
	Module[{table,lengthmoms=Length[moms]},
		If[
			Sum[
				Boole[Length[partition[[n]]]<=Length[moms[[n]]]],{n,1,lengthmoms}
			]==lengthmoms,(*check whether the lenght of the partition of partition is compatible to the length of lists of momenta. An example is shown in the first example below.*)
			table=
				Table[
					PartitionMomenta[moms[[i]],partition[[i]]],
					{i,1,lengthmoms}
				];
			Return[table], (*assign to each list of momenta its partition*)
			Return[Nothing];
		]
	]


(* ::Subsubsection:: *)
(*Momenta Selection*)


MomentaSelection[d_][{{gluonsM_,gluonsP_},{fermM_,fermP_},ders_}]:= (*generates all the independent momenta, their corresponding partitions of partitions and assign all of them to the lists of momenta*)
	Module[{scals=d-2(gluonsM+gluonsP)-3/2*(fermM+fermP)-ders,moms},
		moms=IndependentMomenta[gluonsM,gluonsP,fermM,fermP,scals,ders];
		moms=
			Sort[ (* sort the elements according to a canonical order *)
				Map[
					Flatten,
					AllMomentaPartition[moms,#]&/@AllPartitions[moms,ders]
				]
			];
		Return[moms];
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
	Module[{counts1=Counts[List1],lengthcounts1,counts2=Counts[List2],lengthcounts2,test1,test2},
	(*List1 and List2 are made of repeated elements, for example {1,1,1,2,2,3,3,6}*)
		lengthcounts1=Length[counts1];
		lengthcounts2=Length[counts2];

		test1=
			Sum[
				Boole[
					counts1[[i]]<=Length[List1]/2 
				],
				{i,1,lengthcounts1}
			]==lengthcounts1;

		test2=
			Sum[
				Boole[
					counts2[[i]]<=Length[List2]/2
				],
				{i,1,lengthcounts2}
			]==lengthcounts2;

		If[
			test1&&test2,
			Return[{CountsToList[List1],CountsToList[List2]}],
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
        DisplayFunction -> (RowBox[{"(",RowBox[{#1,",",#2}],")"}]&),
        InterpretationFunction -> (RowBox[{"Bracket","[",RowBox[{#1,",",#2}],"]"}]&)]

Bracket /: MakeBoxes[Bracket[a_, b_], StandardForm | TraditionalForm] := BracketBox[ToBoxes[a], ToBoxes[b]]


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


(* ::Subsubsection:: *)
(*Matter Content associated to each form factor*)


MatterContentStructures[formfactorStructures_List,dimO_]:=
	Module[{formfactor,helicities,numberparticles,dimFF,labels={{},{},{},{},{}},numberderivatives,i,numbergluons=0,numberfermions=0,numberscalars=0},
		formfactor=formfactorStructures[[1,1]]*formfactorStructures[[2,1]];
		helicities=HelicityWeight[formfactor];
		dimFF=MassDimension[formfactor];
		numberparticles=Length[helicities];
		For[i=1,i<=numberparticles,i++,
			If[
				helicities[[i,2]]==-2,
				(numbergluons++;
				labels[[1]]=Append[labels[[1]],helicities[[i,1]]]),
				If[
					helicities[[i,2]]==2,
					(numbergluons++;
					labels[[2]]=Append[labels[[2]],helicities[[i,1]]]),
					If[
						helicities[[i,2]]==-1,
						(numberfermions++;
						labels[[3]]=Append[labels[[3]],helicities[[i,1]]]),
						If[
							helicities[[i,2]]==1,
							(numberfermions++;
							labels[[4]]=Append[labels[[4]],helicities[[i,1]]]),
							If[
								helicities[[i,2]]==0,
								(numberscalars++;
								labels[[5]]=Append[labels[[5]],helicities[[i,1]]])
							]
						]
					]
				]
			]
		];
		For[i=numbergluons+numberfermions+numberscalars+1,i<=(dimO-dimFF),i++,
			labels[[5]]=Append[labels[[5]],i];
		];
		If[
			labels[[2]]=={},
			If[
				labels[[1]]=={},
				numbergluons=0,
				numbergluons=Last[labels[[1]]]
			],
			numbergluons=Last[labels[[2]]]
		];
		numberderivatives=(dimO-2*numbergluons-3/2*numberfermions-(dimO-dimFF-numbergluons-numberfermions));
		Return[{formfactorStructures,labels,numberderivatives}]
	]


(* ::Subsubsection:: *)
(*Are  the Same Form Factor?*)


AreSameFormFactor[{firstff_,secondff_},mattercontent_]:=
	Module[{localmatter=DeleteCases[mattercontent,{}],allrelabelling,duplicateQ},
		allrelabelling=Tuples[Permutations/@localmatter];
		duplicateQ=
			MemberQ[
				ReLabel[secondff,localmatter,#]&/@allrelabelling,
				firstff
			];
		Return[duplicateQ];
	]


(* ::Text:: *)
(*I want to write a function that can recognise that two different form factors are the same after relabelling, e.g. Spinoranglebracket[1,2]^2 Spinoranglebracket[3,4]^2,Spinoranglebracket[1,4]^2 Spinoranglebracket[2,3]^2.*)
(*The relabelling of the momenta has already been taken into account, then there is no need to check whether there could be a repetition for the operators by relabelling the scalars, because there enter in the form factors only through the momenta.*)


(* ::Subsubsection:: *)
(*Independent Form Factors*)


IndependentFormFactors[formfactors_List,mattercontent_]:=
	Module[{localff=formfactors,couples,length,stop=True},
		While[
			stop,
			If[
				Length[localff]==1,Return[localff]
			]; (*one single form factor cannot be repeated*)
			couples=Subsets[localff,{2}]; (*takes couples of form factors*)
			length=Length[couples];
			Do[
				If[
					AreSameFormFactor[couples[[i]],mattercontent], (*check if a couple is a repetition*)
					localff=DeleteCases[localff,couples[[i,2]]]; (*if yes, delete the second f.f. of the couple*)
					Break[], (*and generate new couples*)
					If[i==length,stop=False] (*if it checked all the couples, we have a list of *)
				],
				{i,1,length}
			]
		];
		Return[localff];
	]


(* ::Text:: *)
(*An alternative function could generate all the permutations of the first formfactor and check whether there are repetitions in the others and delete them. Then it generates the permutations of the second (remaining) f.f. and so on. This could be faster because the permutations for one type of operators is generated only once.*)


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
	AnglesAndSquares,
	MatterContentStructures,
	AreSameFormFactor,
	IndependentFormFactors
    },
    Protected
]


EndPackage[]
