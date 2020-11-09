(* ::Package:: *)

(* ::Chapter:: *)
(*SM Fields and Gauge Singlets*)


BeginPackage["SMandGaugeSinglets`"]


(* ::Section:: *)
(*Messages*)


TransformationRules::usage = "..."
GGp::usage = "..."
WWp::usage = "..."
BBp::usage = "..."
GGm::usage = "..."
WWm::usage = "..."
BBm::usage = "..."
QQ::usage = "..."
uu::usage = "..."
dd::usage = "..."
LL::usage = "..."
ee::usage = "..."
QBar::usage = "..."
uBar::usage = "..."
dBar::usage = "..."
LBar::usage = "..."
eBar::usage = "..."
HH::usage = "..."
HBar::usage = "..."

adj::usage = "..."
sing::usage = "..."
fund::usage = "..."
afund::usage = "..."

GluonsM::usage = "..."
GluonsP::usage = "..."
FermionsM::usage = "..."
FermionsP::usage = "..."
Scalars::usage = "..."
Fields::usage = "..."

ColourSingletDoable::usage = "..."
CombinationsOfFields::usage = "..."
LabelsToNumbers::usage = "..."
SMEFTOperatorDoable::usage = "..."


(* ::Section:: *)
(*Private*)


Begin["`Private`"]


(* ::Subsection:: *)
(*Transformation rules*)


TransformationRules={GGp->{adj,sing,0},WWp->{sing,adj,0},BBp->{sing,sing,0},GGm->{adj,sing,0},WWm->{sing,adj,0},BBm->{sing,sing,0},QQ->{fund,fund,1/6},uu->{afund,sing,-(2/3)},dd->{afund,sing,1/3},LL->{sing,fund,-(1/2)},ee->{sing,sing,1},QBar->{afund,fund,-(1/6)},uBar->{fund,sing,2/3},dBar->{fund,sing,-(1/3)},LBar->{sing,fund,1/2},eBar->{sing,sing,-1},HH->{sing,fund,1/2},HBar->{sing,fund,-(1/2)}}


(* ::Subsection:: *)
(*Fields and their helicity configuration*)


GluonsP={GGp,WWp,BBp}
GluonsM={GGm,WWm,BBm}
FermionsP={QQ,uu,dd,LL,ee}
FermionsM={QBar,uBar,dBar,LBar,eBar}
Scalars={HH,HBar}
Fields={GluonsP,GluonsM,FermionsP,FermionsM,Scalars};


(* ::Subsection:: *)
(*Is a gauge singlet doable?*)


ColourSingletDoable[fields_List]:=
	Module[{tensorstructure,adjointSU3,fundSU3,afundSU3,adjointSU2,fundSU2,charge},
		tensorstructure=Transpose[
			ReplaceAll[
				fields,
				TransformationRules
			]
		];
		adjointSU3=Count[tensorstructure[[1]],adj];
		fundSU3=Count[tensorstructure[[1]],fund];
		afundSU3=Count[tensorstructure[[1]],afund];
		adjointSU2=Count[tensorstructure[[2]],adj];
		fundSU2=Count[tensorstructure[[2]],fund];
		charge=Total[tensorstructure[[3]]];
		If[
			((fundSU3==0&&afundSU3==0&&adjointSU3!=1)||(fundSU3!=0&&fundSU3==afundSU3))&&((fundSU2==0&&adjointSU2!=1)||(fundSU2!=0&&EvenQ[fundSU2]))&&
			charge==0,
			Return[fields],
			Return[Nothing];
		]
	]


(* ::Subsection:: *)
(*Combinations of fields*)


CombinationsOfFields[listNumbers_List]:=
	Module[{types=Length[listNumbers],groupingFields},
		If[
			types==5,
			groupingFields=
				Table[
					Sort[ (*this order sort\[Rule]deleteduplicates\[Rule]sort is slightly faster than sort\[Rule]sort\[Rule]deleteduplicates*)
						DeleteDuplicates[
							Sort/@ (*sort to recognise duplicates*)
								Tuples[Fields[[i]],listNumbers[[i]]]
						]
					],
					{i,1,5}
				];
			groupingFields=
				ColourSingletDoable/@
					Map[
						Flatten[#,1]&,
						Tuples[groupingFields] (*combines the different choices for each type of field*)
					];
			Return[groupingFields];
		]
	]


(* ::Subsection:: *)
(*Labels to numbers*)


LabelsToNumbers[listLabels_List]:=
	Module[{listNumbers},
		listNumbers=Length/@listLabels;
		Return[listNumbers];
	]


(* ::Subsection:: *)
(*Is the a SMEFT operator doable?*)


SMEFTOperatorDoable[{helicityStructures_,listLabels_List,numberDerivatives_Integer}]:=
	Module[{listNumbers=LabelsToNumbers[listLabels],combinations,numberCombinations,operators},
		combinations=CombinationsOfFields[listNumbers];
		numberCombinations=Length[combinations];
		operators=
			Table[
				{helicityStructures,listLabels,numberDerivatives,combinations[[i]]},
				{i,1,numberCombinations}
			]
	]


End[]


(* ::Section:: *)
(*Attributes*)


SetAttributes[
    {
	TransformationRules,
	GGp,
	WWp,
	BBp,
	GGm,
	WWm,
	BBm,
	QQ,
	uu,
	dd,
	LL,
	ee,
	QBar,
	uBar,
	dBar,
	LBar,
	eBar,
	HH,
	HBar,
	adj,
	sing,
	fund,
	afund,
	GluonsM,
	GluonsP,
	FermionsM,
	FermionsP,
	Scalars,
	Fields,
	ColourSingletDoable,
	CombinationsOfFields,
	LabelsToNumbers,
	SMEFTOperatorDoable
	},
    Protected
]

EndPackage[]
