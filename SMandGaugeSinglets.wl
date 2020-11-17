(* ::Package:: *)

(* ::Chapter:: *)
(*SM Fields and Gauge Singlets*)


BeginPackage["SMandGaugeSinglets`",{"SUInvariants`"}]


(* ::Section:: *)
(*Messages*)


TransformationRules::usage = "Associate to each particle of the Standard Model its transformation property under the gauge group."
OrderingRule::usage = "The order chosen for the SM fields"
GGp::usage = "The gluons with plus helicity"
WWp::usage = "The W bosons with plus helicity"
BBp::usage = "The B boson with plus helicity"
GGm::usage = "The gluons with minus helicity"
WWm::usage = "The W bosons with minus helicity"
BBm::usage = "The B boson with minus helicity"
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

adj::usage = "The adjoint representation of both the SU(2) and SU(3) gauge groups"
sing::usage = "The singlet representation for both the SU(2) and SU(3) gauge groups"
fund::usage = "The fundamental representation for the SU(3) gauge group"
afund::usage = "The antifundamental representation for the SU(3) gauge group"

GluonsM::usage = "All the vectors with plus helicity"
GluonsP::usage = "All the vectors with minus helicity"
FermionsM::usage = "All the fermions with plus helicity"
FermionsP::usage = "All the fermions with minus helicity"
Scalars::usage = "All the scalars"
Fields::usage = "All the fields of the Standard Model"

ColourSingletDoable::usage = "Given a list of particles of the Standard Model, the function gives the list back if it possible to form a colour singlet."
CombinationsOfFields::usage = "..."


(* ::Section:: *)
(*Private*)


Begin["`Private`"]


(* ::Subsection:: *)
(*Transformation rules*)


TransformationRules={GGp->{adj,sing,0},WWp->{sing,adj,0},BBp->{sing,sing,0},GGm->{adj,sing,0},WWm->{sing,adj,0},BBm->{sing,sing,0},QQ->{fund,fund,1/6},uu->{afund,sing,-(2/3)},dd->{afund,sing,1/3},LL->{sing,fund,-(1/2)},ee->{sing,sing,1},QBar->{afund,fund,-(1/6)},uBar->{fund,sing,2/3},dBar->{fund,sing,-(1/3)},LBar->{sing,fund,1/2},eBar->{sing,sing,-1},HH->{sing,fund,1/2},HBar->{sing,fund,-(1/2)}}


(* ::Subsection:: *)
(*Fields order*)


OrderingRule={GGp,GGm,WWp,WWm,BBp,BBm,QQ,uu,dd,LL,ee,QBar,uBar,dBar,LBar,eBar,HH,HBar}


(* ::Subsection:: *)
(*Fields and their helicity configuration*)


GluonsP={GGp,WWp,BBp}
GluonsM={GGm,WWm,BBm}
FermionsP={QQ,uu,dd,LL,ee}
FermionsM={QBar,uBar,dBar,LBar,eBar}
Scalars={HH,HBar}
Fields={GluonsM,GluonsP,FermionsM,FermionsP,Scalars};


(* ::Subsection:: *)
(*Is a gauge singlet doable?*)


ColourSingletDoable[fields_List]:=
	Module[{tensorstructure,adjointSU3,fundSU3,afundSU3,adjointSU2,fundSU2,charge,chargedQ},
		tensorstructure=Transpose[
			ReplaceAll[
				fields,
				TransformationRules
			]
		]; (*we substitute the transformation rules to each field and by doing the Transpose we group the representations according to the subgroups *)
		adjointSU3=Count[tensorstructure[[1]],adj];
		fundSU3=Count[tensorstructure[[1]],fund];
		afundSU3=Count[tensorstructure[[1]],afund];
		adjointSU2=Count[tensorstructure[[2]],adj];
		fundSU2=Count[tensorstructure[[2]],fund];
		charge=Total[tensorstructure[[3]]];
		If[
			((fundSU3==0&&afundSU3==0&&adjointSU3!=1)||(fundSU3!=0&&fundSU3==afundSU3))&&((fundSU2==0&&adjointSU2!=1)||(fundSU2!=0&&EvenQ[fundSU2]))&&
			charge==0, (*singlet conditions*)
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
					(*Sort[*) (*this order sort\[Rule]deleteduplicates\[Rule]sort is slightly faster than sort\[Rule]sort\[Rule]deleteduplicates*)
						DeleteDuplicates[
							Sort(*By[#,Position[OrderingRule,#]&]&*)/@ (*sort to recognise duplicates*)
								Tuples[Fields[[i]],listNumbers[[i]]] (*given the species, we take listNumber[[i]] of them maybe this can be fastened using IntegerPartions[listNumber[[i]]], PadRight[#,Length[Fields[[i]]]] and Permutations)*)
						]
					(*]*),
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


End[]


(* ::Section:: *)
(*Attributes*)


SetAttributes[
    {
	TransformationRules,
	OrderingRule,
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
	CombinationsOfFields
	},
    Protected
]

EndPackage[]
