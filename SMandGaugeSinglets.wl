(* ::Package:: *)

(* ::Chapter:: *)
(*SM Fields and Gauge Singlets*)


BeginPackage["SMandGaugeSinglets`",{"SpinorHelicity6D`","HelicityStructures`","SUInvariants`","YoungSymm`"}]


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

SU3singlet::usage = "..."
SU2singlet::usage = "..."
GaugeSinglets::usage = "..."

FinalAmplitude::usage = "..."
IdentitiesBetweenAmplitudes::usage = "..."

AllOperators::usage = "..."


(* ::Section:: *)
(*Private*)


Begin["`Private`"]


(* ::Subsection:: *)
(*Transformation rules*)


TransformationRules={GGp->{adj,sing,0},WWp->{sing,adj,0},BBp->{sing,sing,0},GGm->{adj,sing,0},WWm->{sing,adj,0},BBm->{sing,sing,0},QQ->{fund,fund,1/6},uu->{afund,sing,-(2/3)},dd->{afund,sing,1/3},LL->{sing,fund,-(1/2)},ee->{sing,sing,1},QBar->{afund,fund,-(1/6)},uBar->{fund,sing,2/3},dBar->{fund,sing,-(1/3)},LBar->{sing,fund,1/2},eBar->{sing,sing,-1},HH->{sing,fund,1/2},HBar->{sing,fund,-(1/2)}}


(* ::Subsection:: *)
(*Fields order*)


OrderingRule={BBm,GGm,WWm,BBp,GGp,WWp,QBar,uBar,dBar,LBar,eBar,QQ,uu,dd,LL,ee,HBar,HH}


(* ::Subsection::Closed:: *)
(*Fields and their helicity configuration*)


GluonsP={BBp,GGp,WWp}
GluonsM={BBm,GGm,WWm}
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
			((fundSU3==0&&afundSU3==0&&adjointSU3!=1)||(Mod[fundSU3-afundSU3,3]==0&&(fundSU3!=0||afundSU3!=0)))&&((fundSU2==0&&adjointSU2!=1)||(fundSU2!=0&&EvenQ[fundSU2]))&&
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


(* ::Subsection::Closed:: *)
(*SU(3) singlet*)


SU3singlet[replist_List]:=
	Module[{reps={}},
		Do[
			If[
				replist[[i]]==adj,
				AppendTo[reps,{i,0}]
			];
			If[
				replist[[i]]==fund,
				AppendTo[reps,{i,1}]
			];
			If[
				replist[[i]]==afund,
				AppendTo[reps,{i,-1}]
			],
			{i,1,Length[replist]}
		];
		Return[reps];
	]


(* ::Subsection::Closed:: *)
(*SU(2) singlet*)


SU2singlet[replist_List]:=
	Module[{reps={}},
		Do[
			If[
				replist[[i]]==adj,
				AppendTo[reps,{i,2}]
			];
			If[
				replist[[i]]==fund,
				AppendTo[reps,{i,1}]
			],
			{i,1,Length[replist]}
		];
		Return[reps];
		]


(* ::Subsection:: *)
(*Gauge Singlets*)


Options[GaugeSinglets]={"RenormalisableTree"->False}

GaugeSinglets[fields_List,OptionsPattern[]]:=
	Module[{singlets,adjointSU3(*,adjointSU2*)},
		singlets=
			Transpose[
				ReplaceAll[fields,TransformationRules]
			];
		If[
			OptionValue["RenormalisableTree"]==True,
			If[
				(MemberQ[fields,BBm]||MemberQ[fields,BBp])&&\[Not]MemberQ[singlets[[3]],_?(#!=0&)],
				Return[Null]
			]
		];
		singlets=Drop[singlets,-1];
		adjointSU3=Flatten[Position[singlets[[1]],adj]];
		singlets[[1]]=
			SimplifyInvariants[
				ContractSU3[#,Length[fields]+1]&/@
					(Product[TauSU3[ALabel[i],bLabel[i],aLabel[i]],{i,adjointSU3}]
						AllInvariantDeltas[
							SU3singlet[singlets[[1]]]
						])
			];
		(*adjointSU2=Flatten[Position[singlets[[2]],adj]];*)
		singlets[[2]]=InvariantsSU2[SU2singlet[singlets[[2]]],"Dummies"->Length[fields]];
			(*SimplifyInvariants[
				ContractSU2[#,Length[fields]+1]&/@
					(Product[TauSU2[ILabel[i]][xLabel[i,120],xLabel[i,121]],{i,adjointSU2}]
						FromStructuresToEpsilonSU2[
							SU2singlet[singlets[[2]]]
						])
			];*)
		singlets=Map[(Times@@#)&,Tuples[singlets],{1}];
		Return[singlets];
	]


(* ::Subsection:: *)
(*Final Amplitude*)


Options[FinalAmplitude]={"RenormalisableTree"->False}

FinalAmplitude[{fields_List,helicity_},OptionsPattern[]]:=
	Module[{colourfactors=GaugeSinglets[fields,"RenormalisableTree"->OptionValue["RenormalisableTree"]],amplitudes},
		If[colourfactors==Null,Return[Nothing]];
		amplitudes=Thread[Times[colourfactors,helicity]];
		If[\[Not]DuplicateFreeQ[fields],
			Module[{bosons={{}},fermions={{}},localfields=DeleteDuplicates[fields],localamplitudes=amplitudes,number,positions},
				number=Length[localfields];
				Do[
					positions=Flatten[Position[fields,localfields[[i]]]];
					If[
						Length[positions]>1,
						If[MemberQ[Join[GluonsM,GluonsP,Scalars],localfields[[i]]],AppendTo[bosons,positions]];
						If[MemberQ[Join[FermionsM,FermionsP],localfields[[i]]],AppendTo[fermions,positions]]
					],
					{i,1,number}
				];
				localamplitudes=MultipleSymmetrise[#,Sequence@@bosons]&/@localamplitudes;
				localamplitudes=MultipleSymmetrise[#,Sequence@@fermions,"AntiSymmetric"->True]&/@localamplitudes;
				amplitudes=DeleteCases[localamplitudes,_?PossibleZeroQ];
			];
		];
		amplitudes=Table[{fields,amplitudes[[i]]},{i,1,Length[amplitudes]}];
		Return[amplitudes]
	]


(* ::Subsubsection:: *)
(*Identities Between Amplitudes*)


(* ::Text:: *)
(*The SU(3) are not implemented yet! TODO!!!*)
(*This function has also to take into account the additional momentum conservation identities! TODO!!!*)


IdentitiesBetweenAmplitudes[{{fields_},operators_}]:=
	Module[{singlets,num=Length[fields],localoperators,count,independent={operators[[1]]}},
		If[Length[operators]==1||DuplicateFreeQ[fields],Return[{{fields},operators}]];
		localoperators=Expand[operators/.{SpinorAngleBracket[i_,l_]SpinorSquareBracket[j_,k_]/;(l==k==num):>-Sum[SpinorAngleBracket[i,p]SpinorSquareBracket[j,p],{p,1,num-1}]}];(*powers???*)
		count=AngleSquareCount[#,num]&/@localoperators;
		count=AngleSquareSchouten[DeleteDuplicates[count]];
		localoperators=localoperators/.count//Expand;
		singlets=
			Drop[
				Transpose[
					ReplaceAll[fields,TransformationRules]
				],
				-1
			];
		singlets={(*AllIdentitiesSU3[SU3singlet[singlets[[1]]]],*)SubstitutionsSU2[SU2singlet[singlets[[2]]],"Dummies"->num]};
		singlets=Flatten[(*Drop[*)singlets(*,1]*)];
		localoperators=localoperators/.singlets//Expand;
		Do[
			If[
				\[Not]MatchQ[
					Simplify[localoperators[[i]],Table[localoperators[[j]]==0,{j,1,i-1}]],
					0
				],
				AppendTo[independent,operators[[i]]];
			],
			{i,2,Length[localoperators]}
		];
		Return[{{fields},independent}];
	]


(* ::Subsubsection::Closed:: *)
(*All Operators*)


AllOperators[d_]:=
	Module[{matter,helicityfactor,ops},
		{matter,helicityfactor}=Transpose[(*IndependentHelicityFactors[d]*)TestMomentumConservation[d]];
		matter=CombinationsOfFields/@matter;
		ops=
			Flatten[
				Thread/@
					(If[MatchQ[#[[1]],{}],Nothing,#]&/@Transpose[List[matter,helicityfactor]]),
				1
			];
		ops=Flatten[FinalAmplitude/@ops,1];
		ops=Map[DeleteDuplicates,Transpose/@GatherBy[ops,First],{2}];
		ops=
			Flatten[
				Tuples/@(IdentitiesBetweenAmplitudes/@ops),
				1
			];
		Return[ops];
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
	CombinationsOfFields,
	SU3singlet,
	SU2singlet,
	GaugeSinglets,
	FinalAmplitude,
	IdentitiesBetweenAmplitudes,
	AllOperators
	},
    Protected
]

EndPackage[]
