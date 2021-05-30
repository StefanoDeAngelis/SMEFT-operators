(* ::Package:: *)

(* ::Chapter:: *)
(*YoungSymm*)


BeginPackage["YoungSymm`"]


(* ::Section:: *)
(*Messages*)


ReLabel::usage = "..."
Symmetrise::usage = "..."
MultipleSymmetrise::usage = "..."
YoungSymmetrise::usage = "..."
MultipleYoungSymmetrise::usage = "..."


(* ::Section:: *)
(*Functions*)


Begin["`Private`"]


(* ::Subsection::Closed:: *)
(*ReLabel*)


(*ReLabel[exp_,toberelabelled_,newlabels_]:=
	ReplaceAll[
		exp,
		Join[
			{s_Power:>s,s_Rational:>s},
			Thread[Flatten[toberelabelled]->Flatten[newlabels]]
		]
	]*)
	
ReLabel[x_List,tobe_List,new_List]:=ReLabel[#,tobe,new]&/@x
ReLabel[x_Plus,tobe_List,new_List]:=Plus@@(ReLabel[#,tobe,new]&/@(List@@x))
ReLabel[x_Times,tobe_List,new_List]:=Times@@(ReLabel[#,tobe,new]&/@(List@@x))

ReLabel[exp_Power,tobe_List,new_List]:=MapAt[ReLabel[#,tobe,new]&,exp,1]
ReLabel[exp_,tobe_List,new_List]/;NumberQ[exp]:=exp

ReLabel[exp_,toberelabelled_List,newlabels_List]:=
	Block[{Simp},
		
		
		Set@@@Thread[{Simp/@toberelabelled,newlabels}];
		Simp[f_[x___][y___]]:=f[Sequence@@(Simp/@{x})][Sequence@@(Simp/@{y})];
		Simp[f_[x___]]:=f[Sequence@@(Simp/@{x})];
		Simp[x_]:=x;
		
		Simp@exp
	]

(*ReLabel[exp_,toberelabelled_,newlabels_]:=
	Module[{localexp=exp,power=1},
	
		If[NumberQ[localexp],Return[localexp]];
		
		If[MatchQ[localexp,Power[_,_]],power=localexp[[2]];localexp=localexp[[1]]];
		
		localexp=ReplaceAll[localexp,Thread[Flatten[toberelabelled]->Flatten[newlabels]]];
		
		Return[Power[localexp,power]];
	]*)


(* ::Subsection::Closed:: *)
(*Symmetrise*)


Options[Symmetrise]={"AntiSymmetric"->False(*,"NumericalCoefficients"\[Rule]True*)}; (*The NumericalCoefficients options is necessary when the label to permute are numbers. Wrong replacement could appear while working with numbers. At the present stage of the function ReLabel this should not be the case anymore, so the option NumericalCoefficients is commented.*)

Symmetrise[exp_,tobesymmetrised_?(Length[#]==1&),OptionsPattern[]]:=exp

Symmetrise[exp_,tobesymmetrised_List,OptionsPattern[]]:=
	Module[{length=(Length[tobesymmetrised])!,permutations,signs,symmetrisation(*,coefficient*)},

		permutations=Permutations[tobesymmetrised];

		signs=
			If[
				OptionValue["AntiSymmetric"],
				Signature[tobesymmetrised]*Signature/@permutations,
				Table[1,{i,1,length}]
			];

		symmetrisation=Sum[signs[[i]]*ReLabel[exp,tobesymmetrised,permutations[[i]]],{i,1,length}];

		(*If[
			OptionValue["NumericalCoefficients"],
			coefficient=length,
			coefficient=Abs[Take[Factor[symmetrisation],1]]; (*All the terms have the same coefficients as far as they are all distinguishable, which is always the case assumed by the present function. Counterexample: |1,1,2> instead of |1,2,3> (all the labels are different)*)
			If[
				!(NumericQ[coefficient]), (*it can happen that there is no overall coefficient, then Take[Factor[],1] is not a number*)
				coefficient=1
			]
		];*)

		symmetrisation=Expand[symmetrisation/(*coefficient*)length];

		Return[symmetrisation];
	]


(* ::Subsection::Closed:: *)
(*Multiple-Symmetrise*)


Options[MultipleSymmetrise]={"AntiSymmetric"->False(*,"NumericalCoefficients"\[Rule]True*)};

MultipleSymmetrise[exp_,tobesymmetrised__List,OptionsPattern[]]:=
	Module[{localexp=exp,localsymm={tobesymmetrised},coefficient},

		Do[
			localexp=Symmetrise[localexp,i,"AntiSymmetric"->OptionValue["AntiSymmetric"](*,"NumericalCoefficients"\[Rule]False*)],
			{i,localsymm}
		];

		(*If[
			OptionValue["NumericalCoefficients"],
			coefficient=Length[localexp],
			coefficient=1
		];*)

		localexp=Expand[localexp(*/coefficient*)];

		Return[localexp];
	]


(* ::Subsection:: *)
(*Young-Symmetrise*)


YoungSymmetrise[exp_,tobesymmetrised_?(Length[#]<=1&)]:=exp

YoungSymmetrise[exp_,symmetries_List]:=
	Module[{antisymmetries,symmetrisation},

		(*Antisymmetric indices*)
		antisymmetries=PadRight[#,Length[First[symmetries]]]&/@symmetries;
		antisymmetries=DeleteCases[#,0]&/@Transpose[antisymmetries];

		(*Impose symmetries*)
		symmetrisation=
			MultipleSymmetrise[
				MultipleSymmetrise[
					exp,
					Sequence@@antisymmetries,
					"AntiSymmetric"->True(*,"NumericalCoefficients"\[Rule]False*)
				],
				Sequence@@symmetries(*,
				"NumericalCoefficients"\[Rule]False*)
			];

		(*Return output*)
		symmetrisation=Expand[symmetrisation(*/Length[symmetrisation]*)];

		Return[symmetrisation];
]


(* ::Subsection:: *)
(*Multiple Young-Symmetrise*)


MultipleYoungSymmetrise[exp_,tobesymmetrised__List]:=
	Module[{localexp=exp,localsymm={tobesymmetrised},coefficient},

		Do[
			localexp=YoungSymmetrise[localexp,i],
			{i,localsymm}
		];

		localexp=Expand[localexp];

		Return[localexp];
	]


End[]


(* ::Section:: *)
(*Attributes*)


SetAttributes[
    {ReLabel,
    Symmetrise,
    MultipleSymmetrise,
    YoungSymmetrise,
    MultipleYoungSymmetrise},
    Protected
]


EndPackage[]
