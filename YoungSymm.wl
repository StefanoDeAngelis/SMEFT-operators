(* ::Package:: *)

(* ::Chapter:: *)
(*YoungSymm*)


BeginPackage["YoungSymm`"]


(* ::Section:: *)
(*Messages*)


ReLabel::usage = "..."
Symmetrise::usage = "..."
MultipleSymmetrise::usage = "..."
YoungSymmetriser::usage = "..."


(* ::Section:: *)
(*Functions*)


Begin["`Private`"]


(* ::Subsection:: *)
(*ReLabel*)


(*ReLabel[exp_,toberelabelled_,newlabels_]:=
	ReplaceAll[
		exp,
		Join[
			{s_Power:>s,s_Rational:>s},
			Thread[Flatten[toberelabelled]->Flatten[newlabels]]
		]
	]*)
	
ReLabel[x_Plus,tobe_,new_]:=Plus@@(ReLabel[#,tobe,new]&/@(List@@x))
ReLabel[x_Times,tobe_,new_]:=Times@@(ReLabel[#,tobe,new]&/@(List@@x))

ReLabel[exp_,toberelabelled_,newlabels_]:=
	Module[{localexp=exp,power=1},
	
		If[NumberQ[localexp],Return[localexp]];
		
		If[MatchQ[localexp,Power[_,_]],power=localexp[[2]];localexp=localexp[[1]]];
		
		localexp=ReplaceAll[localexp,Thread[Flatten[toberelabelled]->Flatten[newlabels]]];
		
		Return[Power[localexp,power]];
	]


(* ::Subsection:: *)
(*Symmetrise*)


Options[Symmetrise]={"AntiSymmetric"->False(*,"NumericalCoefficients"\[Rule]True*)}; (*The NumericalCoefficients options is necessary when the label to permute are numbers. Wrong replacement could appear while working with numbers. At the present stage of the function ReLabel this should not be the case anymore, so the option NumericalCoefficients is commented.*)

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


(* ::Subsection:: *)
(*Multiple-Symmetrise*)


Options[MultipleSymmetrise]={"AntiSymmetric"->False(*,"NumericalCoefficients"\[Rule]True*)};

MultipleSymmetrise[exp_,tobesymmetrised__List,OptionsPattern[]]:=
	Module[{localexp=exp,localsymm={tobesymmetrised},coefficient},

		Do[
			localexp=Symmetrise[localexp,localsymm[[i]],"AntiSymmetric"->OptionValue["AntiSymmetric"](*,"NumericalCoefficients"\[Rule]False*)],
			{i,1,Length[localsymm]}
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


YoungSymmetriser[exp_,symmetries_List]:=
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


End[]


(* ::Section:: *)
(*Attributes*)


SetAttributes[
    {ReLabel,
    Symmetrise,
    MultipleSymmetrise,
    YoungSymmetriser},
    Protected
]


EndPackage[]
