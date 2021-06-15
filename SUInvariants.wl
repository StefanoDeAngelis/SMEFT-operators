(* ::Package:: *)

(* ::Title:: *)
(*SUInvariants*)


BeginPackage["SUInvariants`",{"YoungSymm`","GraphGenerator`"}]


(* ::Section:: *)
(*Messages*)


jLabel::usage = "..."
iLabel::usage = "..."
xLabel::usage = "..."

ILabel::usage = "..."
XLabel::usage = "..."

EpsilonSU2::usage = "..."

TauSU2::usage = "..."

StructureConstantSU2::usage = "..."

DeltaSU2::usage = "..."

RenameDummiesSU2::usage = "..."

ContractSU2::usage = "..."

FromMatricesToEpsilons::usage = "..."
FromStructuresToEpsilonSU2::usage = "..."
InvariantsSU2::usage = "..."

LinearRelationsSU2::usage = "..."
SubstitutionsSU2::usage = "..."

aLabel::usage = "..."
bLabel::usage = "..."

ALabel::usage = "..."
CLabel::usage = "..."

TauSU3::usage = "..."

DeltaSU3::usage = "..."

EpsilonFundSU3::usage = "..."
EpsilonAFundSU3::usage = "..."

DeltaAdjSU3::usage = "..."

TraceSU3::usage = "..."

StructureConstantSU3::usage = "..."

TensorDSU3::usage = "..."

(*RenameDummiesSU3::usage = "..."*)
ContractSU3::usage = "..."
(*JacobiSU3::usage = "..."
IndependentAdjSU3::usage = "..."*)

TakeLabels::usage = "..."
ToDelta::usage = "..."
PartitionsK::usage = "..."
AdjConstraint::usage = "..."
AllInvariantsSU3::usage = "..."
AllInvariantDeltas::usage = "..."

SimplifyInvariants::usage = "..."

AllIdentitiesSU3::usage = "..."


(* ::Section:: *)
(*Invariant Tensors for the su(2) algebra*)


Begin["`su2`"]


(* ::Text:: *)
(*Todo: add comments to the various functions.*)


(* ::Subsection:: *)
(*Labels and building blocks*)


(* ::Text:: *)
(*(*Normalisation of the generators of the gauge group generators: \[Tau]^a \[Tau]^b =(1/(2N)) \[Delta]^(a b) +(i/2) f^(a b c) \[Tau]^c+(1/2) d^(a b c)\[Tau]^c,*)
(*TODO:Check the coefficients of the substitutions*)*)


(* ::Subsubsection::Closed:: *)
(*Indices of fundamental representation*)


iBox[x_]:=
	TemplateBox[{x},"iLabel",
		DisplayFunction->(SubscriptBox["i",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"iLabel","[",RowBox[{#}],"]"}]&)]
iLabel /: MakeBoxes[iLabel[x_],StandardForm|TraditionalForm] := iBox[ToBoxes[x]]

jBox[x_]:=
	TemplateBox[{x},"jLabel",
		DisplayFunction->(SubscriptBox["j",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"jLabel","[",RowBox[{#}],"]"}]&)]
jLabel /: MakeBoxes[jLabel[x_],StandardForm|TraditionalForm] := jBox[ToBoxes[x]]

xBox[x_,n_]:=
	TemplateBox[{x,n},"xLabel",
		DisplayFunction->(SubscriptBox[#2,RowBox[{#1}]]&),
		InterpretationFunction->(RowBox[{"xLabel","[",RowBox[{#1}],",",RowBox[{#2}]"]"}]&)]
xLabel /: MakeBoxes[xLabel[x_,n_],StandardForm|TraditionalForm] := xBox[ToBoxes[x],ToBoxes[FromCharacterCode[n]]]


(* ::Subsubsection::Closed:: *)
(*Indices of the adjoint representation*)


IBox[x_]:=
	TemplateBox[{x},"ILabel",
		DisplayFunction->(SubscriptBox["I",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"ILabel","[",RowBox[{#}],"]"}]&)]
ILabel /: MakeBoxes[ILabel[x_],StandardForm|TraditionalForm] := IBox[ToBoxes[x]]

XBox[x_]:=
	TemplateBox[{x},"XLabel",
		DisplayFunction->(SubscriptBox["X",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"XLabel","[",RowBox[{#}],"]"}]&)]
XLabel /: MakeBoxes[XLabel[x_],StandardForm|TraditionalForm] := XBox[ToBoxes[x]]


(* ::Subsubsection::Closed:: *)
(*Epsilon*)


EpsilonBoxSU2[a_, b_] :=
    TemplateBox[{a, b}, "EpsilonSU2",
        DisplayFunction -> (SuperscriptBox["\[Epsilon]",RowBox[{#1,#2}]]&),
        InterpretationFunction -> (RowBox[{"EpsilonSU2","[",RowBox[{#1,",",#2}],"]"}]&)]
EpsilonSU2 /: MakeBoxes[EpsilonSU2[a_, b_], StandardForm | TraditionalForm] := EpsilonBoxSU2[ToBoxes[a], ToBoxes[b]]

EpsilonBoxSU2[][a_, b_] :=
    TemplateBox[{a, b}, "EpsilonSU2",
        DisplayFunction -> (SubscriptBox["\[Epsilon]",RowBox[{#1,#2}]]&),
        InterpretationFunction -> (RowBox[{"EpsilonSU2[]","[",RowBox[{#1,",",#2}],"]"}]&)]
EpsilonSU2 /: MakeBoxes[EpsilonSU2[][a_, b_], StandardForm | TraditionalForm] := EpsilonBoxSU2[][ToBoxes[a], ToBoxes[b]]


(* ::Subsubsection::Closed:: *)
(*Delta (fundamental)*)


EpsilonBoxSU2[a_][b_] :=
    TemplateBox[{a, b}, "EpsilonSU2",
        DisplayFunction -> (SubsuperscriptBox["\[Delta]",RowBox[{#2}],RowBox[{#1}]]&),
        InterpretationFunction -> (RowBox[{"EpsilonSU2","[",RowBox[{#1}],"]","[",RowBox[{#2}],"]"}]&)]
EpsilonSU2 /: MakeBoxes[EpsilonSU2[a_][b_], StandardForm | TraditionalForm] := EpsilonBoxSU2[ToBoxes[a]][ToBoxes[b]]


(* ::Subsubsection::Closed:: *)
(*Generators*)


TauBoxSU2[A_][a_, b_] :=
    TemplateBox[{A,a, b}, "TauSU2",
        DisplayFunction -> (SubscriptBox[SuperscriptBox["\[Sigma]",RowBox[{#1}]],RowBox[{#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"TauSU2","[",#1,"]","[",#2,",",#3,"]"}]&)]
TauSU2 /: MakeBoxes[TauSU2[A_][a_, b_], StandardForm | TraditionalForm] := TauBoxSU2[ToBoxes[A]][ToBoxes[a], ToBoxes[b]]

TauBoxSU2[A_,a_][ b_] :=
    TemplateBox[{A,a, b}, "TauSU2",
        DisplayFunction -> (SubsuperscriptBox[SuperscriptBox["\[Sigma]",RowBox[{#1}]],RowBox[{#3}],RowBox[{#2}]]&),
        InterpretationFunction -> (RowBox[{"TauSU2","[",#1, ",",#2,"]","[",#3,"]"}]&)]
TauSU2 /: MakeBoxes[TauSU2[A_,a_][ b_], StandardForm | TraditionalForm] := TauBoxSU2[ToBoxes[A],ToBoxes[a]][ ToBoxes[b]]

TauBoxSU2[A_,a_, b_] :=
    TemplateBox[{A,a, b}, "TauSU2",
        DisplayFunction -> (SuperscriptBox["\[Sigma]",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"TauSU2","[",#1 ,",",#2,",",#3,"]"}]&)]
TauSU2 /: MakeBoxes[TauSU2[A_,a_, b_], StandardForm | TraditionalForm] := TauBoxSU2[ToBoxes[A],ToBoxes[a], ToBoxes[b]]


(* ::Subsubsection::Closed:: *)
(*Structure Constants*)


StructureBoxSU2[A_,B_, C_] :=
    TemplateBox[{A,B, C}, "StructureConstantSU2",
        DisplayFunction ->(SuperscriptBox["\[Epsilon]",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"StructureConstantSU2","[",RowBox[{#1, ",",#2,",",#3}],"]"}]&)]
StructureConstantSU2 /: MakeBoxes[StructureConstantSU2[A_,B_, C_], StandardForm | TraditionalForm] := StructureBoxSU2[ToBoxes[A],ToBoxes[B], ToBoxes[C]]


(* ::Subsubsection::Closed:: *)
(*Delta (adjoint)*)


DeltaBoxSU2[A_,B_] :=
    TemplateBox[{A,B}, "DeltaSU2",
        DisplayFunction ->(SuperscriptBox["\[Delta]",RowBox[{#1,#2}]]&),
        InterpretationFunction -> (RowBox[{"DeltaSU2","[",RowBox[{#1,",",#2}],"]"}]&)]
DeltaSU2 /: MakeBoxes[DeltaSU2[A_,B_], StandardForm | TraditionalForm] := DeltaBoxSU2[ToBoxes[A],ToBoxes[B]]


(* ::Subsubsection::Closed:: *)
(*Symmetry properties of building blocks*)


EpsilonSU2[a_,b_] /;  \[Not]OrderedQ[{a,b}] := -EpsilonSU2[b,a];
EpsilonSU2[a_,b_] /;  (a==b) := 0;
EpsilonSU2[][a_,b_] /;  \[Not]OrderedQ[{a,b}] := -EpsilonSU2[][b,a];
EpsilonSU2[][a_,b_] /;  (a==b) := 0;
EpsilonSU2[a_][b_] /; (a==b) := 2;

TauSU2[A_,a_,b_] /;   \[Not]OrderedQ[{a,b}] := TauSU2[A,b,a];
TauSU2[A_][a_,b_] /;  \[Not]OrderedQ[{a,b}] := TauSU2[A][b,a];
TauSU2[A_,a_][b_] /;  (a==b) := 0;

StructureConstantSU2[A_,B_,C_] /;  \[Not]OrderedQ[{A,B,C}] :=Signature[{A,B,C}]*StructureConstantSU2[Sequence@@Sort[{A,B,C}]];
StructureConstantSU2[A_,B_,C_] /;  (A==B)||(B==C)||(A==C) :=0;

DeltaSU2[A_,B_] /; \[Not]OrderedQ[{A,B}] := DeltaSU2[B,A];
DeltaSU2[A_,B_] /; (A==B) := 3;


(* ::Subsection:: *)
(*Contractions and dummy labels*)


(* ::Subsubsection::Closed:: *)
(*Rename dummies*)


(* ::Text:: *)
(*This function should be rewritten in such a way that it counts double indices and rewrite them.*)


RenameDummiesSU2[x_Plus,n_]:=Plus@@(RenameDummiesSU2[#,n]&/@(List@@x))

RenameDummiesSU2[exp_,n_]:=
	Module[{localexp,dummies={}},
		Cases[
			{exp},
			HoldPattern[XLabel[h_]]:>AppendTo[dummies,h],
			\[Infinity]
			];
		dummies=DeleteDuplicates[dummies];
		
		localexp=ReplaceAll[exp,Thread[XLabel/@dummies->XLabel/@Table[n+i-1,{i,1,Length[dummies]}]]](*ReLabel[exp,dummies,Table[n+i-1,{i,1,Length[dummies]}]]*);
		
		Return[localexp];
	]


(* ::Subsubsection::Closed:: *)
(*Contract indices in the fundamental*)


ContractSU2[exp_Plus,dummylabel_]:= Plus@@(ContractSU2[#,dummylabel]&/@(List@@exp))
ContractSU2[exp_List,dummylabel_]:=ContractSU2[#,dummylabel]&/@exp

ContractSU2[exp_,dummylabel_]:= (*dummylabel is needed because I don't want the labels to mix with actual fields in the form factor, which will be symmetrised*)
	Module[
		{localexp=exp,raiseindices={},lowerindices,normalisationtau={},decompositiongenerators={},deltafund={},deltaadj={},dummies=dummylabel},
		
		raiseindices=
			{
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(b==d):>TauSU2[A,c][a],
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(a==d):>TauSU2[A,c][b],
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(b==c):>-TauSU2[A,d][a],
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(a==c):>-TauSU2[A,d][b],
			
			TauSU2[A_,a_][b_]EpsilonSU2[c_,d_]/;(b==d):>TauSU2[A,a,c],
			TauSU2[A_,a_][b_]EpsilonSU2[c_,d_]/;(b==c):>-TauSU2[A,a,d]
			};
			
		lowerindices=
			{
			TauSU2[A_,a_,b_]EpsilonSU2[][c_,d_]/;(b==d):>TauSU2[A,a][c],
			TauSU2[A_,a_,b_]EpsilonSU2[][c_,d_]/;(a==d):>TauSU2[A,b][c],
			TauSU2[A_,a_,b_]EpsilonSU2[][c_,d_]/;(b==c):>-TauSU2[A,a][d],
			TauSU2[A_,a_,b_]EpsilonSU2[][c_,d_]/;(a==c):>-TauSU2[A,b][d],
			
			TauSU2[A_,a_][b_]EpsilonSU2[][c_,d_]/;(a==d):>TauSU2[A][c,b],
			TauSU2[A_,a_][b_]EpsilonSU2[][c_,d_]/;(a==c):>-TauSU2[A][d,b]
			};

		deltafund =
			{
			TauSU2[A_,a_,b_]EpsilonSU2[c_][d_]/;(b==d):>TauSU2[A,a,c],
			TauSU2[A_,a_,b_]EpsilonSU2[c_][d_]/;(a==d):>TauSU2[A,c,b],
		
			TauSU2[A_,a_][b_]EpsilonSU2[c_][d_]/;(b==c):>TauSU2[A,a][d],
			TauSU2[A_,a_][b_]EpsilonSU2[c_][d_]/;(a==d):>TauSU2[A,c][b],

			TauSU2[A_][a_,b_]EpsilonSU2[c_][d_]/;(b==c):>TauSU2[A][a,d],
			TauSU2[A_][a_,b_]EpsilonSU2[c_][d_]/;(a==c):>TauSU2[A][d,b],

			EpsilonSU2[a_,b_]EpsilonSU2[c_][d_]/;(b==d):>EpsilonSU2[a,c],
			EpsilonSU2[a_,b_]EpsilonSU2[c_][d_]/;(a==d):>EpsilonSU2[c,b],
			EpsilonSU2[][a_,b_]EpsilonSU2[c_][d_]/;(b==c):>EpsilonSU2[][a,d],
			EpsilonSU2[][a_,b_]EpsilonSU2[c_][d_]/;(a==c):>EpsilonSU2[][d,b],
			
			EpsilonSU2[a_,b_]EpsilonSU2[][c_,d_]/;(b==d):>-EpsilonSU2[a][c],
			EpsilonSU2[a_,b_]EpsilonSU2[][c_,d_]/;(a==c):>-EpsilonSU2[b][d],
			EpsilonSU2[a_,b_]EpsilonSU2[][c_,d_]/;(a==d):>EpsilonSU2[b][c],
			EpsilonSU2[a_,b_]EpsilonSU2[][c_,d_]/;(b==c):>EpsilonSU2[a][d],

			EpsilonSU2[a_][b_]EpsilonSU2[c_][d_]/;(b==c):>EpsilonSU2[a][d]
			};

		decompositiongenerators=
			{
			TauSU2[A_,a_][b_]TauSU2[B_,c_][d_]/;(b==c) :>I/2* StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],a][d]+1/4*DeltaSU2[A,B]EpsilonSU2[a][d],
			
			TauSU2[A_,a_,b_]TauSU2[B_][c_,d_] /;(b==d) :> -I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],a][c]-1/4*DeltaSU2[A,B]EpsilonSU2[a][c],
			TauSU2[A_,a_,b_]TauSU2[B_][c_,d_] /;(b==c) :> -I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],a][d]-1/4*DeltaSU2[A,B]EpsilonSU2[a][d],
			TauSU2[A_,a_,b_]TauSU2[B_][c_,d_] /;(a==d) :> -I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],b][c]-1/4*DeltaSU2[A,B]EpsilonSU2[b][c],
			TauSU2[A_,a_,b_]TauSU2[B_][c_,d_] /;(a==c) :> -I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],b][d]-1/4*DeltaSU2[A,B]EpsilonSU2[b][d],
			
			TauSU2[A_,a_,b_]TauSU2[B_,c_][d_] /;(b==d) :>1/4*DeltaSU2[A,B]EpsilonSU2[a,c]-I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],a,c],
			TauSU2[A_,a_,b_]TauSU2[B_,c_][d_] /;(a==d) :>1/4*DeltaSU2[A,B]EpsilonSU2[b,c]-I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],b,c],
			
			TauSU2[A_,a_][b_]TauSU2[B_][c_,d_] /;(a==d) :> -I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++]][b,c]-1/4*DeltaSU2[A,B]EpsilonSU2[][b,c],
			TauSU2[A_,a_][b_]TauSU2[B_][c_,d_] /;(a==c) :> -I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++]][b,d]-1/4*DeltaSU2[A,B]EpsilonSU2[][b,d]
			};
			
		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,Join[raiseindices,lowerindices,deltafund,decompositiongenerators]]]&,
				localexp
			];
			
		deltaadj=
			{
			DeltaSU2[A_,B_]TauSU2[C_,a_,b_]/;(B==C):>TauSU2[A,a,b],
			DeltaSU2[A_,B_]TauSU2[C_,a_,b_]/;(A==C):>TauSU2[B,a,b],
			
			
			DeltaSU2[A_,B_]TauSU2[C_,a_][b_]/;(B==C):>TauSU2[A,a][b],
			DeltaSU2[A_,B_]TauSU2[C_,a_][b_]/;(A==C):>TauSU2[B,a][b],
			
			DeltaSU2[A_,B_]TauSU2[C_][a_,b_]/;(B==C):>TauSU2[A][a,b],
			DeltaSU2[A_,B_]TauSU2[C_][a_,b_]/;(A==C):>TauSU2[B][a,b],
			
			StructureConstantSU2[A_,B_,C_]DeltaSU2[D_,EE_] /; (C==EE):> StructureConstantSU2[A,B,D],
			StructureConstantSU2[A_,B_,C_]DeltaSU2[D_,EE_] /; (B==EE):> StructureConstantSU2[A,D,C],
			StructureConstantSU2[A_,B_,C_]DeltaSU2[D_,EE_] /; (A==EE):> StructureConstantSU2[D,B,C],
			
			
			StructureConstantSU2[A_,B_,C_]StructureConstantSU2[D_,E_,F_]:>-(DeltaSU2[A,F]*DeltaSU2[B,E]*DeltaSU2[C,D])+DeltaSU2[A,E]*DeltaSU2[B,F]*DeltaSU2[C,D]+DeltaSU2[A,F]*DeltaSU2[B,D]*DeltaSU2[C,E]-DeltaSU2[A,D]*DeltaSU2[B,F]*DeltaSU2[C,E]-DeltaSU2[A,E]*DeltaSU2[B,D]*DeltaSU2[C,F]+DeltaSU2[A,D]*DeltaSU2[B,E]*DeltaSU2[C,F],


			DeltaSU2[A_,C_]DeltaSU2[B_,D_]/;(C==D):> DeltaSU2[A,B],
			DeltaSU2[A_,C_]DeltaSU2[B_,D_]/;(C==B):> DeltaSU2[A,D],

			Power[DeltaSU2[A_,C_],2]:>3
			};
			
		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,deltaadj]]&,
				localexp
			];
		
		normalisationtau={StructureConstantSU2[A_,B_,C_]:>-4*I*TauSU2[A,xLabel[1,120]][xLabel[2,120]]TauSU2[B,xLabel[2,120]][xLabel[3,120]]TauSU2[C,xLabel[3,120]][xLabel[1,120]]};
			
		If[
			Head[localexp]===Plus,
			
			localexp=
				Plus@@(
					If[
			
						Length@Complement[Cases[#,StructureConstantSU2[A__]:>A,Infinity],Cases[#,TauSU2[A_,a_,b_]|TauSU2[A_,a_][b_]|TauSU2[A_][a_,b_]:>A,Infinity]]==1,	
			
						Expand@ReplaceRepeated[#,normalisationtau],
						
						#
				
					]&/@(List@@localexp)
					),
			
			If[
			
				Length@Complement[Cases[localexp,StructureConstantSU2[A__]:>A,Infinity],Cases[localexp,TauSU2[A_,a_,b_]|TauSU2[A_,a_][b_]|TauSU2[A_][a_,b_]:>A,Infinity]]==1,
			
				localexp=Expand@ReplaceRepeated[localexp,normalisationtau];
				
			]
			
		];
		
		normalisationtau=
			{
			TauSU2[x_,a_][b_]*TauSU2[x_,c_][d_]:>1/4*(EpsilonSU2[a,c]EpsilonSU2[][b,d]+EpsilonSU2[a][d]EpsilonSU2[c][b]),
			TauSU2[x_,a_,b_]*TauSU2[x_,c_][d_]:>1/4*(EpsilonSU2[a,c]EpsilonSU2[b][d]+EpsilonSU2[a][d]EpsilonSU2[b,c]),
			TauSU2[x_,i1_,i2_]*TauSU2[x_,i3_,i4_]:>-1/4*(EpsilonSU2[i2,i3]*EpsilonSU2[i1,i4]+EpsilonSU2[i2,i4]*EpsilonSU2[i1,i3]),
			TauSU2[x_,a_,b_]*TauSU2[x_][c_,d_]:>-1/4*(EpsilonSU2[a][c]EpsilonSU2[b][d]+EpsilonSU2[a][d]EpsilonSU2[b][c]),
			TauSU2[x_,a_][b_]*TauSU2[x_][c_,d_]:>-1/4*(EpsilonSU2[a][c]EpsilonSU2[][b,d]+EpsilonSU2[a][d]EpsilonSU2[][b,c]),
			TauSU2[x_][a_,b_]*TauSU2[x_][c_,d_]:>-1/4*(EpsilonSU2[][a,c]EpsilonSU2[][b,d]+EpsilonSU2[][a,d]EpsilonSU2[][b,c])
			};
			
		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,normalisationtau]]&,
				localexp
			];
			
		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,Join[raiseindices,lowerindices,deltafund,decompositiongenerators]]]&,
				localexp
			];
			
		localexp=RenameDummiesSU2[localexp,dummylabel];
		
		Return[localexp];
]


(* ::Subsubsection::Closed:: *)
(*Independent adjoint structures*)


(* ::Text:: *)
(*Todo!!! For the SU(2) group it is enough a function which transforms a double epsilon into a combination of deltas. Otherwise the duplicates can be isolated using the Complement function for the two lists of three indices. For now this is implemented in ContractSU2*)


(* ::Subsection:: *)
(*Generation of independent invariant tensors*)


(* ::Subsubsection::Closed:: *)
(*From the adjacency matrix to the associated epsilon structure*)


FromMatricesToEpsilons[adjacencymatrix_List,labels_List,numberpoints_Integer,numberfundlabels_Integer]:=
	Module[{countingadj=Table[119,numberpoints-numberfundlabels]}, (*we want the character of the xLabel to start from x (\[Rule] 120)*)
		
		Product[
			Product[
				EpsilonSU2[
					If[
						i<=numberfundlabels,
						iLabel[labels[[i]]],
						countingadj[[i-numberfundlabels]]++;
						xLabel[labels[[i]],countingadj[[i-numberfundlabels]]]
					],
					If[
						j<=numberfundlabels,
						iLabel[labels[[j]]],
						countingadj[[j-numberfundlabels]]++;
						xLabel[labels[[j]],countingadj[[j-numberfundlabels]]]
					]
				],
				{n,1,adjacencymatrix[[i,j]]}
			],
			{i,1,numberpoints},{j,i+1,numberpoints}
		]
		
]


(* ::Subsubsection::Closed:: *)
(*From the representation structure to the (independent) epsilon structures*)


FromStructuresToEpsilonSU2[pointslines_List]:=
	Module[{localpointslines,numberfundlabels=0,lines,labels,numberpoints=Length[pointslines],admatrices,structures},
	
		If[pointslines=={},Return[{1}]];

		localpointslines=Sort[pointslines,#1[[2]]<=#2[[2]]&]; (*fundamental first!*)

		lines=Table[localpointslines[[i,2]],{i,1,numberpoints}];
		labels=Table[localpointslines[[i,1]],{i,1,numberpoints}];

		numberfundlabels=Count[lines,1];

		admatrices=Normal/@AllNonIntersectingGraphs[lines];
		
		structures=FromMatricesToEpsilons[#,labels,numberpoints,numberfundlabels]&/@admatrices;
		
		Return[structures];
]


(* ::Subsubsection::Closed:: *)
(*From the representation structure to the (independent&simplified) invariant tensors*)


Options[InvariantsSU2]={"Dummies"->0}

InvariantsSU2[pointslines_List,OptionsPattern[]]:=
	Module[{labelsadj=TakeLabels[DeleteCases[pointslines,_?(#[[2]]!=2&)]],biggest=Max[TakeLabels[pointslines]],invariants},
		invariants=
			SimplifyInvariants[
				ContractSU2[#,Max[OptionValue["Dummies"],biggest]+1]&/@(Product[TauSU2[ILabel[i]][xLabel[i,120],xLabel[i,121]],{i,labelsadj}]*FromStructuresToEpsilonSU2[pointslines])
			];
		Return[invariants];
	]


(* ::Subsection:: *)
(*Generation of the linear relations between invariant tensors*)


(* ::Text:: *)
(*(*The relations generated by this function do not distinguish between x_i and y_i indices. Then they also make sense once they are contracted with the generators of the group. *)
(*TODO: implement the contraction in the functions above.*)*)


(* ::Subsubsection::Closed:: *)
(*Generation of the su(2) linear relations*)


Options[LinearRelationsSU2]={"Dummies"->0}

LinearRelationsSU2[pointslines_List,OptionsPattern[]]:=
	Module[{localpointslines,numberfundlabels=0,lines,labels,labelsadj,numberpoints=Length[pointslines],biggestlabel,intersecting,numberinter,nonintersecting,numbernoninter,replacements,graphlabels,generators,x,y},
	
		If[pointslines=={},Return[{}]];

		localpointslines=Sort[pointslines,#1[[2]]<=#2[[2]]&]; (*fundamental first!*)

		lines=Table[localpointslines[[i,2]],{i,1,numberpoints}];
		labels=Table[localpointslines[[i,1]],{i,1,numberpoints}];

		numberfundlabels=Count[lines,1];
		labelsadj=Table[labels[[i]],{i,numberfundlabels+1,numberpoints}];
		biggestlabel=Max[labels];

		intersecting=Normal/@AllGraphs[lines]; (*generate all graphs*)

		nonintersecting=IsGraphNonIntesercting/@intersecting; (*generate non-intersecting graphs*)
		numbernoninter=Length[nonintersecting];
		
		If[numbernoninter==0,Return[{}]];

		intersecting=Complement[intersecting,nonintersecting]; (*complement to take select the intersecting graphs*)
		numberinter=Length[intersecting];

		graphlabels=
			Join[
				Table[
					intersecting[[i]]->x[i], (*assign labels to intersecting and intersecting graphs*)
					{i,1,numberinter} (*In this way the x and y definition can be shadowed when using this package.
					I should find a better way to do this.*)
				],
				Table[
					nonintersecting[[i]]->y[i], (*assign labels to intersecting and non-intersecting graphs*)
					{i,1,numbernoninter}
				]
			];
		
		(*generators=Product[TauSU2[ILabel[labels[[i]]]][xLabel[labels[[i]],1],xLabel[labels[[i]],2]],{i,numberfundlabels+1,numberpoints}];*) (*senza motivo!*)

		nonintersecting=
			Table[
				y[i]->FromMatricesToEpsilons[nonintersecting[[i]],labels,numberpoints,numberfundlabels],
				{i,1,numbernoninter}
			];

		replacements=
			Table[
				x[i]->Total[SchoutenCrossing[intersecting[[i]]]/.graphlabels],
				{i,1,Length[intersecting]}
			];
			
		replacements=
			Table[
				FromMatricesToEpsilons[intersecting[[i]],labels,numberpoints,numberfundlabels]-
				Expand[x[i]//.replacements]/.nonintersecting,
				{i,1,numberinter}
			]; (*placing the repeated replacements inside the list speeds the function up*)
			
		replacements=ContractSU2[#,Max[OptionValue["Dummies"],biggestlabel]+1]&/@(Product[TauSU2[ILabel[i]][xLabel[i,120],xLabel[i,121]],{i,labelsadj}]*replacements); (*Contractions with the generators of the group and contractions*)
		
		replacements=
			DeleteDuplicates[
				If[NumberQ[#[[1,1]]],(#/#[[1,1]])//Expand,#]&/@DeleteCases[replacements,0] (*normalisations and repetitions are taken into account*)
			];

		Return[replacements];

]


(* ::Subsubsection::Closed:: *)
(*All Invariants of su(2) appearing in the linear relations*)


Options[SubstitutionsSU2]={"Dummies"->0}

SubstitutionsSU2[pointslines_List,OptionsPattern[]]:=
	Module[{independent,num1,dependent,num2,linear=LinearRelationsSU2[pointslines,"Dummies"->OptionValue["Dummies"]],x,y,subs,substitutions},
		If[linear=={},Return[{}]];
		independent=InvariantsSU2[pointslines,"Dummies"->OptionValue["Dummies"]]; (*the first two lines speed up the computation of a factor 10^-2 for the cases where we do not have dependent invariants*)
		dependent=
			Complement[
				DeleteDuplicates[
					If[NumberQ[#[[1]]],(#/#[[1]])//Expand,#]&/@Flatten[linear/.Plus->List]
				],
				independent
			];
		num1=Length[independent];
		num2=Length[dependent];
		subs=
			Join[
				Thread[Rule[independent,Table[x[i],{i,num1}]]],
				Thread[Rule[dependent,Table[y[i],{i,num2}]]]
			];
		substitutions=
			Flatten[
				Solve[
					Thread[(linear/.subs)==Table[0,Length[linear]]],
					Table[y[i],{i,num2}]
				]/.(Reverse/@subs)//Expand
			];
		Return[substitutions];
	]


End[]


(* ::Section:: *)
(*Invariant Tensors for the su(N) algebras*)


Begin["`suN`"]


(* ::Subsection:: *)
(*Labels and building blocks*)


(* ::Subsubsection::Closed:: *)
(*Indices of the fundamental representation*)


aBox[x_]:=
	TemplateBox[{x},"aLabel",
		DisplayFunction->(SubscriptBox["a",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"aLabel","[",RowBox[{#}],"]"}]&)]

bBox[x_]:=
	TemplateBox[{x},"bLabel",
		DisplayFunction->(SubscriptBox["b",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"bLabel","[",RowBox[{#}],"]"}]&)]
		
aLabel /: MakeBoxes[aLabel[x_],StandardForm|TraditionalForm] :=aBox[ToBoxes[x]]
bLabel /: MakeBoxes[bLabel[x_],StandardForm|TraditionalForm] :=bBox[ToBoxes[x]]


(* ::Subsubsection::Closed:: *)
(*Indices of the adjoint representation*)


ABox[x_]:=
	TemplateBox[{x},"ALabel",
		DisplayFunction->(SubscriptBox["A",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"ALabel","[",RowBox[{#}],"]"}]&)]
ALabel /: MakeBoxes[ALabel[x_],StandardForm|TraditionalForm] := ABox[ToBoxes[x]]

CBox[x_]:=
	TemplateBox[{x},"CLabel",
		DisplayFunction->(SubscriptBox["C",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"CLabel","[",RowBox[{#}],"]"}]&)]
CLabel /: MakeBoxes[CLabel[x_],StandardForm|TraditionalForm] := CBox[ToBoxes[x]]


(* ::Subsubsection::Closed:: *)
(*Generators*)


(*Old modified by Manuel*)
(*TauBoxSU3[A__,a_, b_] :=
    TemplateBox[{a, b,A}, "TauSU3",
        DisplayFunction -> (SubscriptBox[SuperscriptBox["\[Tau]",RowBox[{##3,#1}]],RowBox[{#2}]]&),
        InterpretationFunction -> (RowBox[{"TauSU3","[",##3,",",#1,",",#2,"]"}]&)];
        
TauSU3 /: MakeBoxes[TauSU3[A__,a_, b_], StandardForm | TraditionalForm] := TauBoxSU3[Sequence@@(ToBoxes/@{A}),ToBoxes[a], ToBoxes[b]]
*)

(*Manuel's new version. Non elegantissimo ma funziona sempre (credo)*)
TauBoxSU3[A__,a_, b_] :=
    TemplateBox[{A,a, b}, "TauSU3",
        DisplayFunction -> (Evaluate@SubscriptBox[SuperscriptBox["\[Tau]",RowBox[{TemplateSlotSequence[{1,Length[{A}]}],Slot[Length[{A}]+1]}]],RowBox[{Slot[Length[{A}]+2]}]]&)];
        
TauSU3 /: MakeBoxes[TauSU3[A__,a_, b_], StandardForm | TraditionalForm] := TauBoxSU3[Sequence@@(ToBoxes/@{A}),ToBoxes[a], ToBoxes[b]];


(* ::Subsubsection::Closed:: *)
(*Delta*)


DeltaBoxSU3[a_, b_] :=
    TemplateBox[{a, b}, "DeltaSU3",
        DisplayFunction -> (SubsuperscriptBox["\[Delta]",RowBox[{#2}],RowBox[{#1}]]&),
        InterpretationFunction -> (RowBox[{"DeltaSU3","[",RowBox[{#1 ,",",#2}],"]"}]&)]
DeltaSU3 /: MakeBoxes[DeltaSU3[a_, b_], StandardForm | TraditionalForm] := DeltaBoxSU3[ToBoxes[a], ToBoxes[b]]


(* ::Subsubsection::Closed:: *)
(*Epsilons (three fundamentals and three antifundamentals)*)


EpsilonFundBoxSU3[a_,b_,c_]:=
	TemplateBox[{a, b,c}, "EpsilonFundSU3",
        DisplayFunction -> (SubscriptBox["\[Epsilon]",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"EpsilonFundSU3","[",RowBox[{#1,",",#2,",",#3}],"]"}]&)]
EpsilonFundSU3 /: MakeBoxes[EpsilonFundSU3[a_, b_,c_], StandardForm | TraditionalForm] := EpsilonFundBoxSU3[ToBoxes[a], ToBoxes[b],ToBoxes[c]]

EpsilonAFundBoxSU3[a_,b_,c_]:=
	TemplateBox[{a, b,c}, "EpsilonAFundSU3",
        DisplayFunction -> (SuperscriptBox["\[Epsilon]",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"EpsilonAFundSU3","[",RowBox[{#1,",",#2,",",#3}],"]"}]&)]
EpsilonAFundSU3 /: MakeBoxes[EpsilonAFundSU3[a_, b_,c_], StandardForm | TraditionalForm] := EpsilonAFundBoxSU3[ToBoxes[a], ToBoxes[b],ToBoxes[c]]


(* ::Subsubsection::Closed:: *)
(*Delta (adjoint)*)


DeltaAdjBoxSU3[A_, B_] :=
    TemplateBox[{A, B}, "DeltaAdjSU3",
        DisplayFunction -> (SuperscriptBox["\[Delta]",RowBox[{#1,#2}]]&),
        InterpretationFunction -> (RowBox[{"DeltaAdjSU3","[",RowBox[{#1 ,",",#2}],"]"}]&)]
DeltaAdjSU3 /: MakeBoxes[DeltaAdjSU3[A_, B_], StandardForm | TraditionalForm] := DeltaAdjBoxSU3[ToBoxes[A], ToBoxes[B]]


(* ::Subsubsection::Closed:: *)
(*Trace structures*)


(*Old*)
(*TraceBoxSU3[A__] :=
    TemplateBox[{A}, "TraceSU3",
        DisplayFunction -> (SuperscriptBox["\[Tau]",RowBox[{##}]]&),
        InterpretationFunction -> (RowBox[{"TraceSU3","[",RowBox[{##}],"]"}]&)]
TraceSU3 /: MakeBoxes[TraceSU3[A__], StandardForm | TraditionalForm] := TraceBoxSU3[Sequence@@(ToBoxes/@{A})]*)

(*Manuel version*)
TraceBoxSU3[A__] :=
    TemplateBox[{A}, "TraceSU3",
        DisplayFunction -> (SuperscriptBox["\[Tau]",RowBox[{##}]]&)];
        
TraceSU3 /: MakeBoxes[TraceSU3[A__], StandardForm | TraditionalForm] := TraceBoxSU3[Sequence@@(ToBoxes/@{A})];


(* ::Subsubsection::Closed:: *)
(*Structure constants*)


StructureBoxSU3[A_, B_,C_] :=
    TemplateBox[{A, B,C}, "StructureConstantSU3",
        DisplayFunction -> (SuperscriptBox["f",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"StructureConstantSU3","[",RowBox[{#1,",",#2,",",#3}],"]"}]&)]
StructureConstantSU3 /: MakeBoxes[StructureConstantSU3[A_, B_,C_], StandardForm | TraditionalForm] := StructureBoxSU3[ToBoxes[A], ToBoxes[B],ToBoxes[C]]


(* ::Subsubsection::Closed:: *)
(*d-tensors*)


TensorDBoxSU3[A_, B_,C_] :=
    TemplateBox[{A, B,C}, "TensorDSU3",
        DisplayFunction -> (SuperscriptBox["d",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"TensorDSU3","[",RowBox[{#1,",",#2,",",#3}],"]"}]&)]
TensorDSU3/: MakeBoxes[TensorDSU3[A_, B_,C_], StandardForm | TraditionalForm] := TensorDBoxSU3[ToBoxes[A], ToBoxes[B],ToBoxes[C]]


(* ::Subsubsection::Closed:: *)
(*Symmetry properties of the building blocks*)


StructureConstantSU3[A_,B_,C_] /;  \[Not]OrderedQ[{A,B,C}] :=Signature[{A,B,C}]*StructureConstantSU3[Sequence@@Sort[{A,B,C}]];

TensorDSU3[A_,B_,C_] /; \[Not]OrderedQ[{A,B,C}] :=TensorDSU3[Sequence@@Sort[{A,B,C}]];

EpsilonFundSU3[a_,b_,c_] /; \[Not]OrderedQ[{a,b,c}] := Signature[{a,b,c}]*EpsilonFundSU3[Sequence@@Sort[{a,b,c}]]
EpsilonAFundSU3[a_,b_,c_] /; \[Not]OrderedQ[{a,b,c}] := Signature[{a,b,c}]*EpsilonAFundSU3[Sequence@@Sort[{a,b,c}]]

DeltaAdjSU3[A_,B_] /; \[Not]OrderedQ[{A,B}] := DeltaAdjSU3[B,A];

TraceSU3[A__]/;(First@Ordering[{A}]!=1):=TraceSU3[Sequence@@RotateLeft[{A},First@Ordering[{A}]-1]];
TraceSU3[A__]/;Length[{A}]==2:=DeltaAdjSU3[A]/2;

StructureConstantSU3[A_,B_,C_] /;  (A==B)||(B==C)||(A==C) :=0;

TensorDSU3[A_,B_,C_] /;  (A==B)||(B==C)||(A==C) :=0;


(* ::Subsection:: *)
(*Contractions and dummy labels*)


(* ::Subsubsection::Closed:: *)
(*Rename dummies*)


(*RenameDummiesSU3[x_Plus,n_]:=Plus@@(RenameDummiesSU3[#,n]&/@(List@@x))

RenameDummiesSU3[exp_,n_]:=
	Module[{localexp,dummies={}},
		Cases[
			{exp},
			HoldPattern[CLabel[h_]]:>AppendTo[dummies,h],
			\[Infinity]
		];
		dummies=DeleteDuplicates[dummies];
		localexp=ReLabel[exp,dummies,Table[n+i-1,{i,1,Length[dummies]}]];
		Return[localexp];
	]*)


(* ::Subsubsection::Closed:: *)
(*Contract indices*)


ContractSU3[exp_(*,dummylabel_*)]:= (*dummylabel is needed because I don't want the labels to mix with actual fields in the form factor, which will be symmetrised*)
	Module[
		{localexp=exp,eliminatedeltas,decompositiongenerators(*,normandsymm*)(*,dummies=dummylabel*),compositiongenerators},
		eliminatedeltas=
			{
			TauSU3[A_,a_,b_]DeltaSU3[c_,d_]/;(b==c):>TauSU3[A,a,d],
			TauSU3[A_,a_,b_]DeltaSU3[c_,d_]/;(a==d):>TauSU3[A,c,b],
			DeltaSU3[a_,b_]DeltaSU3[c_,d_] /; (b==c):>DeltaSU3[a,d],

			TauSU3[A_,a_,b_] /; (a==b):>0,
			DeltaSU3[a_,b_] /; (a==b) :> 3,
			
			EpsilonAFundSU3[d_,e_,f_]EpsilonFundSU3[a_,b_,c_] :> -(DeltaSU3[d, c]*DeltaSU3[e, b]*DeltaSU3[f, a]) + DeltaSU3[d, b]*DeltaSU3[e, c]*DeltaSU3[f, a] + DeltaSU3[d, c]*DeltaSU3[e, a]*DeltaSU3[f, b] - DeltaSU3[d, a]*DeltaSU3[e, c]*DeltaSU3[f, b] - DeltaSU3[d, b]*DeltaSU3[e, a]*DeltaSU3[f, c] + DeltaSU3[d, a]*DeltaSU3[e, b]*DeltaSU3[f, c],

			DeltaAdjSU3[A_,B_] /; (A==B) :> 8,

			StructureConstantSU3[A_,B_,C_]DeltaAdjSU3[D_,EE_] /; (C==EE):> StructureConstantSU3[A,B,D],
			
			TauSU3[A_,a_,b_]DeltaAdjSU3[B_,C_]/;(C==A):>TauSU3[B,a,b],

			TensorDSU3[A_,B_,C_] DeltaAdjSU3[D_,EE_]/;(C==EE):>TensorDSU3[A,B,D],

			DeltaAdjSU3[A_,C_] DeltaAdjSU3[B_,EE_]/;(C==EE):>DeltaAdjSU3[A,B]
			};
		decompositiongenerators=
			{
			TauSU3[A_,a_,b_]TauSU3[B_,c_,d_] /;(b==c)&&(a==d) :> 1/2 * DeltaAdjSU3[A,B](*,

			TauSU3[A_,a_,b_]TauSU3[B_,c_,d_]/; (b==c) :> I/2* StructureConstantSU3[A,B,CLabel[dummies]] TauSU3[CLabel[dummies],a,d]+1/2* TensorDSU3[A,B,CLabel[dummies]] TauSU3[CLabel[dummies++],a,d] + 1/6*DeltaAdjSU3[A,B] *DeltaSU3[a,d]*)
			};
		(*normandsymm=
			{
			StructureConstantSU3[A_,C_,D_]TensorDSU3[B_,EE_,FF_]/;(C\[Equal]EE)&&(D\[Equal]FF) \[RuleDelayed] 0,

		StructureConstantSU3[A_,C_,D_]StructureConstantSU3[B_,EE_,FF_]/;(C\[Equal]EE)&&(D\[Equal]FF) \[RuleDelayed]3 * DeltaAdjSU3[A,B],

		TensorDSU3[A_,C_,D_]TensorDSU3[B_,EE_,FF_]/;(C\[Equal]EE)&&(D\[Equal]FF) \[RuleDelayed](3^2-4)/3* DeltaAdjSU3[A,B] (*(N^2-4)/N*)
			};*)
		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,Join[eliminatedeltas,decompositiongenerators(*,normandsymm*)]]]&,
				localexp
			];
		
		compositiongenerators=
			{
			TauSU3[A__,a_,b_]TauSU3[B__,c_,d_]/;b==c:>TauSU3[A,B,a,d],
			
			TauSU3[A__,a_,b_]/;a==b&&Length[{A}]>1:>TraceSU3[A]
			};
		localexp=ReplaceRepeated[localexp,compositiongenerators];
		(*localexp=RenameDummiesSU3[localexp,dummylabel];*)
		Return[localexp];
	]


(* ::Text:: *)
(*Todo: understand whether the "normandsymm" relations and their generalisations are needed for higher-dimension representations*)


(* ::Subsubsection::Closed:: *)
(*Jacobi identities*)


(*JacobiSU3[exp_]:=
	Module[{localexp=exp,jacobi},

		jacobi=
			(
			StructureConstantSU3[A_,D_,E_]StructureConstantSU3[B_,C_,F_]/;(E==F)&&OrderedQ[{A,B,C,D}]:>StructureConstantSU3[A,C,E]StructureConstantSU3[B,D,E]-StructureConstantSU3[A,B,E]StructureConstantSU3[C,D,E]
			);

		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,jacobi]]&,
				localexp
			];

		Return[localexp];

	]*)


(* ::Subsubsection::Closed:: *)
(*Independent adjoint structures with four free indices*)


(*TODO: avoid the repeated replacement but give a general one with a DuplicateFreeQ conditions and Signature for the sign from the different ordering*)


(*IndependentAdjSU3[exp_]:=
	Module[{localexp=exp,replacements},

		replacements=
			{
			StructureConstantSU3[A_,B_,EE_]StructureConstantSU3[C_,D_,F_]/;(EE==F):> (-2*DeltaAdjSU3[A, D]*DeltaAdjSU3[B, C])/3 + (2*DeltaAdjSU3[A, C]*DeltaAdjSU3[B, D])/3 + I*StructureConstantSU3[B, D, EE]*TensorDSU3[A, C, EE] + I*StructureConstantSU3[B, C, EE]*TensorDSU3[A, D, EE] + I*StructureConstantSU3[A, D, EE]*TensorDSU3[B, C, EE] - TensorDSU3[A, D, EE]*TensorDSU3[B, C, EE] + I*StructureConstantSU3[A, C, EE]*TensorDSU3[B, D, EE] + TensorDSU3[A, C, EE]*TensorDSU3[B, D, EE],
			
			StructureConstantSU3[C_,D_,F_]TensorDSU3[A_,B_,EE_]/;(EE==F&&OrderedQ[{C,A}]):> -StructureConstantSU3[A,D,EE]TensorDSU3[B,C,EE]-StructureConstantSU3[B,D,EE]TensorDSU3[C,A,EE]
			};

		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,replacements]]&,
				localexp
			];

		Return[localexp];

	]*)


(* ::Subsection:: *)
(*Generation of the independent invariant tensors*)


(* ::Subsubsection::Closed:: *)
(*Adjoint constraint (on delta representation of the invariats)*)


AdjConstraint[x_Plus]:=Plus@@(AdjConstraint/@(List@@x))
AdjConstraint[x_Times]:=Times@@(AdjConstraint/@(List@@x))
AdjConstraint[x_]:=If[MatchQ[x,DeltaSU3[aLabel[a_],bLabel[b_]]/;a==b],0,x]


(* ::Subsubsection::Closed:: *)
(*Some functions*)


TakeLabels[labelsreps_List]:=Table[labelsreps[[i,1]],{i,1,Length[labelsreps]}]
ToDelta[{l1_,l2_}]:=DeltaSU3[aLabel[l1],bLabel[l2]]
ToDelta[{l1_,l2_,l3_}]:=EpsilonFundSU3[bLabel[l1],bLabel[l2],bLabel[l3]]
ToDelta[{{l1_},{l2_},{l3_}}]:=EpsilonAFundSU3[aLabel[l1],aLabel[l2],aLabel[l3]]


(* ::Subsubsection::Closed:: *)
(*PartitionK*)


PartitionsK[list_,l_]/;Length[list]==l:={{list}}

PartitionsK[list_,l_]:= (*Iterative definition of the partitions of a set in subsets with l elements (Length[list]/l has to be an integer)*)
	Join@@
		Table[
			{x,##}&@@@PartitionsK[Complement[list,x],l], (*# represent the first argument supplied to a pure function, ## represents a slot of arguments*)
			{x,Subsets[list,{l},Binomial[Length[list]-1,l-1]]} (*Binomial[Length[list]-1,l-1] is the number of subsets with the first element of list. This avoids repetitions.*)
		]


(* ::Subsubsection:: *)
(*All invariants (list form)*)


AllInvariantsSU3[labelsrepresentations_List]:=
	Module[{labelsfund,labelsantif,allinvariants,numfund,numafund,mod3},
		
		labelsfund=
			TakeLabels[
				Select[labelsrepresentations,#[[2]]>=0&]
			];
		labelsantif=
			TakeLabels[
				Select[labelsrepresentations,#[[2]]<=0&]
			];
		
		numfund=Length[labelsfund];
		numafund=Length[labelsantif];
		mod3=(numfund-numafund)/3;

		If[\[Not]IntegerQ[mod3],Return[0]];
			
		If[
			mod3==0,
			labelsantif=Permutations[labelsantif];
			allinvariants=
				Transpose/@
					Tuples[{{labelsfund},labelsantif}];
					(*Can this be made faster by using Join as below? TODO!*)
			allinvariants=
				If[MemberQ[#,x_/;(x[[1]]==x[[2]])],Nothing,#]&/@allinvariants;
				(*MemberQ is needed because it is enough for one of the deltas to be {i,i} for the invariant to be zero*)
			Return[allinvariants]
		];

		If[
			mod3>0,
			
			If[
				numafund>0,
				
				labelsfund=
					Join@@
						Table[
							{i,##}&@@@Map[List,PartitionsK[Complement[labelsfund,i],3],{3}],
							{i,Flatten[Permutations/@Subsets[labelsfund,{numafund}],1]}
						];
			
				allinvariants=
					MapAt[
						Sequence@@
							Transpose[
								Join[{#},{labelsantif}]
							]&,
						labelsfund,
						{All,1}
					];
				allinvariants=If[MemberQ[#,x_/;(x[[1]]==x[[2]])],Nothing,#]&/@allinvariants,
				
				allinvariants=Map[List,PartitionsK[labelsfund,3],{3}];
			];
			
			Return[allinvariants],
			
			If[
				numfund>0,
				
				labelsantif=
					Join@@
						Table[
							{i,##}&@@@PartitionsK[Complement[labelsantif,i],3], (*similar to the definition of PartitionK, we take the excedeeing elements*)
							{i,Flatten[Permutations/@Subsets[labelsantif,{numfund}],1]}(*permutations of the subsets with number of elements equal to the number of exceding elements between fund and antifund*)
						];
					
				allinvariants=
					MapAt[
						Sequence@@
							Transpose[
								Join[{labelsfund},{#}]
							]&,
						labelsantif,
						{All,1}
					];
				allinvariants=If[MemberQ[#,x_/;(x[[1]]==x[[2]])],Nothing,#]&/@allinvariants,
				
				allinvariants=PartitionsK[labelsantif,3]
			];
			
			Return[allinvariants]
		]
	]


(* ::Subsubsection:: *)
(*All invariant (representation with deltas)*)


AllInvariantDeltas[labelsrepresentations_List]:=Times@@@Map[ToDelta,AllInvariantsSU3[labelsrepresentations],{2}]


(* ::Subsection::Closed:: *)
(*Simplifying the invariant tensors (both SU(2) and SU(3))*)


SimplifyInvariants[list_List]:=
	Module[{localinv=Sort[list],number=Length[list]},
		If[list=={1},Return[{1}]];
		Do[
			If[
				Head[localinv[[i]]]===Plus, (*TrueQ, which gives true only if the expression evaluates to true. Gives false in any other case.*)
				localinv[[i]]=localinv[[i,1]]
			];
			If[
				Head[localinv[[i]]]===Times,
				localinv[[i]]=
					If[
						NumberQ[localinv[[i,1]]],
						Delete[localinv[[i]],1],
						localinv[[i]]
					]
			];
			Do[
				localinv[[j]]=localinv[[j]]/.{localinv[[i]]->0},
				{j,i+1,number}
			],
			{i,1,number}
		];
		Return[localinv];
	]


(* ::Subsection::Closed:: *)
(*Relations between the SU(3) invariants up to dimension 8 SMEFT operators (up to dimension 9 for the moment)*)


AllIdentitiesSU3[labelsrepresentations_List]:=
	Module[{labelsfund,labelsantif,labelsadj,dummies,nA,nAF,nF,invariants,x,delta,identities},
		labelsfund=TakeLabels[Select[labelsrepresentations,#[[2]]==1&]];
		labelsantif=TakeLabels[Select[labelsrepresentations,#[[2]]==-1&]];
		labelsadj=TakeLabels[Select[labelsrepresentations,#[[2]]==0&]];
(*dummies=Max[Join[labelsfund,labelsantif,labelsadj]]+1;*)
		
		nA=Length[labelsadj];
		nF=Length[labelsfund];
		nAF=Length[labelsantif];
		
		labelsfund=Join[labelsfund,labelsadj];
		
		labelsantif=Join[labelsantif,labelsadj];
		
		If[(nA+nF<4)&&(nAF+nA<4),Return[{}]];
		
		If[nA+nF==4||nAF+nA==4,
			If[nF==nAF,
				delta=Times@@ToDelta/@Transpose[{labelsfund,labelsantif}];
				identities=4!*AdjConstraint[Symmetrise[delta,bLabel/@labelsantif,"AntiSymmetric"->True]]//Expand;
				identities=Product[TauSU3[ALabel[i],bLabel[i],aLabel[i]],{i,labelsadj}]*identities;
				identities=(*ContractSU3[IndependentAdjSU3[*)ContractSU3[identities(*,dummies]*)](*,dummies]*)
			];
			If[nF<nAF,
				delta={List/@Take[labelsantif,nAF-nF],Take[labelsantif,-nF-nA]};
				delta=MapAt[Sequence@@Partition[#,3]&,delta,1];
				delta=Times@@ToDelta/@MapAt[Sequence@@Transpose[{#,labelsfund}]&,delta,2];
				identities=4*AdjConstraint[Symmetrise[delta,aLabel/@labelsantif,"AntiSymmetric"->True]]//Expand;
				identities=Product[TauSU3[ALabel[i],bLabel[i],aLabel[i]],{i,labelsadj}]*identities;
				identities=(*ContractSU3[IndependentAdjSU3[*)ContractSU3[identities(*,dummies]*)](*,dummies]*)
			];
			If[nAF<nF,
				delta={Take[labelsfund,nF-nAF],Take[labelsfund,-nA-nAF]};
				delta=MapAt[Sequence@@Partition[#,3]&,delta,1];
				delta=Times@@ToDelta/@MapAt[Sequence@@Transpose[{labelsantif,#}]&,delta,2];
				identities=4*AdjConstraint[Symmetrise[delta,bLabel/@labelsfund,"AntiSymmetric"->True]]//Expand;
				identities=Product[TauSU3[ALabel[i],bLabel[i],aLabel[i]],{i,labelsadj}]*identities;
				identities=(*ContractSU3[IndependentAdjSU3[*)ContractSU3[identities(*,dummies]*)](*,dummies]*)
			];
			
			invariants=If[NumberQ[#[[1]]]&&Head[#]==Times,Delete[#,1],#]&/@ContractSU3[Product[TauSU3[ALabel[i],bLabel[i],aLabel[i]],{i,labelsadj}]AllInvariantDeltas[labelsrepresentations]];
			invariants=Thread[Table[Rule[invariants[[i]],x[i]],{i,1,Length[invariants]}]];
	
			invariants=Flatten[Solve[(identities/.invariants)==0]/.(Reverse/@invariants)];
			Return[invariants]
		];
		If[nA+nF>5||nAF+nF>5,Return[{}]];
	]


(* ::Text:: *)
(*Todo: generalise the function above to higher-dimensional representations*)


End[]


(* ::Text:: *)
(**)


(* ::Section:: *)
(*Attributes*)


Protect@@Names["SUInvariants`*"]

EndPackage[]
