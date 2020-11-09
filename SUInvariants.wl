(* ::Package:: *)

(* ::Title:: *)
(*SUInvariants*)


BeginPackage["SUInvariants`",{"YoungSymm`","GraphGenerator`"}]


(* ::Section:: *)
(*Messages*)


iBox::usage = "..."
iLabel::usage = "..."
xBox::usage = "..."
xLabel::usage = "..."

IBox::usage = "..."
ILabel::usage = "..."
XBox::usage = "..."
XLabel::usage = "..."

EpsilonBoxSU2::usage = "..."
EpsilonSU2::usage = "..."

TauBoxSU2::usage = "..."
TauSU2::usage = "..."

StructureBoxSU2::usage = "..."
StructureConstantSU2::usage = "..."

DeltaBoxSU2::usage = "..."
DeltaSU2::usage = "..."

RenameDummiesSU2::usage = "..."

ContractSU2::usage = "..."
JacobiSU2::usage = "..."

FromMatricesToEpsilons::usage = "..."
FromStructuresToEpsilonSU2::usage = "..."

SchoutenCrossing::usage = "..."
LinearRelationsSU2::usage = "..."

aBox::usage = "..."
bBox::usage = "..."
aLabel::usage = "..."
bLabel::usage = "..."

ABox::usage = "..."
ALabel::usage = "..."
CBox::usage = "..."
CLabel::usage = "..."

TauBoxSU3::usage = "..."
TauSU3::usage = "..."

DeltaBoxSU3::usage = "..."
DeltaSU3::usage = "..."

DeltaAdjBoxSU3::usage = "..."
DeltaAdjSU3::usage = "..."

StructureBoxSU3::usage = "..."
StructureConstantSU3::usage = "..."

TensorDBoxSU3::usage = "..."
TensorDSU3::usage = "..."

RenameDummiesSU3::usage = "..."
ContractSU3::usage = "..."
JacobiSU3::usage = "..."
IndependentAdjSU3::usage = "..."

TakeLabels::usage = "..."
ToDelta::usage = "..."
PairingsToDelta::usage = "..."
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
		InterpretationFunction->(RowBox[{"iLabel","[",RowBox[#],"]"}]&)]
iLabel /: MakeBoxes[iLabel[x_],StandardForm|TraditionalForm] := iBox[ToBoxes[x]]

xBox[x_,n_]:=
	TemplateBox[{x,n},"xLabel",
		DisplayFunction->(SubscriptBox[#2,RowBox[{#1}]]&),
		InterpretationFunction->(RowBox[{"xLabel","[",RowBox[#1],",",RowBox[#2]"]"}]&)]
xLabel /: MakeBoxes[xLabel[x_,n_],StandardForm|TraditionalForm] := xBox[ToBoxes[x],ToBoxes[FromCharacterCode[n]]]


(* ::Subsubsection::Closed:: *)
(*Indices of the adjoint representation*)


IBox[x_]:=
	TemplateBox[{x},"ILabel",
		DisplayFunction->(SubscriptBox["I",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"ILabel","[",RowBox[#],"]"}]&)]
ILabel /: MakeBoxes[ILabel[x_],StandardForm|TraditionalForm] := IBox[ToBoxes[x]]

XBox[x_]:=
	TemplateBox[{x},"XLabel",
		DisplayFunction->(SubscriptBox["X",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"XLabel","[",RowBox[#],"]"}]&)]
XLabel /: MakeBoxes[XLabel[x_],StandardForm|TraditionalForm] := XBox[ToBoxes[x]]


(* ::Subsubsection::Closed:: *)
(*Epsilon*)


EpsilonBoxSU2[a_, b_] :=
    TemplateBox[{a, b}, "EpsilonSU2",
        DisplayFunction -> (SuperscriptBox["\[Epsilon]",RowBox[{#1,#2}]]&),
        InterpretationFunction -> (RowBox[{"EpsilonSU2","[",RowBox[{#1,",",#2}],"]"}]&)]
EpsilonSU2 /: MakeBoxes[EpsilonSU2[a_, b_], StandardForm | TraditionalForm] := EpsilonBoxSU2[ToBoxes[a], ToBoxes[b]]


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
        InterpretationFunction -> (RowBox[{"TauSU2","[",RowBox[{#1,"]","[",#2,",",#3}],"]"}]&)]
TauSU2 /: MakeBoxes[TauSU2[A_][a_, b_], StandardForm | TraditionalForm] := TauBoxSU2[ToBoxes[A]][ToBoxes[a], ToBoxes[b]]

TauBoxSU2[A_,a_][ b_] :=
    TemplateBox[{A,a, b}, "TauSU2",
        DisplayFunction -> (SubsuperscriptBox[SuperscriptBox["\[Sigma]",RowBox[{#1}]],RowBox[{#3}],RowBox[{#2}]]&),
        InterpretationFunction -> (RowBox[{"TauSU2","[",RowBox[{#1 ",",#2,"]","[",",",#3}],"]"}]&)]
TauSU2 /: MakeBoxes[TauSU2[A_,a_][ b_], StandardForm | TraditionalForm] := TauBoxSU2[ToBoxes[A],ToBoxes[a]][ ToBoxes[b]]

TauBoxSU2[A_,a_, b_] :=
    TemplateBox[{A,a, b}, "TauSU2",
        DisplayFunction -> (SuperscriptBox["\[Sigma]",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"TauSU2","[",RowBox[{#1 ",",#2,",",#3}],"]"}]&)]
TauSU2 /: MakeBoxes[TauSU2[A_,a_, b_], StandardForm | TraditionalForm] := TauBoxSU2[ToBoxes[A],ToBoxes[a], ToBoxes[b]]


(* ::Subsubsection::Closed:: *)
(*Structure Constants*)


StructureBoxSU2[A_,B_, C_] :=
    TemplateBox[{A,B, C}, "StructureConstantSU2",
        DisplayFunction ->(SuperscriptBox["\[Epsilon]",RowBox[{#1,#2,#3}]]&),
        InterpretationFunction -> (RowBox[{"StructureConstantSU2","[",RowBox[{#1 ",",#2,",",#3}],"]"}]&)]
StructureConstantSU2 /: MakeBoxes[StructureConstantSU2[A_,B_, C_], StandardForm | TraditionalForm] := StructureBoxSU2[ToBoxes[A],ToBoxes[B], ToBoxes[C]]


(* ::Subsubsection::Closed:: *)
(*Delta (adjoint)*)


DeltaBoxSU2[A_,B_] :=
    TemplateBox[{A,B}, "DeltaSU2",
        DisplayFunction ->(SuperscriptBox["\[Delta]",RowBox[{#1,#2}]]&),
        InterpretationFunction -> (RowBox[{"DeltaSU2","[",RowBox[{#1,",",#2}],"]"}]&)]
DeltaSU2 /: MakeBoxes[DeltaSU2[A_,B_], StandardForm | TraditionalForm] := DeltaBoxSU2[ToBoxes[A],ToBoxes[B]]


(* ::Subsubsection:: *)
(*Symmetry properties of building blocks*)


EpsilonSU2[a_,b_] /;  \[Not]OrderedQ[{a,b}] := -EpsilonSU2[b,a];
EpsilonSU2[a_,b_] /;  (a==b) := 0;
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


(* ::Subsubsection:: *)
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
		
		localexp=ReLabel[exp,dummies,Table[n+i-1,{i,1,Length[dummies]}]];
		
		Return[localexp];
	]


(* ::Subsubsection::Closed:: *)
(*Contract indices in the fundamental*)


ContractSU2[exp_]:= (*dummylabel is needed because I don't want the labels to mix with actual fields in the form factor, which will be symmetrised*)
	Module[
		{localexp=exp,raiseindices={},normalisationtau={},decompositiongenerators={},deltafund={},deltaadj={},dummies=1},
		
		raiseindices=
			{
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(b==d):>TauSU2[A,c][a],
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(a==d):>TauSU2[A,c][b],
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(b==c):>-TauSU2[A,d][a],
			TauSU2[A_][a_,b_]EpsilonSU2[c_,d_]/;(a==c):>-TauSU2[A,d][b],
			
			TauSU2[A_,a_][b_]EpsilonSU2[c_,d_]/;(b==d):>TauSU2[A,a,c],
			TauSU2[A_,a_][b_]EpsilonSU2[c_,d_]/;(b==c):>-TauSU2[A,a,d]
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

			EpsilonSU2[a_][b_]EpsilonSU2[c_][d_]/;(b==c):>EpsilonSU2[a][d]
			};

		decompositiongenerators=
			{
			TauSU2[A_,a_][b_]TauSU2[B_,c_][d_]/;(b==c) :>I/2* StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],a][d]+1/4*DeltaSU2[A,B]EpsilonSU2[a][d],
			TauSU2[A_,a_,b_]TauSU2[B_][c_,d_] /;(b==d) :> -I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],a][c]-1/4*DeltaSU2[A,B]EpsilonSU2[a][c],
			TauSU2[A_,a_,b_]TauSU2[B_,c_][d_] /;(b==d) :>1/4*DeltaSU2[A,B]EpsilonSU2[a,c]-I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],a,c],
			TauSU2[A_,a_,b_]TauSU2[B_,c_][d_] /;(a==d) :>1/4*DeltaSU2[A,B]EpsilonSU2[b,c]-I/2*StructureConstantSU2[A,B,XLabel[dummies]]TauSU2[XLabel[dummies++],b,c]
			};

		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,Join[raiseindices,deltafund,decompositiongenerators]]]&,
				localexp
			];
			
		deltaadj=
			{

			StructureConstantSU2[A_,B_,C_]DeltaSU2[D_,EE_] /; (C==EE):> StructureConstantSU2[A,B,D],

			DeltaSU2[A_,C_]DeltaSU2[B_,D_]/;(C==D):> DeltaSU2[A,B],

			Power[DeltaSU2[A_,C_],2]:>3
			};
			
		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,deltaadj]]&,
				localexp
			];
		
		Return[localexp];
]


(* ::Subsubsection:: *)
(*Jacobi identities*)


JacobiSU2[exp_]:=
	Module[{localexp=exp,jacobi},

		jacobi=
			(
			StructureConstantSU2[A_,D_,E_]StructureConstantSU2[B_,C_,F_]/;(E==F)&&OrderedQ[{A,B,C,D}]:>StructureConstantSU2[A,C,E]StructureConstantSU2[B,D,E]-StructureConstantSU2[A,B,E]StructureConstantSU2[C,D,E]
			);

		localexp=
			FixedPoint[
				Expand[ReplaceRepeated[#,jacobi]]&,
				localexp
			];

		Return[localexp];

	]


(* ::Subsubsection:: *)
(*Independent adjoint structures*)


(* ::Text:: *)
(*Todo!!!*)


(*StructureConstantSU2[A_,C_,EE_]StructureConstantSU2[B_,D_,F_]/;(EE\[Equal]F)\[RuleDelayed]-DeltaSU2[A,D]*DeltaSU2[B,C]+DeltaSU2[A,B]*DeltaSU2[C,D],*)
(*StructureConstantSU2[A_,B_,C_]StructureConstantSU2[D_,EE_,F_] \[RuleDelayed] -(DeltaSU2[A,F]*DeltaSU2[B,EE]*DeltaSU2[C,D])+DeltaSU2[A,EE]*DeltaSU2[B,F]*DeltaSU2[C,D]+DeltaSU2[A,F]*DeltaSU2[B,D]*DeltaSU2[C,EE]-DeltaSU2[A,D]*DeltaSU2[B,F]*DeltaSU2[C,EE]-DeltaSU2[A,EE]*DeltaSU2[B,D]*DeltaSU2[C,F]+DeltaSU2[A,D]*DeltaSU2[B,EE]*DeltaSU2[C,F],*)


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

		localpointslines=Sort[pointslines,#1[[2]]<=#2[[2]]&]; (*fundamental first!*)

		lines=Table[localpointslines[[i,2]],{i,1,numberpoints}];
		labels=Table[localpointslines[[i,1]],{i,1,numberpoints}];

		numberfundlabels=Count[lines,1];

		admatrices=Map[PadLeft[#,numberpoints]&,Append[#,{}]&/@AllGraphs[lines],{2}];
		
		admatrices=IsGraphNonIntesercting/@admatrices;
		
		structures=FromMatricesToEpsilons[#,labels,numberpoints,numberfundlabels]&/@admatrices;
		
		Return[structures];
]


(* ::Subsection:: *)
(*Generation of the linear relations between invariant tensors*)


(* ::Text:: *)
(*(*The relations generated by this function do not distinguish between x_i and y_i indices. Then they also make sense once they are contracted with the generators of the group. *)
(*TODO: implement the contraction in the functions above.*)*)


(* ::Subsubsection::Closed:: *)
(*Schouten = loosen crossings*)


(*This function loosen ONE of the crossings in the graphs.*)


SchoutenCrossing[adjacencymatrix_List]:=
	Module[{matrixdim=Length[adjacencymatrix],positions={},matrix1,matrix2},
		Do[
			If[
				adjacencymatrix[[i,j]]!=0,
				If[
					adjacencymatrix[[k,l]]!=0,
					positions={i,k,j,l};
					Break[];
				]
			],
			{i,1,matrixdim},
			{j,i+2,matrixdim-1},
			{k,i+1,j-1},
			{l,j+1,matrixdim}
		];
		
		If[
			positions!={},
			
			matrix1=adjacencymatrix;
			matrix1[[positions[[1]],positions[[3]]]]+=-1;
			matrix1[[positions[[2]],positions[[4]]]]+=-1;
			matrix2=matrix1;
			matrix1[[positions[[1]],positions[[2]]]]++;
			matrix1[[positions[[3]],positions[[4]]]]++;
			matrix2[[positions[[1]],positions[[4]]]]++;
			matrix2[[positions[[2]],positions[[3]]]]++;
			
			Return[{matrix1,matrix2}],
			
			Return[adjacencymatrix]
		];
	]


(*Instead of untie recursively all the crossings we can choose to untie the first one for all the graphs (this gives an loosening rule) and then substitute recursively. Slower (about x10): count the intersections as Sum[adjacencymatrix[[k,l]]] / use the IsGraphNonIntersecting, and apply recursively the SchoutenCrossing.*)


(* ::Subsubsection::Closed:: *)
(*Generation of the su(2) linear relations*)


LinearRelationsSU2[pointslines_List]:=
	Module[{localpointslines,numberfundlabels=0,lines,labels,numberpoints=Length[pointslines],intersecting,numberinter,nonintersecting,numbernoninter,replacements,graphlabels,generators,x,y},

		localpointslines=Sort[pointslines,#1[[2]]<=#2[[2]]&]; (*fundamental first!*)

		lines=Table[localpointslines[[i,2]],{i,1,numberpoints}];
		labels=Table[localpointslines[[i,1]],{i,1,numberpoints}];

		numberfundlabels=Count[lines,1];

		intersecting=Map[PadLeft[#,numberpoints]&,Append[#,{}]&/@AllGraphs[lines],{2}];

		nonintersecting=IsGraphNonIntesercting/@intersecting;
		numbernoninter=Length[nonintersecting];

		intersecting=Complement[intersecting,nonintersecting];
		numberinter=Length[intersecting];

		graphlabels=
			Join[
				Table[
					intersecting[[i]]->x[i],
					{i,1,numberinter}
				],
				Table[
					nonintersecting[[i]]->y[i],
					{i,1,numbernoninter}
				]
			];
		
		generators=Product[TauSU2[ILabel[labels[[i]]]][xLabel[labels[[i]],1],xLabel[labels[[i]],2]],{i,numberfundlabels+1,numberpoints}];

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
				FromMatricesToEpsilons[intersecting[[i]],labels,numberpoints,numberfundlabels]->
				Expand[x[i]//.replacements]/.nonintersecting,
				{i,1,numberinter}
			]; (*placing the repeated replacements inside the list speeds the function up*)

		Return[replacements];

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
		InterpretationFunction->(RowBox[{"aLabel","[",RowBox[#],"]"}]&)]

bBox[x_]:=
	TemplateBox[{x},"bLabel",
		DisplayFunction->(SubscriptBox["b",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"bLabel","[",RowBox[#],"]"}]&)]
		
aLabel /: MakeBoxes[aLabel[x_],StandardForm|TraditionalForm] :=aBox[ToBoxes[x]]
bLabel /: MakeBoxes[bLabel[x_],StandardForm|TraditionalForm] :=bBox[ToBoxes[x]]


(* ::Subsubsection::Closed:: *)
(*Indices of the adjoint representation*)


ABox[x_]:=
	TemplateBox[{x},"ALabel",
		DisplayFunction->(SubscriptBox["A",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"ALabel","[",RowBox[#],"]"}]&)]
ALabel /: MakeBoxes[ALabel[x_],StandardForm|TraditionalForm] := ABox[ToBoxes[x]]

CBox[x_]:=
	TemplateBox[{x},"CLabel",
		DisplayFunction->(SubscriptBox["C",RowBox[{#}]]&),
		InterpretationFunction->(RowBox[{"CLabel","[",RowBox[#],"]"}]&)]
CLabel /: MakeBoxes[CLabel[x_],StandardForm|TraditionalForm] := CBox[ToBoxes[x]]


(* ::Subsubsection::Closed:: *)
(*Generators*)


TauBoxSU3[A_,a_, b_] :=
    TemplateBox[{A,a, b}, "TauSU3",
        DisplayFunction -> (SubscriptBox[SuperscriptBox["\[Tau]",RowBox[{#1,#2}]],RowBox[{#3}]]&),
        InterpretationFunction -> (RowBox[{"TauSU3","[",RowBox[{#1 ",",#2,",",#3}],"]"}]&)]
TauSU3 /: MakeBoxes[TauSU3[A_,a_, b_], StandardForm | TraditionalForm] := TauBoxSU3[ToBoxes[A],ToBoxes[a], ToBoxes[b]]


(* ::Subsubsection::Closed:: *)
(*Delta*)


DeltaBoxSU3[a_, b_] :=
    TemplateBox[{a, b}, "DeltaSU3",
        DisplayFunction -> (SubsuperscriptBox["\[Delta]",RowBox[{#2}],RowBox[{#1}]]&),
        InterpretationFunction -> (RowBox[{"DeltaSU3","[",RowBox[{#1 ",",#2}],"]"}]&)]
DeltaSU3 /: MakeBoxes[DeltaSU3[a_, b_], StandardForm | TraditionalForm] := DeltaBoxSU3[ToBoxes[a], ToBoxes[b]]


(* ::Subsubsection::Closed:: *)
(*Delta (adjoint)*)


DeltaAdjBoxSU3[A_, B_] :=
    TemplateBox[{A, B}, "DeltaAdjSU3",
        DisplayFunction -> (SuperscriptBox["\[Delta]",RowBox[{#1,#2}]]&),
        InterpretationFunction -> (RowBox[{"DeltaAdjSU3","[",RowBox[{#1 ",",#2}],"]"}]&)]
DeltaAdjSU3 /: MakeBoxes[DeltaAdjSU3[A_, B_], StandardForm | TraditionalForm] := DeltaAdjBoxSU3[ToBoxes[A], ToBoxes[B]]


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

TensorDSU3[A_,B_,C_] /;  \[Not]OrderedQ[{A,B,C}] :=TensorDSU3[Sequence@@Sort[{A,B,C}]];

DeltaAdjSU3[A_,B_] /; \[Not]OrderedQ[{A,B}] := DeltaAdjSU3[B,A];

StructureConstantSU3[A_,B_,C_] /;  (A==B)||(B==C)||(A==C) :=0;

TensorDSU3[A_,B_,C_] /;  (A==B)||(B==C)||(A==C) :=0;


(* ::Subsection:: *)
(*Contractions and dummy labels*)


(* ::Subsubsection::Closed:: *)
(*Rename dummies*)


RenameDummiesSU3[x_Plus,n_]:=Plus@@(RenameDummiesSU3[#,n]&/@(List@@x))

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
	]


(* ::Subsubsection:: *)
(*Contract indices*)


ContractSU3[exp_,dummylabel_]:= (*dummylabel is needed because I don't want the labels to mix with actual fields in the form factor, which will be symmetrised*)
	Module[
		{localexp=exp,eliminatedeltas,decompositiongenerators,(*normandsymm,*)dummies=dummylabel},
		eliminatedeltas=
			{
			TauSU3[A_,a_,b_]DeltaSU3[c_,d_]/;(b==c):>TauSU3[A,a,d],
			TauSU3[A_,a_,b_]DeltaSU3[c_,d_]/;(a==d):>TauSU3[A,c,b],
			DeltaSU3[a_,b_]DeltaSU3[c_,d_] /; (b==c):>DeltaSU3[a,d],

			TauSU3[A_,a_,b_] /; (a==b):>0,
			DeltaSU3[a_,b_] /; (a==b) :> 3,

			DeltaAdjSU3[A_,B_] /; (A==B) :> 8,

			StructureConstantSU3[A_,B_,C_]DeltaAdjSU3[D_,EE_] /; (C==EE):> StructureConstantSU3[A,B,D],

			TensorDSU3[A_,B_,C_] DeltaAdjSU3[D_,EE_]/;(C==EE):>TensorDSU3[A,B,D],

		DeltaAdjSU3[A_,C_] DeltaAdjSU3[B_,EE_]/;(C==EE):>DeltaAdjSU3[A,B]
			};
		decompositiongenerators=
			{
			TauSU3[A_,a_,b_]TauSU3[B_,c_,d_] /;(b==c)&&(a==d) :> 1/2 * DeltaAdjSU3[A,B],

			TauSU3[A_,a_,b_]TauSU3[B_,c_,d_]/; (b==c) :> I/2* StructureConstantSU3[A,B,CLabel[dummies]] TauSU3[CLabel[dummies],a,d]+1/2* TensorDSU3[A,B,CLabel[dummies]] TauSU3[CLabel[dummies++],a,d] + 1/6*DeltaAdjSU3[A,B] *DeltaSU3[a,d]
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
		localexp=RenameDummiesSU3[localexp,dummylabel];
		Return[localexp];
	]


(* ::Text:: *)
(*Todo: understand whether the "normandsymm" relations and their generalisations are needed for higher-dimension representations*)


(* ::Subsubsection:: *)
(*Jacobi identities*)


JacobiSU3[exp_]:=
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

	]


(* ::Subsubsection:: *)
(*Independent adjoint structures with four free indices*)


IndependentAdjSU3[exp_]:=
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

	]


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
PairingsToDelta[listofpairings_List]:=ToDelta/@listofpairings


(* ::Subsubsection::Closed:: *)
(*All invariants (list form)*)


AllInvariantsSU3[labelsrepresentations_List]:=
	Module[{labelsfund,labelsantif,allinvariants},
		
		labelsfund=
			TakeLabels[
				Select[labelsrepresentations,#[[2]]>=0&]
			];
		labelsantif=
			Permutations[
				TakeLabels[
				Select[labelsrepresentations,#[[2]]<=0&]
				]
			];
			
		If[
			\[Not](Length[labelsantif]==Length[labelsfund]),
			allinvariants=
				Transpose/@
				Tuples[{{labelsfund},labelsantif}];
			allinvariants=
				If[MemberQ[#,x_/;(x[[1]]==x[[2]])],Nothing,#]&/@allinvariants,
			Print["No invariants, man!"]
		]
	]


(* ::Subsubsection::Closed:: *)
(*All invariant (representation with deltas)*)


AllInvariantDeltas[labelsrepresentations_List]:=
Times@@@PairingsToDelta/@AllInvariantsSU3[labelsrepresentations]


(* ::Subsection::Closed:: *)
(*Simplifying the invariant tensors (both SU(2) and SU(3))*)


SimplifyInvariants[list_List]:=
	Module[{localinv=Sort[list],number=Length[list]},
		Do[
			If[
				Head[localinv[[i]]]===Plus, (*TrueQ, which gives true only if the expression evaluates to true. Gives false in any other case.*)
				localinv[[i]]=
				If[
					NumberQ[localinv[[i,1,1]]],
					Delete[localinv[[i,1]],1],
					localinv[[i,1]]
				],
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


(* ::Text:: *)
(**)


(* ::Subsection:: *)
(*Relations between the SU(3) invariants up to dimension 11 SMEFT operators (up to dimension 9 for the moment)*)


AllIdentitiesSU3[labelsfund_List,labelsantif_List]:=
	Module[{labelsadj=Intersection[labelsfund,labelsantif],dummies=Max[Join[labelsfund,labelsantif]]+1,nA,nF=Length[Complement[labelsfund,labelsantif]],delta,identities}, (*Maybe the intersection/complement step can be eliminated, but I left it for now, because we are not interested in simple cases so far.*)
		nA=Length[labelsadj];
		delta=
			Times@@
				ToDelta/@
					Transpose[{labelsfund,labelsantif}];
		If[nA+nF<4,Print["No identities, man!"]];
		If[
			nA+nF==4,
			identities=4!*AdjConstraint[
				Symmetrise[delta,bLabel/@labelsantif,"AntiSymmetric"->True]
				]//Expand;
			identities=Product[TauSU3[ALabel[i],bLabel[i],aLabel[i]],{i,labelsadj}]*identities;
			identities=IndependentAdjSU3[ContractSU3[identities,dummies]];
			Return[identities];
		];
		If[
			nA+nF>5,
			Print["Wait! Not so fast, man!"]
		];
	]


(* ::Text:: *)
(*Todo: generalise the function above to higher-dimensional representations*)


End[]


(* ::Text:: *)
(**)


(* ::Section:: *)
(*Attributes*)


SetAttributes[
    {iBox,
	iLabel,
	xBox,
	xLabel,
	IBox,
	ILabel,
	XBox,
	XLabel,
	EpsilonBoxSU2,
	EpsilonSU2,
	TauBoxSU2,
	TauSU2,
	StructureBoxSU2,
	StructureConstantSU2,
	DeltaBoxSU2,
	DeltaSU2,
	RenameDummiesSU2,
	ContractSU2,
	JacobiSU2,
	FromMatricesToEpsilons,
	FromStructuresToEpsilonSU2,
	SchoutenCrossing,
	LinearRelationsSU2,
	aBox,
	aLabel,
	bBox,
	bLabel,
	ABox,
	ALabel,
	CBox,
	CLabel,
	TauBoxSU3,
	TauSU3,
	DeltaBoxSU3,
	DeltaSU3,
	DeltaAdjBoxSU3,
	DeltaAdjSU3,
	StructureBoxSU3,
	StructureConstantSU3,
	TensorDBoxSU3,
	TensorDSU3,
	RenameDummiesSU3,
	ContractSU3,
	JacobiSU3,
	IndependentAdjSU3,
	TakeLabels,
	ToDelta,
	PairingsToDelta,
	AdjConstraint,
	AllInvariantsSU3,
	AllInvariantDeltas,
	SimplifyInvariants,
	AllIdentitiesSU3
	},
    Protected
]

EndPackage[]
