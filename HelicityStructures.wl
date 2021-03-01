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

IndependentFormFactors::usage = "..."
IndependentHelicityFactors::usage = "..."


(* ::Section:: *)
(*Classification*)


Begin["`Private`"]


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
					(EvenQ[der+#[[2,1]]])&& (*The first four conditions come from the representation theory and they check whether is possible to form a Lorentz singlet*)
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


(* ::Subsubsection::Closed:: *)
(*Number of fields*)


NumberFields[d_][{{gM_,gP_},{fM_,fP_},der_}]:=d-gM-gP-1/2*(fM+fP)-der


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


PartitionMomenta[moms_List,partition_List]:= (*Given a certain partition and a list of momenta of certain fields (e.g. helicity minus gluons), this function repeat and order the momenta according to the partition*) (*in the following function, this function will encounter some zeros, instead of a list associated to a partition. In this case it gives Nothing*)
		Flatten[
			Table[
				moms[[i]],
				{i,1,Length[partition]},
				{j,1,partition[[i]]} (*repeat the corresponding object as many times as it says the element of the partition*)
			] (*do it for all the elements of the partition*)
		]


(* ::Subsubsection::Closed:: *)
(*Momenta Selection*)


MomentaSelection[d_][{{gluonsM_,gluonsP_},{fermM_,fermP_},ders_}]:= (*generates all the independent momenta, their corresponding partitions of partitions and assign all of them to the lists of momenta*)
	Module[{scals=d-2(gluonsM+gluonsP)-3/2*(fermM+fermP)-ders,moms,partitions,numberfields},
		If[scals<0,Message[MomentaSelection::negative];Return[Null]];
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


MomentaSelection::negative="The number of scalars is negative"


(* ::Subsubsection::Closed:: *)
(*Spinor structures*)


SpinorStructure[d_Integer][{{gluonsM_Integer,gluonsP_Integer},{fermM_Integer,fermP_Integer},ders_Integer}]:= (*appends the list of momenta to both the angles and the squares bracket lists*)
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
(*Is a singlet doable?*)


(* ::Text:: *)
(*This function can be suppressed in the future to speed up the computation. The momenta and the helicity structures can be generated simply with numbers associated to each leg, as in IndependentHelicityFactors.*)


IsSingletDoable[n_][{List1_List,List2_List}]:= (*the counting of one element can never exceed half of the total number of countings*)
	Module[{test1,test2,zeros},
		(*List1 and List2 are made of repeated elements, for example {1,1,1,2,2,3,3,6}*)
		
		zeros=Map[{#,0}&,{Complement[#,List1],Complement[#,List2]}&@Range[n],{2}];
		
		test1=
			And@@
				Table[
					#1[[i]]<=#2/2 ,
					{i,1,Length[#1]}
				]&[Counts[List1],Length[List1]];

		test2=
			And@@
				Table[
					#1[[i]]<=#2/2 ,
					{i,1,Length[#1]}
				]&[Counts[List2],Length[List2]];

		If[
			test1&&test2,
			Return[Sort/@Join@@@Transpose[{{Tally[List1],Tally[List2]},zeros}]],
			Return[Nothing];
		];
	]


(* ::Section:: *)
(*Form Factors & Helicity Factors*)


(* ::Subsubsection::Closed:: *)
(*From Adjacency Matrices to Spinor Formula*)


FromMatrixToSpinors[{adjAngle_,adjSquare_},labels_List]:=
	Times@@
		(SpinorAngleBracket[labels[[#[[1,1]]]],labels[[#[[1,2]]]]]^#[[2]]&/@Transpose[{adjAngle["NonzeroPositions"],adjAngle["NonzeroValues"]}])*
	Times@@
		(SpinorSquareBracket[labels[[#[[1,1]]]],labels[[#[[1,2]]]]]^#[[2]]&/@Transpose[{adjSquare["NonzeroPositions"],adjSquare["NonzeroValues"]}])


(* ::Subsubsection::Closed:: *)
(*Momentum Conservation*)


PlanarMomentumConservation[{angles_,squares_}]:=
	Module[{nonzeroangles=angles["NonzeroPositions"],nonzerosquares=squares["NonzeroPositions"],n=Length[angles]},
		If[
			(MemberQ[nonzeroangles,{1,n-1}]&&MemberQ[nonzerosquares,{1,n-1}])||
			(MemberQ[nonzeroangles,{n-1,n}]&&MemberQ[nonzerosquares,{_,n-1}])||
			(MemberQ[nonzerosquares,{n-1,n}]&&MemberQ[nonzeroangles,{_,n-1}])||
			(MemberQ[nonzerosquares,{1,n}]&&MemberQ[nonzeroangles,{1,n-1}])||
			(MemberQ[nonzerosquares,{1,n-1}]&&MemberQ[nonzeroangles,{1,n}]),
			Return[Nothing],
			Return[{angles,squares}]
		]
	]


(* ::Subsubsection:: *)
(*From structure to Angles&Squares structures*)


HelicityStructures[{anglestructure_List,squarestructure_List}]:=
	Module[{formfactors,angles,squares},

		angles=AllNonIntersectionGraphs[Part[#,2]&/@anglestructure];
		squares=AllNonIntersectionGraphs[Part[#,2]&/@squarestructure];

		formfactors=Tuples[{angles,squares}];
		
		If[
			anglestructure[[-2,2]]+squarestructure[[-2,2]]!=0||anglestructure[[1,2]]+squarestructure[[1,2]]!=0,
			formfactors=PlanarMomentumConservation/@formfactors
		];
	
		formfactors=FromMatrixToSpinors[#,Part[#,1]&/@anglestructure]&/@formfactors;
	
		Return[formfactors];
	]


(* ::Subsection:: *)
(*Independent Form Factors*)


Options[IndependentFormFactors]={"MatterContent"->True}

IndependentFormFactors[d_Integer,OptionsPattern[]]:=
	Module[{structures},
		
		structures=IsSingletDoable[#1][#2]&@@@Thread[{NumberFields[d][#],SpinorStructure[d][#]}]&/@AmplitudesStructure[d];

		If[
			OptionValue["MatterContent"],
			structures=Tuples/@Thread[{List/@List/@Flatten/@AmplitudesScalars[d],structures}]
		];

		structures=Flatten[structures,1];
		
		If[
			OptionValue["MatterContent"],
			structures=Flatten[#,1]&@(Tuples/@(MapAt[HelicityStructures,#,2]&/@structures)),
			structures=Flatten[HelicityStructures[#]&/@structures]
		];	

		Return[structures]
	]


(* ::Subsection::Closed:: *)
(*Independent Helicity Factors*)


IndependentHelicityFactors[dim_Integer][list__?(Length[#]==2 && IntegerQ[2*#[[2]]]&)]:=
	Module[{labels=Part[#,1]&/@{list},angles,squares,structures},
	
		{angles,squares}={Abs[#]-#,Abs[#]+#}&@(Part[#,2]&/@{list});
		
		structures=Append[#,0]&/@PermutationsOfPartitions[dim-Total[angles]/2-Total[squares]/2,Length[angles]-1];
		
		structures={angles+#,squares+#}&/@structures;
		
		structures=If[Length[#]<2,Nothing,#]&/@Map[IsLoopLessDoable,structures,{2}];
		
		structures=HelicityStructures/@Map[Thread[{labels,#}]&,structures,{2}];
		
		Return[Flatten@structures]
	]


(* ::Subsection:: *)
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


End[]


(* ::Section:: *)
(*Attributes*)


Protect@@Names["HelicityStructures`*"]


EndPackage[]
