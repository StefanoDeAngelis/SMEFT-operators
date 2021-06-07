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

GluonsM::usage = "All the vectors with plus helicity"
GluonsP::usage = "All the vectors with minus helicity"
FermionsM::usage = "All the fermions with plus helicity"
FermionsP::usage = "All the fermions with minus helicity"
Scalars::usage = "All the scalars"
Fields::usage = "All the fields of the Standard Model"

adj::usage = "..."
sing::usage = "..."
fund::usage = "..."
afund::usage = "..."

Nf::usage = "..."

FermionQ::usage = ".."
BosonQ::usage = ".."

CombinationsOfFields::usage = "..."

GaugeSinglets::usage = "..."

AllOperators::usage = "..."


(* ::Section:: *)
(*Private*)


Begin["`Private`"]


(* ::Subsection:: *)
(*Transformation rules*)


TransformationRules={GGp->{adj,sing,0},WWp->{sing,adj,0},BBp->{sing,sing,0},GGm->{adj,sing,0},WWm->{sing,adj,0},BBm->{sing,sing,0},QQ->{fund,fund,1/6},uu->{afund,sing,-(2/3)},dd->{afund,sing,1/3},LL->{sing,fund,-(1/2)},ee->{sing,sing,1},QBar->{afund,afund,-(1/6)},uBar->{fund,sing,2/3},dBar->{fund,sing,-(1/3)},LBar->{sing,afund,1/2},eBar->{sing,sing,-1},HH->{sing,fund,1/2},HBar->{sing,afund,-(1/2)}}


(* ::Subsection:: *)
(*Fields and their helicity configuration*)


GluonsP={BBp,GGp,WWp}
GluonsM={BBm,GGm,WWm}
FermionsP={QQ,uu,dd,LL,ee}
FermionsM={QBar,uBar,dBar,LBar,eBar}
Scalars={HBar,HH}
Fields={GluonsM,GluonsP,FermionsM,FermionsP,Scalars};

Fermions=Join[FermionsP,FermionsM];
Bosons=Join[GluonsM,GluonsP,Scalars];

FermionQ[x_]:=MemberQ[Fermions,x]
BosonQ[x_]:=MemberQ[Bosons,x]


(* ::Subsection:: *)
(*Fields order*)


OrderingRule=Flatten@Fields;


(* ::Subsection::Closed:: *)
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
		fundSU2=Count[tensorstructure[[2]],fund|afund];
		charge=Total[tensorstructure[[3]]];
		If[
			((fundSU3==0&&afundSU3==0&&adjointSU3!=1)||(Mod[fundSU3-afundSU3,3]==0&&(fundSU3!=0||afundSU3!=0)))&&((fundSU2==0&&adjointSU2!=1)||(fundSU2!=0&&EvenQ[fundSU2]))&&
			charge==0, (*singlet conditions*)
			Return[fields],
			Return[Nothing];
		]
	]


(* ::Subsection::Closed:: *)
(*Combinations of fields*)


CombinationsOfFields[listNumbers_List]:=
	Module[{types=Length[listNumbers],groupingFields},
		If[
			types==5,
			groupingFields=
				Table[
					(*Sort[*) (*this order sort\[Rule]deleteduplicates\[Rule]sort is slightly faster than sort\[Rule]sort\[Rule]deleteduplicates*)
						DeleteDuplicates[
							SortBy[#,Position[OrderingRule,#]&]&/@ (*sort to recognise duplicates*)
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
				replist[[i]]==fund||replist[[i]]==afund,
				AppendTo[reps,{i,1}]
			],
			{i,1,Length[replist]}
		];
		Return[reps];
		]


(* ::Subsection::Closed:: *)
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
				ContractSU3[#(*,Length[fields]+1*)]&/@
					(Product[TauSU3[ALabel[i],bLabel[i],aLabel[i]],{i,adjointSU3}]
						AllInvariantDeltas[
							SU3singlet[singlets[[1]]]
						])
			];
		singlets[[2]]=Product[EpsilonSU2[][jLabel[i],iLabel[i]],{i,Flatten@Position[singlets[[2]],afund]}]InvariantsSU2[SU2singlet[singlets[[2]]],"Dummies"->Length[fields]];
		singlets[[2]]=ContractSU2[singlets[[2]],Length@fields+1];
		singlets[[2]]=If[(Head[#]===Times)&&MatchQ[#[[1]],-1],-#,#]&/@singlets[[2]];
		singlets=DeleteCases[#,0]&@Map[(Times@@#)&,Tuples[singlets],{1}];
		Return[singlets];
	]


(* ::Subsection::Closed:: *)
(*IdenticalParticles*)


(*Given a list of fields, IndenticalParticles return a list of list of list: {bosons,fermions} with bosons={{positions of identical bosons of type1},{positions of identical bosons of type2},...}*)
IdenticalParticles[fields_List]:=
	If[FermionQ[fields[[1]]],{#[[2]],#[[1]]},#]&@ (*if there are no vectors, we find {{fermions},{scalars}} and then we have to swap them*)
		(
		If[Length[#]===1,Append[#,{{}}],#]&@ (*if no bosons (or no fermions) are in the operator we have to append a list*)
			GatherBy[
				GatherBy[Range@Length[fields],fields[[#]]&],(*Gather identical particles in sublists, which contain their position*)
				BosonQ[
					fields[[#[[1]]]]
				]&(*Gather the sublists into two lists, with bosons and fermions*)
			]
		)

OrderedListPartition[list_List]:=FoldPairList[TakeDrop,list,#]&/@IntegerPartitions[Length[list]]
AllTableaux[fermionlist_List]:=Tuples[OrderedListPartition/@fermionlist]

(*Block[{$ContextPath},Needs["Combinatorica`"]//Quiet]
myTableaux[{}]:={{}}
myTableaux[single_List?(Length[#]==1&)]:={{single}}
myTableaux[list_List]:=ReplaceAll[Combinatorica`Tableaux[#],Thread[Range@#->list]]&@(Length@list)
AllTableaux[fermionlists_List]:=Tuples[myTableaux/@fermionlists]*)

ConjugatePartition[l_List]:=Module[{i,r=Reverse[l],n=Length[l]},Table[n+1-Position[r,_?(#>=i&),Infinity,1][[1,1]],{i,l[[1]]}]](*copied from Wolfram website https://mathworld.wolfram.com/ConjugatePartition.html*)
HookContentFormula[partition_List,flavours_]:=
	If[
		partition==={},
		1,
		Product[(flavours-i+j),{j,Length@partition},{i,1,partition[[j]]}]/Product[partition[[j]]+#[[i]]+1-i-j,{j,Length@partition},{i,1,partition[[j]]}]&@ConjugatePartition[partition]
	]


(* ::Subsection:: *)
(*Final Amplitude*)


Options[FinalAmplitude]={"RenormalisableTree"->False};

FinalAmplitude[d_Integer,species_List][{fields_List,helicity_List},OptionsPattern[]]:=
	Module[{colourfactors=GaugeSinglets[fields,"RenormalisableTree"->OptionValue["RenormalisableTree"]],amplitudes,allstructures},
		
		If[colourfactors==Null,Return[Nothing]];
		
		allstructures=Times@@@Tuples[{colourfactors,helicity}];
		
		If[\[Not]DuplicateFreeQ[fields],
			Block[{bosons,fermions},
				{bosons,fermions}=IdenticalParticles[fields];
				fermions=AllTableaux[fermions];
				amplitudes=MultipleSymmetrise[#,Sequence@@bosons]&/@allstructures;
				amplitudes=Table[{(*Times@@(HookContentFormula[#,Nf]&/@Map[Length,i,{2}])*)i,MultipleYoungSymmetrise[#,(Sequence@@i)]&/@amplitudes},{i,fermions}];
(*amplitudes=Map[Flatten[#,1]&,MapAt[DeleteDuplicates,Transpose/@GatherBy[amplitudes,#[[1]]&],{All,1}],{2}]; (*this steps gather together all the structures which have the same Young diagram, but different std Young tableaux*)
amplitudes=MapAt[Times@@(HookContentFormula[#,Nf]&/@#)&,amplitudes,{All,1}];*)
				amplitudes=MapAt[DeleteCases[#,_?PossibleZeroQ]&,#,2]&/@amplitudes;
				amplitudes=MapAt[DeleteDuplicates[#,(#1===#2||#1===-#2)&]&,#,2]&/@amplitudes;
				amplitudes=DeleteCases[amplitudes,{_,{}}];
			],
			amplitudes={{(*Power[Nf,Count[fields,_?FermionQ]]*){{}},allstructures}}
		];

(*DeleteRedundant has to be here because for SU(3) not only the independent structures are generated, but all of them for the moment*)
			amplitudes=If[\[Not]MatchQ[amplitudes,{}],DeleteRedundant[{fields,{#}},d-Total@(species*{2,2,3/2,3/2,1}),allstructures]&/@amplitudes,{}];
			amplitudes=DeleteCases[amplitudes,{_,{}}];
		
		If[
			MatchQ[amplitudes,{}],
			Return[Nothing],
			Return[{fields,amplitudes}]
		]
	]


(* ::Subsection:: *)
(*Identities Between Amplitudes*)


(* ::Text:: *)
(*The SU(3) are not implemented yet! TODO!!!*)
(*TODO: avoid the Simp auxilliary function + solve the problems between Coms/Simp and SpinorAngleBracket/SpinorSquareBracket*)
(*TODO: the Simplify has to be removed if we want to go beyond dimension 8 (setting the first addend equal to minus the rest for each (local)operator recursively.*)


HelicityConfigurations[species_List]:=Thread[{Range[Total@species],Flatten@MapThread[ConstantArray,{{-1,1,-1/2,1/2,0},species}]}]

AllCoefficients[poly_,vars_]:=Coefficient[poly,#]&/@vars
LinIndependentAmplitudes[matrix_?MatrixQ]:=
	Block[{indeps={},count=0},
		Do[
			If[Length@#>count,count++;AppendTo[indeps,i]]&@
				DeleteCases[#,Table[0,Length@matrix[[1]]]]&@
					RowReduce[
						matrix[[;;i]]
					],
			{i,Length@matrix}
		];
		Return[indeps]
	]

DeleteRedundant[{fields_List,operators_List},momenta_Integer,allstructures_List]:=
	Block[{singlets,num=Length[fields],localoperators=operators,independent={},SimpSU2,SimpSU3},

		If[
			momenta>0&&fields[[-2]]===fields[[-1]],(*two necessary condition for the momentum of the n^th-particle to appear is that the number of derivatives is non zero and it is identical to the *)
			Block[{Cons},

				Cons[x_Plus]:=Plus@@(Cons/@List@@x);
				Cons[x_*a__]/;MatchQ[Head[x],EpsilonSU2|TauSU2|StructureConstantSU2|DeltaSU2|TauSU3|DeltaSU3|DeltaAdjSU3|TraceSU3|EpsilonFundSU3|EpsilonAFundSU3]||NumberQ[x]:=x*Cons[Times[a]];
				Cons[x_]:=
						ReplaceRepeated[
							x,
							Flatten@(
								Table[
									SpinorAngleBracket[i,num]^a_. SpinorSquareBracket[j,num]^b_.:>Evaluate[(Sum[-SpinorAngleBracket[i,k]SpinorSquareBracket[j,k],{k,num-1}])^Min[a,b] SpinorAngleBracket[i,num]^Max[a-b,0] SpinorSquareBracket[j,num]^Max[b-a,0]],
									{i,num-1},{j,num-1}
								]
							)
						];

				localoperators=MapAt[Expand[Cons[#]]&,#,{2,All}]&/@localoperators
			]
		];

		localoperators=MapAt[Expand[Simp[#]]&,#,{2,All}]&/@localoperators;(*can this step be avoided?
		We could assign a value to certain combinations of brackets.
	No! We cannot a value to Times, because they are always products of spinor invariants.*)

		singlets=
			Drop[
				Transpose[
					ReplaceAll[fields,TransformationRules]
				],
				-1
			];
		
		SimpSU3[x_Plus]:=Plus@@(SimpSU3/@List@@x);
		SimpSU3[x_]/;MatchQ[Head[x],Power|SpinorAngleBracket|SpinorSquareBracket|EpsilonSU2|EpsilonSU2[]|EpsilonSU2[_]|TauSU2|TauSU2[__]|StructureConstantSU2|DeltaSU2]||NumberQ[x]:=x;
		SimpSU3[x_*a__]/;MatchQ[Head[x],Power|SpinorAngleBracket|SpinorSquareBracket|EpsilonSU2|EpsilonSU2[]|EpsilonSU2[_]|TauSU2|TauSU2[__]|StructureConstantSU2|DeltaSU2]||NumberQ[x]:=x*SimpSU3[Times[a]];
			
		Set@@@(MapAt[SimpSU3,#,{1}]&/@AllIdentitiesSU3[SMandGaugeSinglets`Private`SU3singlet[singlets[[1]]]]);
		SimpSU3[x_]:=x;
		
		localoperators=MapAt[Expand[SimpSU3[#]]&,#,{2,All}]&/@localoperators;
		
		SimpSU2[x_Plus]:=Plus@@(SimpSU2/@List@@x);
		SimpSU2[x_]/;MatchQ[Head[x],Power|SpinorAngleBracket|SpinorSquareBracket|TauSU3|DeltaSU3|DeltaAdjSU3|TraceSU3|EpsilonFundSU3|EpsilonAFundSU3]||NumberQ[x]:=x;
		SimpSU2[x_*a__]/;MatchQ[Head[x],Power|SpinorAngleBracket|SpinorSquareBracket|TauSU3|DeltaSU3|DeltaAdjSU3|TraceSU3|EpsilonFundSU3|EpsilonAFundSU3]||NumberQ[x]:=x*SimpSU2[Times[a]];
		
		Set@@@
			(MapAt[SimpSU2,#,{1}]&/@
				Rule@@@(
					If[MatchQ[#[[1,1]],-1],-#,#]&/@
						Map[
							ContractSU2[#,num]&,
							Expand@(Product[EpsilonSU2[][jLabel[i],iLabel[i]],{i,Flatten@Position[singlets[[2]],afund]}]List@@@SubstitutionsSU2[SMandGaugeSinglets`Private`SU2singlet[singlets[[2]]],"Dummies"->num]),
							{2}
						]
				)
			);
		SimpSU2[x_]:=x;
		
		localoperators=MapAt[Expand[SimpSU2[#]]&,#,{2,All}]&/@localoperators;

		localoperators=MapAt[AllCoefficients[#,allstructures]&,#,{2,All}]&/@localoperators;
		localoperators=LinIndependentAmplitudes[#[[2]]]&/@localoperators;
		localoperators=Transpose[{localoperators,operators}];
		localoperators={#[[2,1]],Part[#[[2,2]],#[[1]]]}&/@localoperators;
		
		Return[Flatten[localoperators,1]];
	]
	
IdentitiesBetweenAmplitudes[d_Integer][{species_List,fieldEops_List}]:=
		Block[{Simp,localOps=fieldEops},

			Set@@@
				MapAt[
					Simp,
					AllIdentities[d-Total[#]][Sequence@@HelicityConfigurations[#]]&@species,
					{All,1}
				];
			Simp[x_Plus]:=Plus@@(Simp/@List@@x);
			Simp[x_]/;NumberQ[x]:=x;
			Simp[x_*a__]/;MatchQ[Head[x],EpsilonSU2|EpsilonSU2[]|EpsilonSU2[_]|TauSU2|TauSU2[__]|StructureConstantSU2|DeltaSU2|TauSU3|DeltaSU3|DeltaAdjSU3|TraceSU3|EpsilonFundSU3|EpsilonAFundSU3]||NumberQ[x]:=x*Simp[Times[a]];

			localOps=FinalAmplitude[d,species]/@localOps;
			
			Return[(*{species,*)localOps(*}*)]
		]


(* ::Subsection:: *)
(*All Operators*)


AllOperators[d_]:=
	Block[{ops},
	
		ops=Transpose[IndependentFormFactors[d]];
		
		ops[[1]]=Thread[{ops[[1]],CombinationsOfFields/@ops[[1]]}]; (*ops[[1]] are the matter contents, ops[[2]] are the spinor helicity factors*)
		
		ops=Transpose[ops];
		
		ops=If[MatchQ[#[[1,2]],{}],Nothing,{#[[1,1]],Tuples[{#[[1,2]],{#[[2]]}}]}]&/@ops;
		
		ops=IdentitiesBetweenAmplitudes[d]/@ops;
		
		ops=Flatten[ops,1]
	]


End[]


(* ::Section:: *)
(*Attributes*)


Protect@@Names["SMandGaugeSinglets`*"]

EndPackage[]
