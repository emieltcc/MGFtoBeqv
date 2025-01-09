(* ::Package:: *)

(* ::Title:: *)
(*MGFtoBeqv*)


(* ::Section:: *)
(*Print out*)


MGFtoBeqv$Version = "1.0";


Print["(****** MGFtoBeqv ", MGFtoBeqv$Version, " ******)"];
Print["    Authors: Emiel Claasen, Mehregan Doroudiani"];
Print["    Email: emiel.claasen@aei.mpg.de"];
Print["    The MGFtoBeqv package facilitates the conversion of modular graph forms in their lattice-sum representation to their modular iterated integral representation."]
Print["(**************************)"];


Block[{Print},BeginPackage["MGFtoBeqv`",{"ModularGraphForms`"}];]


MGFtoBeqv::usage= "Expects a linear combination of modular graph forms c[] and converts it to modular iterated integrals. Works up to total graph weight 12.";
FindPrimitive::usage="Expects a linear combination of betaeqv[{},{}] and finds its primitive.";
PiNablaBeqv::usage="Expects a linear combination of betaeqv[{},{}] and computes the action of \!\(\*TemplateBox[<|\"boxes\" -> FormBox[RowBox[{\"\[Pi]\", \"\[Del]\"}], TraditionalForm], \"errors\" -> {}, \"input\" -> \"\\\\pi\\\\nabla\", \"state\" -> \"Boxes\"|>,\"TeXAssistantTemplate\"]\) on it.";
ConvertBasis::usage="Expects holomorphic graph weight as first entry and antiholomorphic graph weight as second. It returns the basis in terms of betaeqv[{},{}]. Works up to total graph weight 12.";
CstBetaeqv::usage="Expects a linear combination of betaeqv[{},{}] and finds the constant in its Laurent polynomial.";
CstMGF::usage="Expects a linear combination of MGFs and finds the constant in its Laurent polynomial in the c+[] convention.";
betaeqv::usage="Represents modular iterated integrals of holomorphic Eisenstein series and takes arguments betaeqv[{j1,...,jl},{k1,...,kl}].";


(* ::Section:: *)
(*Algorithm*)


Begin["`Private`"];


$BeqvPath = {NotebookDirectory[]};
Block[{$Path = $BeqvPath},
	depth1construle={const[{a_},{b_}]->0};
	(*Up to degree 14*)
    depth2construle=Get["betaeqvdepth2const.txt"];
    depth3construle=Get["betaeqvdepth3const.txt"];
];


ModularGraphForms::NoDiIdsFile="Dihedral identity file could not be found at `1`";
ModularGraphForms::NoTriIdsFile="Trihedral identity file could not be found at `1`";
MGFtoBeqv::NoD2BetaeqvConstFile="Depth 2 betaeqv constants file could not be found at `1`";
MGFtoBeqv::NoD3BetaeqvConstFile="Depth 3 betaeqv constants file could not be found at `1`";
packageDir=If[$InputFileName=="",NotebookDirectory[],DirectoryName[$InputFileName]];
If[FileExistsQ[packageDir<>"DiIds.txt"],
Print["Dihedral identity file found at "<>packageDir<>"DiIds.txt"];,
Message[ModularGraphForms::NoDiIdsFile,packageDir<>"DiIds.txt"];]
If[FileExistsQ[packageDir<>"TriIds.txt"],
Print["Trihedral identity file found at "<>packageDir<>"TriIds.txt"];,
Message[ModularGraphForms::NoTriIdsFile,packageDir<>"TriIds.txt"];]
If[FileExistsQ[packageDir<>"betaeqvdepth2const.txt"],
Print["Depth 2 betaeqv constants found at "<>packageDir<>"betaeqvdepth2const.txt"];,
Message[MGFtoBeqv::NoD2BetaeqvConstFile,packageDir<>"betaeqvdepth2const.txt"];]
If[FileExistsQ[packageDir<>"betaeqvdepth3const.txt"],
Print["Depth 3 betaeqv constants found at "<>packageDir<>"betaeqvdepth3const.txt"];,
Message[MGFtoBeqv::NoD3BetaeqvConstFile,packageDir<>"betaeqvdepth3const.txt"];]


(* ::Subsection:: *)
(*Dealing with constants*)


(* ::Text:: *)
(*The mismatch between MGFs and betaeqvs can at most be a constant, so it's important to keep track of them when we take derivatives.*)


addingaconstant::usage="Expects a linear combination of MGFs and replaces the MGF by itself plus a lambda-dependent function if the graph weights are equal.";
addingaconstant[mgfs_]:=Module[{isolatedmgfs,thetarule},
(*Make a list of all MGFs without coefficients*)
isolatedmgfs=DeleteCases[Replace[x_.*Except[0]?ExactNumberQ:>x]/@({mgfs/.Plus->List}//Flatten)/.{tau[2]->1,\[Pi]->1,zeta[a_]->1,g[b_]->1},1|\[Theta][\[Lambda]]];
(*If \[LeftBracketingBar]A|\[LongEqual]|B\[RightBracketingBar], we add a constant*)
thetarule=Table[If[CModWeight[(isolatedmgfs[[i]])/.{\[Theta][a_]->1}][[1]]==CModWeight[(isolatedmgfs[[i]])/.{\[Theta][a_]->1}][[2]],isolatedmgfs[[i]]->isolatedmgfs[[i]]+Pi^(CModWeight[(isolatedmgfs[[i]])/.{\[Theta][a_]->1}][[1]]/2+CModWeight[(isolatedmgfs[[i]])/.{\[Theta][a_]->1}][[2]]/2)/tau[2]^(CModWeight[(isolatedmgfs[[i]])/.{\[Theta][a_]->1}][[1]])Subscript[\[Theta], ToString[isolatedmgfs[[i]]]][\[Lambda]],##&[]],{i,Length[isolatedmgfs]}];
mgfs/.thetarule//Expand]

zetarule={zeta[x_]:>zeta[x]\[Theta][\[Lambda]],zeta[x_]^a_:>zeta[x]^a \[Theta][\[Lambda]]};
doublethetarule={\[Theta][x_] Derivative[1][\[Theta]][x_]->Derivative[1][\[Theta]][x],\[Theta][x_] (\[Theta]^\[Prime]\[Prime])[x_]->(\[Theta]^\[Prime]\[Prime])[x],\[Theta][x_] \!\(\*SuperscriptBox[\(\[Theta]\), 
TagBox[
RowBox[{"(", "y_", ")"}],
Derivative],
MultilineFunction->None]\)[x_]->\!\(\*SuperscriptBox[\(\[Theta]\), 
TagBox[
RowBox[{"(", "y", ")"}],
Derivative],
MultilineFunction->None]\)[x],\[Theta][x_]^y_:>\[Theta][x],\[Theta][x_] Subscript[\[Theta], y_][x_]->Subscript[\[Theta], y][x],\[Theta][x_] Derivative[1][Subscript[\[Theta], y_]][x_]->Derivative[1][Subscript[\[Theta], y]][x],\[Theta][x_] (Subscript[\[Theta], y_]^\[Prime]\[Prime])[x_]->(Subscript[\[Theta], y]^\[Prime]\[Prime])[x],\[Theta][x_] \!\(\*SuperscriptBox[
SubscriptBox[\(\[Theta]\), \(y_\)], 
TagBox[
RowBox[{"(", "z_", ")"}],
Derivative],
MultilineFunction->None]\)[x_]->\!\(\*SuperscriptBox[
SubscriptBox[\(\[Theta]\), \(y\)], 
TagBox[
RowBox[{"(", "z", ")"}],
Derivative],
MultilineFunction->None]\)[x]};


(* ::Subsection:: *)
(*Differential operator and separation*)


derivative::usage="Expects a linear combination of MGFs and auxiliairy functions of lambda and takes its holomorphic derivative.";
derivative[mgfs_]:=Module[{mgfslist},
mgfslist=Flatten[{mgfs/.Plus->List}];
(*Go through all terms one by one. If a term is a \[Lambda]-dependent "constant" we take a \[Lambda] derivative, otherwise we act with \[Pi]\[Del]*)
Total[Table[If[CHolCR[mgfslist[[i]]]===0,\!\(
\*SubscriptBox[\(\[PartialD]\), \(\[Lambda]\)]\(mgfslist[\([i]\)]\)\),addingaconstant[tau[2]Pi CHolCR[mgfslist[[i]]]//CSimplify]],{i,Length[mgfslist]}]]]

separate::usage="Expects a linear combination of MGFs and returns a nested list with separations based on appearances of hol. Eisenstein series.";
separate[mgfs_]:=Module[{mgfslist,positionsNoG,positionsG,posG,separatedList,splittedGs,flattenedlist,regroupedlist},
mgfslist={mgfs/.Plus->List}//Flatten;
(*We find the positions in the list of the terms with and without Eisenstein series*)
posG=Table[If[Length[Cases[Variables[mgfslist[[i]]],g[_]]]==0,noG,G],{i,Length[mgfslist]}];
positionsNoG=Position[posG,noG];
positionsG=Position[posG,G];
(*We separate these terms of different type in a list and separate the terms with Gs again by splitting the G from the coefficient.*)
separatedList={{Total[Extract[mgfslist,positionsNoG]]},{Extract[mgfslist,positionsG]}};
splittedGs=Table[({Coefficient[#,Cases[Variables[#],_g]],Cases[Variables[#],_g]}//Flatten)&/@separatedList[[2,i]],{i,Length[separatedList[[2]]]}];
(*We restructure the list, where we group MGFs by the G they multiplied. In case of MGFs multiplying no G, we write "1" instead of a Subscript[G, k]*)
flattenedlist=Flatten[{{separatedList[[1]],1},If[Length[splittedGs[[1]]]==0,{0,0},splittedGs[[1]]]}];regroupedlist=Table[{flattenedlist[[i]],flattenedlist[[i+1]]},{i,1,Length[flattenedlist]-1,2}]]


(* ::Subsection::Closed:: *)
(*Constructing the trees*)


(* ::Text:: *)
(*Construct the tree as a nested list separately for all possible levels of the tree up to 11.*)


initialization::usage="Expects a linear combination of MGFs and returns a nested list with those MGFs suitable to apply the next steps of the algorithm to.";
initialization[mgfs_]:={{addingaconstant[mgfs//CSimplify],1},{0,0}}/.zetarule /.doublethetarule(*Initialize the input such that it universally fits the algorithm*)

firstiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
seconditer::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
thirditer::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
fourthiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
fifthiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
sixthiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
seventhiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
eighthiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
ninthiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
tenthiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
eleventhiter::usage="Expects a linear combination of MGFs and applies the functions derivative and separate to the first elements of the deepest nested lists.";
firstiter[mgfs_]:=Module[{input},
input=initialization[mgfs];
Table[separate[derivative[input[[a,1]]]],{a,Length[input]}]/.zetarule/.doublethetarule]
seconditer[mgfs_]:=Table[separate[derivative[mgfs[[b,a,1]]]],{b,Length[mgfs]},{a,Length[mgfs[[b]]]}]/.zetarule/.doublethetarule
thirditer[mgfs_]:=Table[separate[derivative[mgfs[[x,b,a,1]]]],{x,Length[mgfs]},{b,Length[mgfs[[x]]]},{a,Length[mgfs[[x,b]]]}]/.zetarule/.doublethetarule
fourthiter[mgfs_]:=Table[separate[derivative[mgfs[[d,x,b,a,1]]]],{d,Length[mgfs]},{x,Length[mgfs[[d]]]},{b,Length[mgfs[[d,x]]]},{a,Length[mgfs[[d,x,b]]]}]/.zetarule/.doublethetarule
fifthiter[mgfs_]:=Table[separate[derivative[ mgfs[[z,d,x,b,a,1]]]],{z,Length[mgfs]},{d,Length[mgfs[[z]]]},{x,Length[mgfs[[z,d]]]},{b,Length[mgfs[[z,d,x]]]},{a,Length[mgfs[[z,d,x,b]]]}]/.zetarule/.doublethetarule
sixthiter[mgfs_]:=Table[separate[derivative[mgfs[[f,z,d,x,b,a,1]]]],{f,Length[mgfs]},{z,Length[mgfs[[f]]]},{d,Length[mgfs[[f,z]]]},{x,Length[mgfs[[f,z,d]]]},{b,Length[mgfs[[f,z,d,x]]]},{a,Length[mgfs[[f,z,d,x,b]]]}]/.zetarule/.doublethetarule
seventhiter[mgfs_]:=Table[separate[derivative[mgfs[[w,f,z,d,x,b,a,1]]]],{w,Length[mgfs]},{f,Length[mgfs[[w]]]},{z,Length[mgfs[[w,f]]]},{d,Length[mgfs[[w,f,z]]]},{x,Length[mgfs[[w,f,z,d]]]},{b,Length[mgfs[[w,f,z,d,x]]]},{a,Length[mgfs[[w,f,z,d,x,b]]]}]/.zetarule/.doublethetarule
eighthiter[mgfs_]:=Table[separate[derivative[mgfs[[h,w,f,z,d,x,b,a,1]]]],{h,Length[mgfs]},{w,Length[mgfs[[h]]]},{f,Length[mgfs[[h,w]]]},{z,Length[mgfs[[h,w,f]]]},{d,Length[mgfs[[h,w,f,z]]]},{x,Length[mgfs[[h,w,f,z,d]]]},{b,Length[mgfs[[h,w,f,z,d,x]]]},{a,Length[mgfs[[h,w,f,z,d,x,b]]]}]/.zetarule/.doublethetarule
ninthiter[mgfs_]:=Table[separate[derivative[mgfs[[i,h,w,f,z,d,x,b,a,1]]]],{i,Length[mgfs]},{h,Length[mgfs[[i]]]},{w,Length[mgfs[[i,h]]]},{f,Length[mgfs[[i,h,w]]]},{z,Length[mgfs[[i,h,w,f]]]},{d,Length[mgfs[[i,h,w,f,z]]]},{x,Length[mgfs[[i,h,w,f,z,d]]]},{b,Length[mgfs[[i,h,w,f,z,d,x]]]},{a,Length[mgfs[[i,h,w,f,z,d,x,b]]]}]/.zetarule/.doublethetarule
tenthiter[mgfs_]:=Table[separate[derivative[mgfs[[j,i,h,w,f,z,d,x,b,a,1]]]],{j,Length[mgfs]},{i,Length[mgfs[[j]]]},{h,Length[mgfs[[j,i]]]},{w,Length[mgfs[[j,i,h]]]},{f,Length[mgfs[[j,i,h,w]]]},{z,Length[mgfs[[j,i,h,w,f]]]},{d,Length[mgfs[[j,i,h,w,f,z]]]},{x,Length[mgfs[[j,i,h,w,f,z,d]]]},{b,Length[mgfs[[j,i,h,w,f,z,d,x]]]},{a,Length[mgfs[[j,i,h,w,f,z,d,x,b]]]}]/.zetarule/.doublethetarule
eleventhiter[mgfs_]:=Table[separate[derivative[mgfs[[k,j,i,h,w,f,z,d,x,b,a,1]]]],{k,Length[mgfs]},{j,Length[mgfs[[k]]]},{i,Length[mgfs[[k,j]]]},{h,Length[mgfs[[k,j,i]]]},{w,Length[mgfs[[k,j,i,h]]]},{f,Length[mgfs[[k,j,i,h,w]]]},{z,Length[mgfs[[k,j,i,h,w,f]]]},{d,Length[mgfs[[k,j,i,h,w,f,z]]]},{x,Length[mgfs[[k,j,i,h,w,f,z,d]]]},{b,Length[mgfs[[k,j,i,h,w,f,z,d,x]]]},{a,Length[mgfs[[k,j,i,h,w,f,z,d,x,b]]]}]/.zetarule/.doublethetarule

level1::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate once.";
level2::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate twice.";
level3::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate three times.";
level4::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate four times.";
level5::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate five times.";
level6::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate six times.";
level7::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate seven times.";
level8::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate eight times.";
level9::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate nine times.";
level10::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate ten times.";
level11::usage="Expects a linear combination of MGFs and returns a nested list where we have applied derivative and separate eleven times.";
level1[mgfs_]:=firstiter[mgfs];
level2[mgfs_]:=seconditer[firstiter[mgfs]];
level3[mgfs_]:=thirditer[seconditer[firstiter[mgfs]]];
level4[mgfs_]:=fourthiter[thirditer[seconditer[firstiter[mgfs]]]];
level5[mgfs_]:=fifthiter[fourthiter[thirditer[seconditer[firstiter[mgfs]]]]];
level6[mgfs_]:=sixthiter[fifthiter[fourthiter[thirditer[seconditer[firstiter[mgfs]]]]]];
level7[mgfs_]:=seventhiter[sixthiter[fifthiter[fourthiter[thirditer[seconditer[firstiter[mgfs]]]]]]];
level8[mgfs_]:=eighthiter[seventhiter[sixthiter[fifthiter[fourthiter[thirditer[seconditer[firstiter[mgfs]]]]]]]];
level9[mgfs_]:=ninthiter[eighthiter[seventhiter[sixthiter[fifthiter[fourthiter[thirditer[seconditer[firstiter[mgfs]]]]]]]]];
level10[mgfs_]:=tenthiter[ninthiter[eighthiter[seventhiter[sixthiter[fifthiter[fourthiter[thirditer[seconditer[firstiter[mgfs]]]]]]]]]];
level11[mgfs_]:=eleventhiter[tenthiter[ninthiter[eighthiter[seventhiter[sixthiter[fifthiter[fourthiter[thirditer[seconditer[firstiter[mgfs]]]]]]]]]]];

level1MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 1.";
level2MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 2.";
level3MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 3.";
level4MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 4.";
level5MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 5.";
level6MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 6.";
level7MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 7.";
level8MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 8.";
level9MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 9.";
level10MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 10.";
level11MGFred::usage="Expects a linear combination of MGFs and returns a list of the functions levelx applied to said level 11.";
level1MGFred[mgfs_]:={level1[mgfs]}
level2MGFred[mgfs_]:={level1[mgfs],level2[mgfs]}
level3MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs]}
level4MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs]}
level5MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs],level5[mgfs]}
level6MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs],level5[mgfs],level6[mgfs]}
level7MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs],level5[mgfs],level6[mgfs],level7[mgfs]}
level8MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs],level5[mgfs],level6[mgfs],level7[mgfs],level8[mgfs]}
level9MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs],level5[mgfs],level6[mgfs],level7[mgfs],level8[mgfs],level9[mgfs]}
level10MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs],level5[mgfs],level6[mgfs],level7[mgfs],level8[mgfs],level9[mgfs],level10[mgfs]}
level11MGFred[mgfs_]:={level1[mgfs],level2[mgfs],level3[mgfs],level4[mgfs],level5[mgfs],level6[mgfs],level7[mgfs],level8[mgfs],level9[mgfs],level10[mgfs],level11[mgfs]}


(* ::Subsection:: *)
(*Finding candidates and solving the system of equations*)


(* ::Subsubsection::Closed:: *)
(*The pi nabla action*)


pinablaJTerm::usage="Expects a single betaeqv[{},{}] and takes the pi nabla action and returns only terms where the value of j changes.";
pinablaJTerm[singlebeta_]:=Module[{newbeta,js,ks},
js=singlebeta[[1]];
ks=singlebeta[[2]];
(*We add 1 to Subscript[j, i] if Subscript[j, i]<Subscript[k, i]-2*)
Table[If[js[[i]]<ks[[i]]-2,newbeta=ReplacePart[singlebeta,{1,i}->singlebeta[[1,i]]+1];-1/4 (#[[2,i]]-#[[1,i]]-1)#&@newbeta,##&[]],{i,1,Length[js]}]]

pinablaGTerm::usage="Expects a single betaeqv[{},{}] and takes the pi nabla action and returns only terms with holomorphic Eisenstein series.";
pinablaGTerm[singlebeta_]:=Module[{kLast,jLast,newbeta},
kLast=singlebeta[[2,-1]];
jLast=singlebeta[[1,-1]];
(*If the Kronecker delta is satisfied in the last term of the differential equation, we add the following term*)
If[kLast-jLast==2,newbeta=1/4 (2I tau[2])^(kLast)g[kLast]Delete[singlebeta,{{1,-1},{2,-1}}],##&[]]]

pinablaTotal::usage="Expects a single betaeqv[{},{}] and takes the pi nabla action and returns only terms where the value of j changes.";
pinablaTotal[singlebeta_]:={pinablaJTerm[singlebeta],pinablaGTerm[singlebeta]}//Flatten

PiNablaBeqv[betas_]:=Module[{betavars,rule},
betavars=Cases[Variables[betas],_betaeqv];
rule=Table[betavars[[i]]->Total[pinablaTotal[betavars[[i]]]],{i,Length[betavars]}];
betas/.rule/.betaeqv[{},{}]:>1]


(* ::Subsubsection:: *)
(*Finding all candidates*)


groupingTerms::usage="Expects a linear combination of betaeqv[{},{}] possibly with hol. Eisenstein series as coefficients and splits them into lists with and without hol. Eisenstein series.";
groupingTerms[betas_]:=Module[{betasList,betasNoGList,betasGList},
betasList={betas/.Plus->List}//Flatten;
(*Find all betas with and without Gs*)
betasNoGList=DeleteCases[betasList,_ g[_]|g[_]];
betasGList=Complement[betasList,betasNoGList];
{betasNoGList,betasGList}]

findingJCand::usage="Expects a linear combination of betaeqv[{},{}] without hol. Eisenstein series and returns candidates based on j-value.";
findingJCand[betas_]:=Module[{betasNoCoeff,betaNoGs},
betaNoGs=groupingTerms[betas][[1]];
betasNoCoeff=Cases[Variables[betaNoGs],_betaeqv];
Flatten[Table[If[betasNoCoeff[[k,1,i]]>0,ReplacePart[betasNoCoeff[[k]],{1,i}->betasNoCoeff[[k,1,i]]-1],##&[]],{k,Length[betasNoCoeff]},{i,1,Length[betasNoCoeff[[k,1]]]}]]]

findingGCand::usage="Expects a linear combination of betaeqv[{},{}] with hol. Eisenstein series and returns candidates.";
findingGCand[betas_]:=Module[{betaGs,threadedList,betasOrdered},
betaGs=groupingTerms[betas][[2]];
threadedList=Table[{Cases[Variables[betaGs[[i]]],_g],Coefficient[betaGs[[i]],Cases[Variables[betaGs[[i]]],_g]]}//Flatten,{i,Length[betaGs]}];
(*Find the \[Beta]^eqv ordered according to the threaded list*)
betasOrdered=Table[Cases[Variables[threadedList[[i]]],_betaeqv],{i,Length[threadedList]}]//Flatten;
(*Append columns at the end*)
Do[AppendTo[betasOrdered[[i,1]],threadedList[[i,1,1]]-2];AppendTo[betasOrdered[[i,2]],threadedList[[i,1,1]]],{i,1,Length[betasOrdered]}];betasOrdered]

firstCandidates::usage="Expects a linear combination of betaeqv[{},{}] possibly with hol. Eisenstein series and returns all first iteration candidates.";
firstCandidates[betas_]:=DeleteDuplicates[{findingGCand[betas],findingJCand[betas]}//Flatten]

allCandidates::usage="Expects a linear combination of betaeqv[{},{}] possibly with hol. Eisenstein series and returns all candidates.";
allCandidates[betas_]:=Module[{firstCands,newRHSbetas,rule1,rule2,betasListRHS,betasList},
betasList={betas/.Plus->List}//Flatten;
(*Remove all coefficients*)
betasListRHS=DeleteDuplicates[Flatten[Table[Replace[x_.*Except[0]?ExactNumberQ:>x]/@betasList[[i]]/.{tau[2]->1,Pi->1},{i,Length[betasList]}]]];
firstCands=firstCandidates[betas];
(*Find the \[Pi]\[Del] action on the candidates*)
newRHSbetas=DeleteDuplicates[Flatten[Table[Replace[x_.*Except[0]?ExactNumberQ:>x]/@pinablaTotal[firstCands[[i]]]/.{tau[2]->1,Pi->1},{i,Length[firstCands]}]]];
(*Keep finding new candidates until their \[Pi]\[Del] action is equal to the \[Pi]\[Del] action on their candidates*)
While[betasListRHS!=newRHSbetas,
rule1=betasListRHS:>newRHSbetas;
rule2=newRHSbetas:>DeleteDuplicates[Flatten[Table[Replace[x_.*Except[0]?ExactNumberQ:>x]/@pinablaTotal[firstCandidates[newRHSbetas][[i]]]/.{tau[2]->1,Pi->1},{i,Length[firstCandidates[newRHSbetas]]}]]];
betasListRHS=betasListRHS/.rule1;
newRHSbetas=newRHSbetas/.rule2];
firstCandidates[newRHSbetas]]


(* ::Subsubsection:: *)
(*Solving the system of equations*)


matching::usage="Expects a linear combination of betaeqv[{},{}] possibly with hol. Eisenstein series and finds the primitive";
matching[betas_]:=Module[{betasRHSOrigWCoeff,betasRHSOrigNoCoeff,cands,betasRHSNewWCoeff,betasRHSNewNoCoeff,xilist,sysOfEqns,rule},
(*Find the (\[Beta]^eqv) with and without coefficients on the RHS of the eqns.*)
betasRHSOrigWCoeff={betas/.Plus->List}//Flatten;
betasRHSOrigNoCoeff=DeleteDuplicates[Replace[x_.*Except[0]?ExactNumberQ:>x]/@betasRHSOrigWCoeff/.{tau[2]->1,Pi->1,zeta[a_]->1,Subscript[\[Theta], b_][a_]->1}];
(*Find all candidates*)
cands=allCandidates[betasRHSOrigWCoeff];
(*Define a list of coefficients multiplying the candidates*)
xilist=Table[Subscript[\[Xi], i],{i,Length[cands]}];
(*Find the new \[Beta]^eqv after \[Pi]\[Del] on all candidates, with and without coefficients*)
betasRHSNewWCoeff=Table[xilist[[i]]pinablaTotal[cands[[i]]],{i,Length[cands]}]//Flatten;
betasRHSNewNoCoeff=DeleteDuplicates[Replace[x_.*Except[0]?ExactNumberQ:>x]/@betasRHSNewWCoeff/.{Subscript[\[Xi], _]->1,tau[2]->1,Pi->1,zeta[a_]->1,Subscript[\[Theta], b_][a_]->1}];
(*Find the system of equations and solve it*)
sysOfEqns=Table[Coefficient[betas,betasRHSNewNoCoeff[[i]]]==Coefficient[Total[betasRHSNewWCoeff],betasRHSNewNoCoeff[[i]]],{i,Length[betasRHSNewNoCoeff]}];
rule=Solve[sysOfEqns,xilist];
Total[Table[xilist[[i]]cands[[i]]/.rule,{i,Length[cands]}]]]


FindPrimitive[betas_]:=Module[{betasList,posAbs,pos,splittedBetas},
betasList={betas/.Plus->List}//Flatten;
(*Find the positions of the derivatives of \[Theta] in the list*)
posAbs=Position[betasList,\!\(\*SuperscriptBox[\(\[Theta]\), 
TagBox[
RowBox[{"(", "_", ")"}],
Derivative],
MultilineFunction->None]\)[_]|\!\(\*SuperscriptBox[
SubscriptBox[\(\[Theta]\), \(_\)], 
TagBox[
RowBox[{"(", "_", ")"}],
Derivative],
MultilineFunction->None]\)[_]];
(*We only care about the list position, not the position within a term*)
pos=Table[Drop[posAbs[[i]],{2,-1}],{i,Length[posAbs]}];
(*We split terms with only betas form ones with derivatives of \[Theta]*)
splittedBetas={Total[DeleteCases[betasList,_ \!\(\*SuperscriptBox[\(\[Theta]\), 
TagBox[
RowBox[{"(", "_", ")"}],
Derivative],
MultilineFunction->None]\)[_]|_ \!\(\*SuperscriptBox[
SubscriptBox[\(\[Theta]\), \(_\)], 
TagBox[
RowBox[{"(", "_", ")"}],
Derivative],
MultilineFunction->None]\)[_]|\!\(\*SuperscriptBox[
SubscriptBox[\(\[Theta]\), \(_\)], 
TagBox[
RowBox[{"(", "_", ")"}],
Derivative],
MultilineFunction->None]\)[_]]],Total[Extract[betasList,pos]]};
(*We solve the system of equations for the input with betas and integrate with respect to \[Lambda] for the derivatives of \[Theta]*)
matching[splittedBetas[[1]]]+ Integrate[splittedBetas[[2]],\[Lambda]]]


(* ::Subsection::Closed:: *)
(*Integrating up the tree*)


(* ::Text:: *)
(*Going back up the tree involves multiplying and summing list elements for which we find the primitive. This we have to be able to do at all levels of nesting.*)


level1combination::usage="Expects a nested list of depth 2 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level2combination::usage="Expects a nested list of depth 3 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level3combination::usage="Expects a nested list of depth 4 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level4combination::usage="Expects a nested list of depth 5 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level5combination::usage="Expects a nested list of depth 6 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level6combination::usage="Expects a nested list of depth 7 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level7combination::usage="Expects a nested list of depth 8 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level8combination::usage="Expects a nested list of depth 9 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level9combination::usage="Expects a nested list of depth 10 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level10combination::usage="Expects a nested list of depth 11 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level11combination::usage="Expects a nested list of depth 12 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level12combination::usage="Expects a nested list of depth 13 and multiplies elements of deepest nesting and adds the one of the second to deepest nesting.";
level1combination[nestedlist_]:=List[Sum[Times@@Extract[nestedlist,{i}],{i,1,Length[nestedlist]}]]
level2combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{j,i}],{i,Length[nestedlist[[j]]]}],{j,Length[nestedlist]}]
level3combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{k,j,i}],{i,Length[nestedlist[[k,j]]]}],{k,Length[nestedlist]},{j,Length[nestedlist[[k]]]}]
level4combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{h,k,j,i}],{i,Length[nestedlist[[h,k,j]]]}],{h,Length[nestedlist]},{k,Length[nestedlist[[h]]]},{j,Length[nestedlist[[h,k]]]}]
level5combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{f,h,k,j,i}],{i,Length[nestedlist[[f,h,k,j]]]}],{f,Length[nestedlist]},{h,Length[nestedlist[[f]]]},{k,Length[nestedlist[[f,h]]]},{j,Length[nestedlist[[f,h,k]]]}]
level6combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{d,f,h,k,j,i}],{i,Length[nestedlist[[d,f,h,k,j]]]}],{d,Length[nestedlist]},{f,Length[nestedlist[[d]]]},{h,Length[nestedlist[[d,f]]]},{k,Length[nestedlist[[d,f,h]]]},{j,Length[nestedlist[[d,f,h,k]]]}]
level7combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{q,d,f,h,k,j,i}],{i,Length[nestedlist[[q,d,f,h,k,j]]]}],{q,Length[nestedlist]},{d,Length[nestedlist[[q]]]},{f,Length[nestedlist[[q,d]]]},{h,Length[nestedlist[[q,d,f]]]},{k,Length[nestedlist[[q,d,f,h]]]},{j,Length[nestedlist[[q,d,f,h,k]]]}]
level8combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{s,q,d,f,h,k,j,i}],{i,Length[nestedlist[[s,q,d,f,h,k,j]]]}],{s,Length[nestedlist]},{q,Length[nestedlist[[s]]]},{d,Length[nestedlist[[s,q]]]},{f,Length[nestedlist[[s,q,d]]]},{h,Length[nestedlist[[s,q,d,f]]]},{k,Length[nestedlist[[s,q,d,f,h]]]},{j,Length[nestedlist[[s,q,d,f,h,k]]]}]
level9combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{p,s,q,d,f,h,k,j,i}],{i,Length[nestedlist[[p,s,q,d,f,h,k,j]]]}],{p,Length[nestedlist]},{s,Length[nestedlist[[p]]]},{q,Length[nestedlist[[p,s]]]},{d,Length[nestedlist[[p,s,q]]]},{f,Length[nestedlist[[p,s,q,d]]]},{h,Length[nestedlist[[p,s,q,d,f]]]},{k,Length[nestedlist[[p,s,q,d,f,h]]]},{j,Length[nestedlist[[p,s,q,d,f,h,k]]]}]
level10combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{o,p,s,q,d,f,h,k,j,i}],{i,Length[nestedlist[[o,p,s,q,d,f,h,k,j]]]}],{o,Length[nestedlist]},{p,Length[nestedlist[[o]]]},{s,Length[nestedlist[[o,p]]]},{q,Length[nestedlist[[o,p,s]]]},{d,Length[nestedlist[[o,p,s,q]]]},{f,Length[nestedlist[[o,p,s,q,d]]]},{h,Length[nestedlist[[o,p,s,q,d,f]]]},{k,Length[nestedlist[[o,p,s,q,d,f,h]]]},{j,Length[nestedlist[[o,p,s,q,d,f,h,k]]]}]
level11combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{r,o,p,s,q,d,f,h,k,j,i}],{i,Length[nestedlist[[r,o,p,s,q,d,f,h,k,j]]]}],{r,Length[nestedlist]},{o,Length[nestedlist[[r]]]},{p,Length[nestedlist[[r,o]]]},{s,Length[nestedlist[[r,o,p]]]},{q,Length[nestedlist[[r,o,p,s]]]},{d,Length[nestedlist[[r,o,p,s,q]]]},{f,Length[nestedlist[[r,o,p,s,q,d]]]},{h,Length[nestedlist[[r,o,p,s,q,d,f]]]},{k,Length[nestedlist[[r,o,p,s,q,d,f,h]]]},{j,Length[nestedlist[[r,o,p,s,q,d,f,h,k]]]}]
level12combination[nestedlist_]:=Table[Sum[Times@@Extract[nestedlist,{w,r,o,p,s,q,d,f,h,k,j,i}],{i,Length[nestedlist[[w,r,o,p,s,q,d,f,h,k,j]]]}],{w,Length[nestedlist]},{r,Length[nestedlist[[w]]]},{o,Length[nestedlist[[w,r]]]},{p,Length[nestedlist[[w,r,o]]]},{s,Length[nestedlist[[w,r,o,p]]]},{q,Length[nestedlist[[w,r,o,p,s]]]},{d,Length[nestedlist[[w,r,o,p,s,q]]]},{f,Length[nestedlist[[w,r,o,p,s,q,d]]]},{h,Length[nestedlist[[w,r,o,p,s,q,d,f]]]},{k,Length[nestedlist[[w,r,o,p,s,q,d,f,h]]]},{j,Length[nestedlist[[w,r,o,p,s,q,d,f,h,k]]]}]


replacementlevel1::usage="Expects a nested list of depth 2 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list.";
replacementlevel2::usage="Expects a nested list of depth 3 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel3::usage="Expects a nested list of depth 4 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel4::usage="Expects a nested list of depth 5 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel5::usage="Expects a nested list of depth 6 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel6::usage="Expects a nested list of depth 7 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel7::usage="Expects a nested list of depth 8 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel8::usage="Expects a nested list of depth 9 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel9::usage="Expects a nested list of depth 10 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel10::usage="Expects a nested list of depth 11 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel11::usage="Expects a nested list of depth 12 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel12::usage="Expects a nested list of depth 13 and replacement list as first and second entry and replaces the first elements of the deepest nesting of the first nesting with the elements of the second list."
replacementlevel1[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{i,1}->list2[[i]]],{i,Length[list1]}];list1]
replacementlevel2[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{j,i,1}->list2[[j,i]]],{j,Length[list1]},{i,Length[list1[[j]]]}];list1]
replacementlevel3[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{k,j,i,1}->list2[[k,j,i]]],{k,Length[list1]},{j,Length[list1[[k]]]},{i,Length[list1[[k,j]]]}];list1]
replacementlevel4[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{h,k,j,i,1}->list2[[h,k,j,i]]],{h,Length[list1]},{k,Length[list1[[h]]]},{j,Length[list1[[h,k]]]},{i,Length[list1[[h,k,j]]]}];list1]
replacementlevel5[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{f,h,k,j,i,1}->list2[[f,h,k,j,i]]],{f,Length[list1]},{h,Length[list1[[f]]]},{k,Length[list1[[f,h]]]},{j,Length[list1[[f,h,k]]]},{i,Length[list1[[f,h,k,j]]]}];list1]
replacementlevel6[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{d,f,h,k,j,i,1}->list2[[d,f,h,k,j,i]]],{d,Length[list1]},{f,Length[list1[[d]]]},{h,Length[list1[[d,f]]]},{k,Length[list1[[d,f,h]]]},{j,Length[list1[[d,f,h,k]]]},{i,Length[list1[[d,f,h,k,j]]]}];list1]
replacementlevel7[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{q,d,f,h,k,j,i,1}->list2[[q,d,f,h,k,j,i]]],{q,Length[list1]},{d,Length[list1[[q]]]},{f,Length[list1[[q,d]]]},{h,Length[list1[[q,d,f]]]},{k,Length[list1[[q,d,f,h]]]},{j,Length[list1[[q,d,f,h,k]]]},{i,Length[list1[[q,d,f,h,k,j]]]}];list1]
replacementlevel8[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{s,q,d,f,h,k,j,i,1}->list2[[s,q,d,f,h,k,j,i]]],{s,Length[list1]},{q,Length[list1[[s]]]},{d,Length[list1[[s,q]]]},{f,Length[list1[[s,q,d]]]},{h,Length[list1[[s,q,d,f]]]},{k,Length[list1[[s,q,d,f,h]]]},{j,Length[list1[[s,q,d,f,h,k]]]},{i,Length[list1[[s,q,d,f,h,k,j]]]}];list1]
replacementlevel9[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{p,s,q,d,f,h,k,j,i,1}->list2[[p,s,q,d,f,h,k,j,i]]],{p,Length[list1]},{s,Length[list1[[p]]]},{q,Length[list1[[p,s]]]},{d,Length[list1[[p,s,q]]]},{f,Length[list1[[p,s,q,d]]]},{h,Length[list1[[p,s,q,d,f]]]},{k,Length[list1[[p,s,q,d,f,h]]]},{j,Length[list1[[p,s,q,d,f,h,k]]]},{i,Length[list1[[p,s,q,d,f,h,k,j]]]}];list1]
replacementlevel10[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{o,p,s,q,d,f,h,k,j,i,1}->list2[[o,p,s,q,d,f,h,k,j,i]]],{o,Length[list1]},{p,Length[list1[[o]]]},{s,Length[list1[[o,p]]]},{q,Length[list1[[o,p,s]]]},{d,Length[list1[[o,p,s,q]]]},{f,Length[list1[[o,p,s,q,d]]]},{h,Length[list1[[o,p,s,q,d,f]]]},{k,Length[list1[[o,p,s,q,d,f,h]]]},{j,Length[list1[[o,p,s,q,d,f,h,k]]]},{i,Length[list1[[o,p,s,q,d,f,h,k,j]]]}];list1]
replacementlevel11[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{r,o,p,s,q,d,f,h,k,j,i,1}->list2[[r,o,p,s,q,d,f,h,k,j,i]]],{r,Length[list1]},{o,Length[list1[[r]]]},{p,Length[list1[[r,o]]]},{s,Length[list1[[r,o,p]]]},{q,Length[list1[[r,o,p,s]]]},{d,Length[list1[[r,o,p,s,q]]]},{f,Length[list1[[r,o,p,s,q,d]]]},{h,Length[list1[[r,o,p,s,q,d,f]]]},{k,Length[list1[[r,o,p,s,q,d,f,h]]]},{j,Length[list1[[r,o,p,s,q,d,f,h,k]]]},{i,Length[list1[[r,o,p,s,q,d,f,h,k,j]]]}];list1]
replacementlevel12[c_,replacement_]:=Module[{list1,list2},
list1=c;
list2=replacement;
Do[list1=ReplacePart[list1,{w,r,o,p,s,q,d,f,h,k,j,i,1}->list2[[w,r,o,p,s,q,d,f,h,k,j,i]]],{w,Length[list1]},{r,Length[list1[[w]]]},{o,Length[list1[[w,r]]]},{p,Length[list1[[w,r,o]]]},{s,Length[list1[[w,r,o,p]]]},{q,Length[list1[[w,r,o,p,s]]]},{d,Length[list1[[w,r,o,p,s,q]]]},{f,Length[list1[[w,r,o,p,s,q,d]]]},{h,Length[list1[[w,r,o,p,s,q,d,f]]]},{k,Length[list1[[w,r,o,p,s,q,d,f,h]]]},{j,Length[list1[[w,r,o,p,s,q,d,f,h,k]]]},{i,Length[list1[[w,r,o,p,s,q,d,f,h,k,j]]]}];list1]


(* ::Subsection:: *)
(*Constants up to graph weight 12*)


eRule=e[x_]->tau[2]^x/Pi^x c[{{x,0},{x,0}}];

CstMGF[mgf_]:=Module[{holW,antiHolW,mgfP},
holW=CModWeight[mgf/.eRule/.tau[2]:>1][[1]];
antiHolW=CModWeight[mgf/.eRule/.tau[2]:>1][[2]];
(*Change conventions*)
mgfP=tau[2]^(holW)/Pi^((holW+antiHolW)/2)(mgf/.eRule/.tau[2]:>1/.Pi:>1);
CLaurentPoly[CConvertToNablaE[CSimplify[mgfP]]]/.y^a_:>y^Abs[a]/.y->0]

CstBetaeqv[input_]:=input/.betaeqv:>const/.depth1construle/.depth2construle/.depth3construle

constants={\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[2]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[3]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 1, 2}, {1, 1, 2}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[4]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 0}, {3, 0}}] c[{{3, 0}, {1, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<    2\ne[2]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 1, 3}, {1, 1, 3}}]\>"\)]\)[\[Lambda]]->-(zeta[5]/60),\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[5]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 0}, {3, 0}}] c[{{4, 0}, {2, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<a[{{0, 2, 3}, {3, 0, 2}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[2] e[3]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{2, 0}, {4, 0}}] c[{{3, 0}, {1, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<a[{{0, 1, 2, 2}, {1, 1, 0, 3}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[2]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 0}, {3, 0}}] c[{{1, 1, 3}, {1, 1, 1}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 0}, {3, 0}}] c[{{5, 0}, {3, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 0}, {3, 0}}] c[{{3, 0}, {1, 0}}] e[2]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 0}, {5, 0}}] c[{{5, 0}, {1, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 1, 2}, {1, 1, 2}}] e[2]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[2] e[4]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<    3\ne[2]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{2, 0}, {4, 0}}] c[{{4, 0}, {2, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{3, 0}, {1, 0}}] c[{{1, 1, 1}, {1, 1, 3}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{3, 0}, {1, 0}}] c[{{3, 0}, {5, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<    2\ne[3]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[3]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<e[6]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 2, 3}, {1, 2, 3}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{2, 2, 2}, {2, 2, 2}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 1, 2, 2}, {1, 1, 2, 2}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<c[{{1, 1, 4}, {1, 1, 4}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<a[{{0, 2, 4}, {5, 0, 1}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<a[{{0, 1, 2, 3}, {2, 1, 3, 0}}]\>"\)]\)[\[Lambda]]->0,\!\(\*SubscriptBox[\(\[Theta]\), \("\<a[{{0, 2, 2, 2}, {3, 0, 1, 2}}]\>"\)]\)[\[Lambda]]->0};


(* ::Subsection:: *)
(*The full construction*)


RtoLatLevel::usage="Expects a nested list and level specification as first and second entry resp. and applies the function FindPrimitive at that level.";
RtoLatLevel[list_,level_]:=Map[FindPrimitive,list,{level}]

addBeta::usage="Expects a linear combination of betaeqv[{},{}] and hol. Eisenstein series and adds empty betaeqv[{},{}] whenever a solitary G or theta is encountered..";
addBeta[betas_]:=Module[{betasList},
betasList={betas/.Plus->List}//Flatten;
(*If we encounter an Eisenstein series or constant without \[Beta]^eqv, we multiply it with an empty \[Beta]^eqv*)
Total[Table[Which[Length[Cases[betasList[[i]],_ g[_]|g[_]]]!=0&&Length[Cases[betasList[[i]],_betaeqv]]===0,betasList[[i]] betaeqv[{},{}]/.{\[Theta][a_]->1},Length[Cases[betasList[[i]],_ \[Theta][_]|\[Theta][_]|_ Subscript[\[Theta], _][_]|Subscript[\[Theta], _][_]]]!=0&&Length[Cases[betasList[[i]],_betaeqv]]===0,(betasList[[i]] betaeqv[{},{}])/.{\[Theta][a_]->1},True,betasList[[i]]],{i,Length[betasList]}]]]

level1Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 1 and returns its betaeqv expansion.";
level2Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 2 and returns its betaeqv expansion.";
level3Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 3 and returns its betaeqv expansion.";
level4Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 4 and returns its betaeqv expansion.";
level5Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 5 and returns its betaeqv expansion.";
level6Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 6 and returns its betaeqv expansion.";
level7Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 7 and returns its betaeqv expansion.";
level8Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 8 and returns its betaeqv expansion.";
level9Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 9 and returns its betaeqv expansion.";
level10Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 10 and returns its betaeqv expansion.";
level11Conversion::usage="Expects a linear combination of MGFs with antiholomorphic weight 11 and returns its betaeqv expansion.";

level1Conversion[mgf_]:=Module[{level1,level2,newlevel1,mgfRedList},
mgfRedList=level1MGFred[mgf];
level1=initialization[mgf];
level2=mgfRedList[[1]];
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[level2],{1}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level2Conversion[mgf_]:=Module[{level1,level2,level3,newlevel1,newlevel2,mgfRedList},
mgfRedList=level2MGFred[mgf];
level1=initialization[mgf];
level2=mgfRedList[[1]];
level3=mgfRedList[[2]];
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[level3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level3Conversion[mgf_]:=Module[{level1,level2,level3,level4,newlevel1,newlevel2,newlevel3,mgfredlist},
mgfredlist=level3MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[level4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level4Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,newlevel1,newlevel2,newlevel3,newlevel4,mgfredlist},
mgfredlist=level4MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[level5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level5Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,level6,newlevel1,newlevel2,newlevel3,newlevel4,newlevel5,mgfredlist},
mgfredlist=level5MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
level6=mgfredlist[[5]];
newlevel5=replacementlevel5[level5,RtoLatLevel[Map[addBeta,level6combination[level6],{5}],5]]/.constants;
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[newlevel5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level6Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,level6,level7,newlevel1,newlevel2,newlevel3,newlevel4,newlevel5,newlevel6,mgfredlist},
mgfredlist=level6MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
level6=mgfredlist[[5]];
level7=mgfredlist[[6]];
newlevel6=replacementlevel6[level6,RtoLatLevel[Map[addBeta,level7combination[level7],{6}],6]]/.constants;
newlevel5=replacementlevel5[level5,RtoLatLevel[Map[addBeta,level6combination[newlevel6],{5}],5]]/.constants;
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[newlevel5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level7Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,level6,level7,newlevel1,newlevel2,newlevel3,newlevel4,newlevel5,newlevel6,mgfredlist,level8,newlevel7},
mgfredlist=level7MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
level6=mgfredlist[[5]];
level7=mgfredlist[[6]];
level8=mgfredlist[[7]];
newlevel7=replacementlevel7[level7,RtoLatLevel[Map[addBeta,level8combination[level8],{7}],7]]/.constants;
newlevel6=replacementlevel6[level6,RtoLatLevel[Map[addBeta,level7combination[newlevel7],{6}],6]]/.constants;
newlevel5=replacementlevel5[level5,RtoLatLevel[Map[addBeta,level6combination[newlevel6],{5}],5]]/.constants;
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[newlevel5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level8Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,level6,level7,level9,newlevel1,newlevel2,newlevel3,newlevel4,newlevel5,newlevel6,mgfredlist,level8,newlevel7,newlevel8},
mgfredlist=level8MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
level6=mgfredlist[[5]];
level7=mgfredlist[[6]];
level8=mgfredlist[[7]];
level9=mgfredlist[[8]];
newlevel8=replacementlevel8[level8,RtoLatLevel[Map[addBeta,level9combination[level9],{8}],8]]/.constants;
newlevel7=replacementlevel7[level7,RtoLatLevel[Map[addBeta,level8combination[newlevel8],{7}],7]]/.constants;
newlevel6=replacementlevel6[level6,RtoLatLevel[Map[addBeta,level7combination[newlevel7],{6}],6]]/.constants;
newlevel5=replacementlevel5[level5,RtoLatLevel[Map[addBeta,level6combination[newlevel6],{5}],5]]/.constants;
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[newlevel5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level9Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,level6,level7,level8,level9,level10,newlevel1,newlevel2,newlevel3,newlevel4,newlevel5,newlevel6,newlevel7,newlevel8,newlevel9,mgfredlist},
mgfredlist=level9MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
level6=mgfredlist[[5]];
level7=mgfredlist[[6]];
level8=mgfredlist[[7]];
level9=mgfredlist[[8]];
level10=mgfredlist[[9]];
newlevel9=replacementlevel9[level9,RtoLatLevel[Map[addBeta,level10combination[level10],{9}],9]]/.constants;
newlevel8=replacementlevel8[level8,RtoLatLevel[Map[addBeta,level9combination[newlevel9],{8}],8]]/.constants;
newlevel7=replacementlevel7[level7,RtoLatLevel[Map[addBeta,level8combination[newlevel8],{7}],7]]/.constants;
newlevel6=replacementlevel6[level6,RtoLatLevel[Map[addBeta,level7combination[newlevel7],{6}],6]]/.constants;
newlevel5=replacementlevel5[level5,RtoLatLevel[Map[addBeta,level6combination[newlevel6],{5}],5]]/.constants;
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[newlevel5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level10Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,level6,level7,level8,level9,level10,level11,newlevel1,newlevel2,newlevel3,newlevel4,newlevel5,newlevel6,newlevel7,newlevel8,newlevel9,newlevel10,mgfredlist},
mgfredlist=level10MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
level6=mgfredlist[[5]];
level7=mgfredlist[[6]];
level8=mgfredlist[[7]];
level9=mgfredlist[[8]];
level10=mgfredlist[[9]];
level11=mgfredlist[[10]];
newlevel10=replacementlevel10[level10,RtoLatLevel[Map[addBeta,level11combination[level11],{10}],10]]/.constants;
newlevel9=replacementlevel9[level9,RtoLatLevel[Map[addBeta,level10combination[newlevel10],{9}],9]]/.constants;
newlevel8=replacementlevel8[level8,RtoLatLevel[Map[addBeta,level9combination[newlevel9],{8}],8]]/.constants;
newlevel7=replacementlevel7[level7,RtoLatLevel[Map[addBeta,level8combination[newlevel8],{7}],7]]/.constants;
newlevel6=replacementlevel6[level6,RtoLatLevel[Map[addBeta,level7combination[newlevel7],{6}],6]]/.constants;
newlevel5=replacementlevel5[level5,RtoLatLevel[Map[addBeta,level6combination[newlevel6],{5}],5]]/.constants;
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[newlevel5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]

level11Conversion[mgf_]:=Module[{level1,level2,level3,level4,level5,level6,level7,level8,level9,level10,level11,level12,newlevel1,newlevel2,newlevel3,newlevel4,newlevel5,newlevel6,newlevel7,newlevel8,newlevel9,newlevel10,newlevel11,mgfredlist},
mgfredlist=level11MGFred[mgf];
level1=initialization[mgf];
level2=mgfredlist[[1]];
level3=mgfredlist[[2]];
level4=mgfredlist[[3]];
level5=mgfredlist[[4]];
level6=mgfredlist[[5]];
level7=mgfredlist[[6]];
level8=mgfredlist[[7]];
level9=mgfredlist[[8]];
level10=mgfredlist[[9]];
level11=mgfredlist[[10]];
level12=mgfredlist[[11]];
newlevel11=replacementlevel11[level11,RtoLatLevel[Map[addBeta,level12combination[level12],{11}],11]]/.constants;
newlevel10=replacementlevel10[level10,RtoLatLevel[Map[addBeta,level11combination[newlevel11],{10}],10]]/.constants;
newlevel9=replacementlevel9[level9,RtoLatLevel[Map[addBeta,level10combination[newlevel10],{9}],9]]/.constants;
newlevel8=replacementlevel8[level8,RtoLatLevel[Map[addBeta,level9combination[newlevel9],{8}],8]]/.constants;
newlevel7=replacementlevel7[level7,RtoLatLevel[Map[addBeta,level8combination[newlevel8],{7}],7]]/.constants;
newlevel6=replacementlevel6[level6,RtoLatLevel[Map[addBeta,level7combination[newlevel7],{6}],6]]/.constants;
newlevel5=replacementlevel5[level5,RtoLatLevel[Map[addBeta,level6combination[newlevel6],{5}],5]]/.constants;
newlevel4=replacementlevel4[level4,RtoLatLevel[Map[addBeta,level5combination[newlevel5],{4}],4]]/.constants;
newlevel3=replacementlevel3[level3,RtoLatLevel[Map[addBeta,level4combination[newlevel4],{3}],3]]/.constants;
newlevel2=replacementlevel2[level2,RtoLatLevel[Map[addBeta,level3combination[newlevel3],{2}],2]]/.constants;
newlevel1=replacementlevel1[level1,RtoLatLevel[Map[addBeta,level2combination[newlevel2],{2}],1]]/.constants;
Expand[Total[Flatten[level1combination[newlevel1]/.{\[Theta][a_]->1}]]]/.constants]


(* ::Subsection:: *)
(*Conversion*)


MGFtoBeqv[input_]:=Module[{mgf,holW,antiHolW,mgfP},
(*Non-holomorphic Eisenstein series have modular weights (0,0), so in order to retrieve the graph weight we apply a rule sending Subscript[E, k] to c[{{k,0},{k,0}}]*)
mgf=input/.eRule;
(*Determine the graph weights*)
holW=CModWeight[mgf/.tau[2]:>1][[1]];
antiHolW=CModWeight[mgf/.tau[2]:>1][[2]];
(*Change conventions*)
mgfP=tau[2]^(holW)/Pi^((holW+antiHolW)/2)mgf;
Which[antiHolW==1,level1Conversion[mgfP],antiHolW==2,level2Conversion[mgfP],antiHolW==3,level3Conversion[mgfP],antiHolW==4,level4Conversion[mgfP],antiHolW==5,level5Conversion[mgfP],antiHolW==6,level6Conversion[mgfP],antiHolW==7,level7Conversion[mgfP],antiHolW==8,level8Conversion[mgfP],antiHolW==9,level9Conversion[mgfP],antiHolW==10,level10Conversion[mgfP],antiHolW==11,level11Conversion[mgfP]]]


ConvertBasis[a_,b_]:=Module[{basis},
basis=CBasis[a,b];
Table[basis[[i]]->MGFtoBeqv[basis[[i]]],{i,Length[basis]}]]


Print["Succesfully loaded the MGFtoBeqv package."];


End[];


EndPackage[];
Protect["MGFtoBeqv`*"];
