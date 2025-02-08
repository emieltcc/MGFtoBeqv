(* ::Package:: *)

(* ::Title:: *)
(*Tetrahedral Simplifications of MGFs*)


Block[{Print},BeginPackage["TetSimplify`",{"ModularGraphForms`"}];]


Tet::usage="Expects a linear combination of MGFs and performs tetrahedral momentum conservation and holomorphic subgraph reduction."


(* ::Section:: *)
(*Initializations*)


Begin["`Private`"];


(* ::Subsubsection::Closed:: *)
(*Inserting blocks*)


(* ::Text:: *)
(*The function Insert doesn't have the option two insert at two positions at the same time, so I wrote one.*)


insertion[block_,a_,b_]:=Module[{pre,fin},pre=Insert[block,a,{1,1}];fin=Insert[pre,b,{2,1}]]


(* ::Section:: *)
(*Momentum Conservation*)


(* ::Subsubsection::Closed:: *)
(*Block Momentum Conservation *)


(* ::Text:: *)
(*Whenever we have multiple legs between vertices in tetrahedral graphs, we have to distribute the momentum conservation also over these edges*)


blockMomCons[mgf_]:=Module[{blockpos,minusonepos,ABblock,newblocks},
blockpos=Position[mgf,-1][[1,1]];
ABblock=mgf[[blockpos]];
minusonepos=Position[ABblock,-1];
newblocks=Table[If[i!=minusonepos[[1,-1]],ReplacePart[ABblock,{{2,i}->ABblock[[2,i]]-1,Flatten[minusonepos]->0}],##&[]],{i,Length[ABblock[[2]]]}];
Total[Table[-ReplacePart[mgf,blockpos->newblocks[[i]]],{i,Length[newblocks]}]]]


(* ::Subsubsection::Closed:: *)
(*Box Momentum Conservation*)


boxMomCons[mgf_]:=Module[{blockpart,blockpos,nextblock,minusonepos,ABblock,nextABblock,newmgfs},
blockpart=blockMomCons[mgf];
blockpos=Position[mgf,-1][[1,1]];
nextblock=Mod[blockpos+1,4,1];
ABblock=mgf[[blockpos]];
nextABblock=mgf[[nextblock]];
minusonepos=Position[ABblock,-1];
newmgfs=Total[Table[ReplacePart[mgf,{{nextblock,2,i}->nextABblock[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock[[2]]]}]];
newmgfs+blockpart]


BoxMomSimp[mgfs_]:=Module[{mgfslist,min1list,rulelist},
mgfslist=Cases[Variables[mgfs],c[___]];
min1list=Table[Position[mgfslist[[i]],-1],{i,Length[mgfslist]}];
rulelist=Table[If[Length[min1list[[i]]]>0&&Length[mgfslist[[i]]]===4,mgfslist[[i]]->boxMomCons[mgfslist[[i]]],##&[]],{i,Length[min1list]}];
mgfs/.rulelist]


(* ::Text:: *)
(*Keep doing it until we've gone all the way around.*)


BMS[mgfs_]:=CSimplify[NestWhile[BoxMomSimp,mgfs,Length[Position[Cases[Variables[mgfs],c[___]],-1]]>0,4]//Expand,diHSR->False,triHSR->False]


(* ::Subsubsection::Closed:: *)
(*Kite Momentum Conservation*)


(* ::Text:: *)
(*Momentum conservation using a tri-valent edge*)


kiteMomConsT[mgf_]:=Module[{blockpart,blockpos,ABblock,nextblockspos,minusonepos,nextblock1,nextblock2,newmgfs1,newmgfs2},
blockpart=blockMomCons[mgf];
blockpos=Position[mgf,-1][[1,1]];
ABblock=mgf[[blockpos]];
minusonepos=Position[ABblock,-1];
nextblockspos=Which[blockpos===1,{3,5},blockpos===3,{1,5},blockpos===5,{1,3},blockpos===2,{4,5},blockpos===4,{2,5}];
nextblock1=mgf[[nextblockspos[[1]]]];
nextblock2=mgf[[nextblockspos[[2]]]];
newmgfs1=Total[Table[-ReplacePart[mgf,{{nextblockspos[[1]],2,i}->nextblock1[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextblock1[[2]]]}]];
newmgfs2=Total[Table[-ReplacePart[mgf,{{nextblockspos[[2]],2,i}->nextblock2[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextblock2[[2]]]}]];
newmgfs1+newmgfs2+blockpart//Expand]


(* ::Text:: *)
(*Momentum conservation using a di-valent edge*)


kiteMomConsV[mgf_]:=Module[{blockpart,blockpos,ABblock,nextblockspos,minusonepos,nextblock,newmgfs},
blockpart=blockMomCons[mgf];
blockpos=Position[mgf,-1][[1,1]];
ABblock=mgf[[blockpos]];
minusonepos=Position[ABblock,-1];
nextblockspos=Which[blockpos===1,2,blockpos===2,1,blockpos===3,4,blockpos===4,3];
nextblock=mgf[[nextblockspos]];
newmgfs=Total[Table[ReplacePart[mgf,{{nextblockspos,2,i}->nextblock[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextblock[[2]]]}]];
newmgfs+blockpart//Expand]


KiteMomSimp[mgfs_]:=Module[{mgfslist,min1list,rulelist,reduced,rulelistred,rmin1list,reducedlist},
mgfslist=Cases[Variables[mgfs],c[___]];
min1list=Table[Position[mgfslist[[i]],-1],{i,Length[mgfslist]}];
rulelist=Table[If[Length[mgfslist[[i]]]===5,If[Length[min1list[[i]]]>0&&Count[mgfslist[[i]][[5,2]],0]===0,mgfslist[[i]]->kiteMomConsT[mgfslist[[i]]],##&[]],##&[]],{i,Length[min1list]}];
reduced=mgfs/.rulelist//Expand;
reducedlist=Cases[Variables[reduced],c[___]];
rmin1list=Table[Position[reducedlist[[i]],-1],{i,Length[reducedlist]}];
rulelistred=Table[If[Length[rmin1list[[i]]]>0,reducedlist[[i]]->kiteMomConsV[reducedlist[[i]]],##&[]],{i,Length[rmin1list]}];reduced/.rulelistred]


KMS[mgfs_]:=If[Length[Position[Cases[Variables[mgfs],c[___]],-1]]>0,KiteMomSimp[mgfs],mgfs]


(* ::Subsubsection::Closed:: *)
(*Mercedes Momentum Conservation*)


MercMomCons[mgf_,vertex_]:=Module[{blockpart,blockpos,nextvertices,minusonepos,ABblock,nextABblock11,nextABblock12,newmgfs1,newmgfs2,blockassignrule,nextblocks1},
minusonepos=Position[mgf,-1];
If[minusonepos!={},
blockpos=minusonepos[[1,1]];
Which[vertex===1,MercMomCons1[mgf,blockpos],vertex===2,MercMomCons2[mgf,blockpos],vertex===3,MercMomCons3[mgf,blockpos],vertex===4,MercMomCons4[mgf,blockpos]],mgf]]


DetermineSeq[mgf_]:=Module[{blockpos},
blockpos=Position[mgf,-1][[1,1]];
Which[blockpos===1,{2,3,4,3},blockpos===2,{2,3,1,3},blockpos===3,{3,1,4,1},blockpos===4,{3,1,2,1},blockpos===5,{1,2,4,2},blockpos===6,{1,2,3,2}]]


MMS[mgfs_]:=Module[{mgfslist,min1list,rulelist,vslist,vertexlists,result1,rulelist1,mgfswcoeffs,mgfswcoeffs2,mgfslist2,rulelist2,result2,mgfswcoeffs3,mgfslist3,rulelist3,result3,mgfswcoeffs4,mgfslist4,rulelist4,result4,rest},
rest=DeleteCases[Flatten[{mgfs/.Plus:>List}],_ c[{__},{__},{__},{__},{__},{__}]|c[{__},{__},{__},{__},{__},{__}]];
mgfswcoeffs=Cases[Flatten[{mgfs/.Plus:>List}],___ c[{__},{__},{__},{__},{__},{__}]|c[{__},{__},{__},{__},{__},{__}]];
mgfslist=Cases[Variables[mgfs],c[{__},{__},{__},{__},{__},{__}]];
min1list=Table[Position[mgfslist[[i]],-1],{i,Length[mgfslist]}];
vertexlists=Table[If[Length[min1list[[i]]]>0,
vslist=DetermineSeq[mgfslist[[i]]],{}],{i,Length[mgfslist]}];
(*cycle 1*)
rulelist1=Table[If[vertexlists[[i]]!={},mgfslist[[i]]->MercMomCons[mgfslist[[i]],vertexlists[[i,1]]],##&[]],{i,Length[mgfslist]}];
result1=Table[mgfswcoeffs[[i]]/.rulelist1,{i,Length[mgfswcoeffs]}]//Expand;
(*cycle 2*)
mgfswcoeffs2=Table[Flatten[{result1[[i]]/.Plus:>List}],{i,Length[result1]}];
mgfslist2=Table[Cases[Variables[result1[[i]]],c[{__},{__},{__},{__},{__},{__}]],{i,Length[result1]}];
rulelist2=Table[If[vertexlists[[i]]!={},
mgfslist2[[i,j]]->MercMomCons[mgfslist2[[i,j]],vertexlists[[i,2]]],
{}],{i,Length[mgfslist2]},{j,Length[mgfslist2[[i]]]}]/.(z_->Null):>(z:>z)/.(z_->Null+a_):>(z:>z);
result2=Table[mgfswcoeffs2[[i,j]]/.rulelist2[[i]],{i,Length[mgfswcoeffs2]},{j,Length[mgfswcoeffs2[[i]]]}]//Expand;
(*cycle 3*)
mgfswcoeffs3=Table[Flatten[{result2[[i,j]]/.Plus:>List}],{i,Length[result2]},{j,Length[result2[[i]]]}];
mgfslist3=Table[Cases[Variables[result2[[i,j]]],c[{__},{__},{__},{__},{__},{__}]],{i,Length[result2]},{j,Length[result2[[i]]]}];
rulelist3=Table[If[vertexlists[[i]]!={},
mgfslist3[[i,j,k]]->MercMomCons[mgfslist3[[i,j,k]],vertexlists[[i,3]]],
{}],{i,Length[mgfslist3]},{j,Length[mgfslist3[[i]]]},{k,Length[mgfslist3[[i,j]]]}]/.(z_->Null):>(z:>z)/.(z_->Null+a_):>(z:>z);
result3=Table[mgfswcoeffs3[[i,j,k]]/.rulelist3[[i,j]],{i,Length[mgfswcoeffs3]},{j,Length[mgfswcoeffs3[[i]]]},{k,Length[mgfswcoeffs3[[i,j]]]}]//Expand;
(*cycle 4*)
mgfswcoeffs4=Table[Flatten[{result3[[i,j,k]]/.Plus:>List}],{i,Length[result3]},{j,Length[result3[[i]]]},{k,Length[result3[[i,j]]]}];
mgfslist4=Table[Cases[Variables[result3[[i,j,k]]],c[{__},{__},{__},{__},{__},{__}]],{i,Length[result3]},{j,Length[result3[[i]]]},{k,Length[result3[[i,j]]]}];
rulelist4=Table[If[vertexlists[[i]]!={},
mgfslist4[[i,j,k,l]]->MercMomCons[mgfslist4[[i,j,k,l]],vertexlists[[i,4]]],
{}],{i,Length[mgfslist4]},{j,Length[mgfslist4[[i]]]},{k,Length[mgfslist4[[i,j]]]},{l,Length[mgfslist4[[i,j,k]]]}]/.(z_->Null):>(z:>z)/.(z_->Null+a_):>(z:>z);
result4=Table[mgfswcoeffs4[[i,j,k,l]]/.rulelist4[[i,j,k]],{i,Length[mgfswcoeffs4]},{j,Length[mgfswcoeffs4[[i]]]},{k,Length[mgfswcoeffs4[[i,j]]]},{l,Length[mgfswcoeffs4[[i,j,k]]]}]//Expand;
Total[rest]+Total[result4,All]]


MMSI[mgfs_]:=Module[{mgfslist},mgfslist={mgfs/.Plus:>List}//Flatten;Table[MMS[mgfslist[[i]]],{i,Length[mgfslist]}]//Total]


(* ::Text:: *)
(*Vertex 1*)


MercMomCons1[mgf_,block_]:=Module[{blockpart,blockpos,newmgfs1,newmgfs2,adjacentblocks,nextABblock1,nextABblock2,minusonepos,ABblock},
blockpos=Position[mgf,-1][[1,1]];
blockpart=blockMomCons[mgf];
adjacentblocks=DeleteCases[{1,5,6},block];
ABblock=mgf[[blockpos]];
minusonepos=Position[ABblock,-1];
nextABblock1=mgf[[adjacentblocks[[1]]]];
nextABblock2=mgf[[adjacentblocks[[2]]]];
newmgfs1=Total[Table[ReplacePart[mgf,{{adjacentblocks[[1]],2,i}->nextABblock1[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock1[[2]]]}]];
newmgfs2=Total[Table[ReplacePart[mgf,{{adjacentblocks[[2]],2,i}->nextABblock2[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock2[[2]]]}]];
Which[block===1,blockpart+newmgfs1-newmgfs2,block===5,blockpart+newmgfs1+newmgfs2,block===6,blockpart-newmgfs1+newmgfs2,1===1,mgf]]


(* ::Text:: *)
(*Vertex 2*)


MercMomCons2[mgf_,block_]:=Module[{blockpart,blockpos,newmgfs1,newmgfs2,adjacentblocks,nextABblock1,nextABblock2,minusonepos,ABblock},
blockpart=blockMomCons[mgf];
blockpos=Position[mgf,-1][[1,1]];
adjacentblocks=DeleteCases[{1,2,3},block];
ABblock=mgf[[blockpos]];
minusonepos=Position[ABblock,-1];
nextABblock1=mgf[[adjacentblocks[[1]]]];
nextABblock2=mgf[[adjacentblocks[[2]]]];
newmgfs1=Total[Table[ReplacePart[mgf,{{adjacentblocks[[1]],2,i}->nextABblock1[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock1[[2]]]}]];
newmgfs2=Total[Table[ReplacePart[mgf,{{adjacentblocks[[2]],2,i}->nextABblock2[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock2[[2]]]}]];
If[block===1||block===2||block===3,blockpart-newmgfs1-newmgfs2,mgf]]


(* ::Text:: *)
(*Vertex 3*)


MercMomCons3[mgf_,block_]:=Module[{blockpart,blockpos,newmgfs1,newmgfs2,adjacentblocks,nextABblock1,nextABblock2,minusonepos,ABblock},
blockpart=blockMomCons[mgf];
blockpos=Position[mgf,-1][[1,1]];
adjacentblocks=DeleteCases[{3,4,5},block];
ABblock=mgf[[blockpos]];
minusonepos=Position[ABblock,-1];
nextABblock1=mgf[[adjacentblocks[[1]]]];
nextABblock2=mgf[[adjacentblocks[[2]]]];
newmgfs1=Total[Table[ReplacePart[mgf,{{adjacentblocks[[1]],2,i}->nextABblock1[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock1[[2]]]}]];
newmgfs2=Total[Table[ReplacePart[mgf,{{adjacentblocks[[2]],2,i}->nextABblock2[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock2[[2]]]}]];
Which[block===3,blockpart+newmgfs1-newmgfs2,block===4,blockpart+newmgfs1+newmgfs2,block===5,blockpart-newmgfs1+newmgfs2,1===1,mgf]]


(* ::Text:: *)
(*Vertex 4*)


MercMomCons4[mgf_,block_]:=Module[{blockpart,blockpos,newmgfs1,newmgfs2,adjacentblocks,nextABblock1,nextABblock2,minusonepos,ABblock},
blockpart=blockMomCons[mgf];
blockpos=Position[mgf,-1][[1,1]];
adjacentblocks=DeleteCases[{2,4,6},block];
ABblock=mgf[[blockpos]];
minusonepos=Position[ABblock,-1];
nextABblock1=mgf[[adjacentblocks[[1]]]];
nextABblock2=mgf[[adjacentblocks[[2]]]];
newmgfs1=Total[Table[ReplacePart[mgf,{{adjacentblocks[[1]],2,i}->nextABblock1[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock1[[2]]]}]];
newmgfs2=Total[Table[ReplacePart[mgf,{{adjacentblocks[[2]],2,i}->nextABblock2[[2,i]]-1,Flatten[{blockpos,minusonepos}]->0}],{i,Length[nextABblock2[[2]]]}]];
Which[block===2,blockpart-newmgfs1+newmgfs2,block===4,blockpart-newmgfs1+newmgfs2,block===6,blockpart+newmgfs1+newmgfs2,1===1,mgf]]


(* ::Section:: *)
(*Holomorphic Subgraph Reduction*)


(* ::Text:: *)
(*Everything is based on Fay identities.*)


(* ::Subsubsection::Closed:: *)
(*Parallel HSR *)


ParallelHSR[mgf_]:=Module[{apos,pos,ap,am,a0,block,zerocolumns,ABblock,blocklength,term1,ABT2p,ABT2,term2,term3,term4,term5},
pos=Total[Flatten[Position[Table[Count[mgf[[i,2]],0],{i,Length[mgf]}],2]]];
block=mgf[[pos]];
blocklength=Length[block[[1]]];
zerocolumns=Flatten[{Position[block[[2]],0]/.{x_}:>{2,x},Position[block[[2]],0]/.{x_}:>{1,x}},1];
ABblock=Delete[block,zerocolumns];
apos={zerocolumns[[-2]],zerocolumns[[-1]]};
ap=Extract[block,apos[[1]]];
am=Extract[block,apos[[2]]];
a0=ap+am;
term1=If[a0>=4,(-1)^(ap)ReplacePart[mgf,pos->(ABblock/.{{},{}}:>{})]g[a0],0];
term2=-Binomial[a0,ap]ReplacePart[mgf,pos->insertion[ABblock,a0,0]];
term3=Sum[Binomial[a0-1-k,ap-k] g[k]ReplacePart[mgf,pos->insertion[ABblock,a0-k,0]],{k,4,ap,2}];
term4=Sum[Binomial[a0-1-k,am-k] g[k]ReplacePart[mgf,pos->insertion[ABblock,a0-k,0]],{k,4,am,2}];
term5=Binomial[a0-2,ap-1](gHat[2]ReplacePart[mgf,pos->insertion[ABblock,a0-2,0]]+Pi/Subscript[\[Tau], 2] ReplacePart[mgf,pos->insertion[ABblock,a0-1,-1]]);
If[a0===2,PHSRdiv[mgf],term1+term2+term3+term4]]


PHSRdiv[mgf_]:=Module[{apos,pos,ap,am,a0,block,zerocolumns,ABblock,blocklength,term1,ABT2p,ABT2,term2,term3,term4,term5},
pos=Total[Flatten[Position[Table[Count[mgf[[i,2]],0],{i,Length[mgf]}],2]]];
block=mgf[[pos]];
blocklength=Length[block[[1]]];
zerocolumns=Flatten[{Position[block,0],Position[block,0]/.{2,x_}:>{1,x}},1];
ABblock=Delete[block,zerocolumns];
apos=Position[block,0]/.{2,x_}:>{1,x};
ap=Extract[block,apos[[1]]];
am=Extract[block,apos[[2]]];
a0=ap+am;
term1=-2ReplacePart[mgf,pos->insertion[ABblock,a0,0]];
term2=-(gHat[2](ReplacePart[mgf,pos->ABblock]/.{{},{}}:>{})-Pi/tau[2] ReplacePart[mgf,pos->insertion[ABblock,a0-1,-1]]);
term1]


PHSR[mgfs_]:=Module[{mgfslist,pos,rulelist},
mgfslist=Cases[Variables[mgfs],c[___]];
pos=Table[Total[Flatten[Position[Table[Count[mgfslist[[j,i,2]],0],{i,Length[mgfslist[[j]]]}],2]]],{j,Length[mgfslist]}];
rulelist=Table[If[pos[[i]]!=0,mgfslist[[i]]->ParallelHSR[mgfslist[[i]]],##&[]],{i,Length[pos]}];
CSimplify[mgfs/.rulelist,diHSR->False,triHSR->False]]


(* ::Subsubsection::Closed:: *)
(*Tri HSR*)


TrihHSR[mgf_]:=Module[{AB1,AB2,AB3,term1,term2,term3,term4,term5,a1,a2,col01,col02,AB1block,AB2block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
a1=Total[Extract[AB1,Position[AB1,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB2,Position[AB2,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB1,0],Position[AB1,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB2,0],Position[AB2,0]/.{2,x_}:>{1,x}},1];
AB1block=Delete[AB1,col01];
AB2block=Delete[AB2,col02];
term1=(-1)^a1 c[AB1block/.{{},{}}:>{},AB2block/.{{},{}}:>{},insertion[AB3,a1+a2,0]];
term2=-(-1)^(a1+a2)Binomial[a1+a2-1,a1]c[AB1block/.{{},{}}:>{},insertion[AB2block,a1+a2,0],AB3];
term3=- Binomial[a1+a2-1,a2]c[insertion[AB1block,a1+a2,0],AB2block/.{{},{}}:>{},AB3];
term4=(-1)^(a1+a2)Sum[ Binomial[a2+j-1,j]c[AB1block/.{{},{}}:>{},insertion[AB2block,a2+j,0],insertion[AB3,a1-j,0]],{j,0,a1-1}];
term5=Sum[ Binomial[a1+j-1,j]c[insertion[AB1block,a1+j,0],AB2block/.{{},{}}:>{},insertion[AB3,a2-j,0]],{j,0,a2-1}];
(-1)^a2( term1+ term2+ term3+ term4+ term5)]


istheretri[mgf_]:=If[Table[Count[mgf[[i,2]],0],{i,Length[mgf]}]=={1,1,1},TRI,no]


THSR[mgfs_]:=Module[{mgfslist,min1list,rulelist},
mgfslist=Cases[Variables[mgfs],c[___]];
rulelist=Table[If[istheretri[mgfslist[[i]]]===TRI,mgfslist[[i]]->TrihHSR[mgfslist[[i]]],##&[]],{i,Length[mgfslist]}];
CSimplify[mgfs/.rulelist,diHSR->False,triHSR->False]]


(* ::Subsubsection::Closed:: *)
(*Box HSR *)


istherebox[mgf_]:=If[Table[Count[mgf[[i,2]],0],{i,Length[mgf]}]=={1,1,1,1},box,no]


boxHSR[mgf_]:=Module[{AB1,AB2,AB3,AB4,term1,term2,term3,term4,term5,a1,a2,col01,col02,AB1block,AB2block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
AB4=mgf[[4]];
a1=Total[Extract[AB1,Position[AB1,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB2,Position[AB2,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB1,0],Position[AB1,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB2,0],Position[AB2,0]/.{2,x_}:>{1,x}},1];
AB1block=Delete[AB1,col01];
AB2block=Delete[AB2,col02];
term1=(-1)^(Total[AB3,All]+Total[AB4,All]) c[AB1block/.{{},{}}:>{},AB2block/.{{},{}}:>{},AB3,AB4,{{a1+a2},{0}}];
term2=-(-1)^a1 Binomial[a1+a2-1,a1]c[AB1block/.{{},{}}:>{},insertion[AB2block,a1+a2,0],AB3,AB4];
term3=-(-1)^a2 Binomial[a1+a2-1,a2]c[insertion[AB1block,a1+a2,0],AB2block/.{{},{}}:>{},AB3,AB4];
term4=(-1)^(Total[AB3,All]+Total[AB4,All])Sum[(-1)^j Binomial[a2+j-1,j]c[AB1block/.{{},{}}:>{},insertion[AB2block,a2+j,0],AB3,AB4,{{a1-j},{0}}],{j,0,a1-1}];
term5=(-1)^(Total[AB3,All]+Total[AB4,All])Sum[(-1)^j Binomial[a1+j-1,j]c[insertion[AB1block,a1+j,0],AB2block/.{{},{}}:>{},AB3,AB4,{{a2-j},{0}}],{j,0,a2-1}];
 term1+ term2+ term3+ term4+ term5]


BHSR[mgfs_]:=Module[{mgfslist,min1list,rulelist},
mgfslist=Cases[Variables[mgfs],c[___]];
rulelist=Table[If[istherebox[mgfslist[[i]]]===box,mgfslist[[i]]->boxHSR[mgfslist[[i]]],##&[]],{i,Length[mgfslist]}];
CSimplify[mgfs/.rulelist,diHSR->False,triHSR->False]]


(* ::Subsubsection::Closed:: *)
(*Kite HSR *)


istheretrikite[mgf_]:=Module[{zeros},zeros=Table[Count[mgf[[i,2]],0],{i,Length[mgf]}];If[zeros=={0,0,1,1,1}||zeros=={0,1,1,1,1}||zeros=={1,0,1,1,1},triR,If[zeros=={1,1,0,0,1}||zeros=={1,1,0,1,1}||zeros=={1,1,1,0,1},triL,no]]]


triKiteHSRL[mgf_]:=Module[{AB1,AB2,AB3,AB4,AB5,term1,term2,term3,term4,term5,a1,a2,col01,col02,AB1block,AB2block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
AB4=mgf[[4]];
AB5=mgf[[5]];
a1=Total[Extract[AB1,Position[AB1,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB2,Position[AB2,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB1,0],Position[AB1,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB2,0],Position[AB2,0]/.{2,x_}:>{1,x}},1];
AB1block=Delete[AB1,col01];
AB2block=Delete[AB2,col02];
term1=c[AB1block/.{{},{}}:>{},AB2block/.{{},{}}:>{},AB3,AB4,insertion[AB5,a1+a2,0]];
term2=-(-1)^a1 Binomial[a1+a2-1,a1]c[AB1block/.{{},{}}:>{},insertion[AB2block,a1+a2,0],AB3,AB4,AB5];
term3=-(-1)^a2 Binomial[a1+a2-1,a2]c[insertion[AB1block,a1+a2,0],AB2block/.{{},{}}:>{},AB3,AB4,AB5];
term4=Sum[(-1)^j Binomial[a2+j-1,j] c[AB1block/.{{},{}}:>{},insertion[AB2block,a2+j,0],AB3,AB4,insertion[AB5,a1-j,0]],{j,0,a1-1}];
term5=Sum[(-1)^j Binomial[a1+j-1,j] c[insertion[AB1block,a1+j,0],AB2block/.{{},{}}:>{},AB3,AB4,insertion[AB5,a2-j,0]],{j,0,a2-1}];
term1+term2+term3+term4+term5]


triKiteHSRR[mgf_]:=Module[{AB1,AB2,AB3,AB4,AB5,term1,term2,term3,term4,term5,a1,a2,col01,col02,AB3block,AB4block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
AB4=mgf[[4]];
AB5=mgf[[5]];
a1=Total[Extract[AB3,Position[AB3,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB4,Position[AB4,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB3,0],Position[AB3,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB4,0],Position[AB4,0]/.{2,x_}:>{1,x}},1];
AB3block=Delete[AB3,col01];
AB4block=Delete[AB4,col02];
term1=c[AB1,AB2,AB3block/.{{},{}}:>{},AB4block/.{{},{}}:>{},insertion[AB5,a1+a2,0]];
term2=-(-1)^a1 Binomial[a1+a2-1,a1]c[AB1,AB2,AB3block/.{{},{}}:>{},insertion[AB4block,a1+a2,0],AB5];
term3=-(-1)^a2 Binomial[a1+a2-1,a2]c[AB1,AB2,insertion[AB3block,a1+a2,0],AB4block/.{{},{}}:>{},AB5];
term4=Sum[(-1)^j Binomial[a2+j-1,j] c[AB1,AB2,AB3block/.{{},{}}:>{},insertion[AB4block,a2+j,0],insertion[AB5,a1-j,0]],{j,0,a1-1}];
term5=Sum[(-1)^j Binomial[a1+j-1,j] c[AB1,AB2,insertion[AB3block,a1+j,0],AB4block/.{{},{}}:>{},insertion[AB5,a2-j,0]],{j,0,a2-1}];
term1+term2+term3+term4+term5]


triKiteHSR[mgfs_]:=Module[{mgfslist,rulelist},
mgfslist=Cases[Variables[mgfs],c[___]];
rulelist=Table[Which[istheretrikite[mgfslist[[i]]]===triL,mgfslist[[i]]->triKiteHSRL[mgfslist[[i]]],istheretrikite[mgfslist[[i]]]===triR,mgfslist[[i]]->triKiteHSRR[mgfslist[[i]]],1===1,##&[]],{i,Length[mgfslist]}];
CSimplify[mgfs/.rulelist,diHSR->False,triHSR->False]]


isthereboxkite[mgf_]:=Module[{zeros},
zeros=Table[Count[mgf[[i,2]],0],{i,Length[mgf]}];
If[zeros=={1,1,1,1,0},boxkite,no]]


BKHSR[mgfs_]:=Module[{mgfslist,rulelist},
mgfslist=Cases[Variables[mgfs],c[___]];
rulelist=Table[If[isthereboxkite[mgfslist[[i]]]===boxkite,mgfslist[[i]]->triKiteHSRL[mgfslist[[i]]],##&[]],{i,Length[mgfslist]}];
CSimplify[mgfs/.rulelist,diHSR->False,triHSR->False]]


(* ::Subsubsection::Closed:: *)
(*Mercedes HSR*)


isthereHSMerc[mgf_]:=Module[{zeros},
zeros=Table[Count[mgf[[i,2]],0],{i,Length[mgf]}];
Which[
zeros==={1,1,0,0,0,1}||zeros==={1,1,1,0,0,1}||zeros==={1,1,0,1,0,1}||zeros==={1,1,0,0,1,1},tri126,
zeros==={0,1,1,1,0,0}||zeros==={1,1,1,1,0,0}||zeros==={0,1,1,1,1,0}||zeros==={0,1,1,1,0,1},tri234,
zeros==={1,0,1,0,1,0}||zeros==={1,1,1,0,1,0}||zeros==={1,0,1,1,1,0}||zeros==={1,0,1,0,1,1},tri135,
zeros==={0,0,0,1,1,1}||zeros==={1,0,0,1,1,1}||zeros==={0,1,0,1,1,1}||zeros==={0,0,1,1,1,1},tri456,
zeros==={1,1,0,1,1,0},box1245,
zeros==={1,0,1,1,0,1},box1346,
zeros==={0,1,1,0,1,1},box2356,
1===1,no]]


MerctriHSR126[mgf_]:=Module[{AB1,AB2,AB3,AB4,AB5,AB6,term1,term2,term3,term4,term5,a1,a2,col01,col02,a1block,a2block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
AB4=mgf[[4]];
AB5=mgf[[5]];
AB6=mgf[[6]];
a1=Total[Extract[AB6,Position[AB6,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB1,Position[AB1,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB6,0],Position[AB6,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB1,0],Position[AB1,0]/.{2,x_}:>{1,x}},1];
a1block=Delete[AB6,col01];
a2block=Delete[AB1,col02];
term1=(-1)^a1 c[a2block/.{{},{}}:>{},insertion[AB2,a1+a2,0],AB3,AB4,AB5,a1block/.{{},{}}:>{}];
term2=-Binomial[a1+a2-1,a1]c[insertion[a2block,a1+a2,0],AB2,AB3,AB4,AB5,a1block/.{{},{}}:>{}];
term3=- Binomial[a1+a2-1,a2]c[a2block/.{{},{}}:>{},AB2,AB3,AB4,AB5,insertion[a1block,a1+a2,0]];
term4=Sum[(-1)^(a1+j) Binomial[a2+j-1,j] c[insertion[a2block,a2+j,0],insertion[AB2,a1-j,0],AB3,AB4,AB5,a1block/.{{},{}}:>{}],{j,0,a1-1}];
term5=Sum[ Binomial[a1+j-1,j] c[a2block/.{{},{}}:>{},insertion[AB2,a2-j,0],AB3,AB4,AB5,insertion[a1block,a1+j,0]],{j,0,a2-1}];
term1+term2+term3+term4+term5]


MerctriHSR234[mgf_]:=Module[{AB1,AB2,AB3,AB4,AB5,AB6,term1,term2,term3,term4,term5,a1,a2,col01,col02,a1block,a2block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
AB4=mgf[[4]];
AB5=mgf[[5]];
AB6=mgf[[6]];
a1=Total[Extract[AB4,Position[AB4,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB2,Position[AB2,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB4,0],Position[AB4,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB2,0],Position[AB2,0]/.{2,x_}:>{1,x}},1];
a1block=Delete[AB4,col01];
a2block=Delete[AB2,col02];
term1=(-1)^a1 c[AB1,a2block/.{{},{}}:>{},insertion[AB3,a1+a2,0],a1block/.{{},{}}:>{},AB5,AB6];
term2=-Binomial[a1+a2-1,a1]c[AB1,insertion[a2block,a1+a2,0],AB3,a1block/.{{},{}}:>{},AB5,AB6];
term3=- Binomial[a1+a2-1,a2]c[AB1,a2block/.{{},{}}:>{},AB3,insertion[a1block,a1+a2,0],AB5,AB6];
term4=Sum[(-1)^(a1+j) Binomial[a2+j-1,j] c[AB1,insertion[a2block,a2+j,0],insertion[AB3,a1-j,0],a1block/.{{},{}}:>{},AB5,AB6],{j,0,a1-1}];
term5=Sum[ Binomial[a1+j-1,j] c[AB1,a2block/.{{},{}}:>{},insertion[AB3,a2-j,0],insertion[a1block,a1+j,0],AB5,AB6],{j,0,a2-1}];
term1+term2+term3+term4+term5]


MerctriHSR135[mgf_]:=Module[{AB1,AB2,AB3,AB4,AB5,AB6,term1,term2,term3,term4,term5,a1,a2,col01,col02,a1block,a2block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
AB4=mgf[[4]];
AB5=mgf[[5]];
AB6=mgf[[6]];
a1=Total[Extract[AB5,Position[AB5,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB3,Position[AB3,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB5,0],Position[AB5,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB3,0],Position[AB3,0]/.{2,x_}:>{1,x}},1];
a1block=Delete[AB5,col01];
a2block=Delete[AB3,col02];
term1=(-1)^a1 c[insertion[AB1,a1+a2,0],AB2,a2block/.{{},{}}:>{},AB4,a1block/.{{},{}}:>{},AB6];
term2=-Binomial[a1+a2-1,a1]c[AB1,AB2,insertion[a2block,a1+a2,0],AB4,a1block/.{{},{}}:>{},AB6];
term3=- Binomial[a1+a2-1,a2]c[AB1,AB2,a2block/.{{},{}}:>{},AB4,insertion[a1block,a1+a2,0],AB6];
term4=Sum[(-1)^(a1+j) Binomial[a2+j-1,j] c[insertion[AB1,a1-j,0],AB2,insertion[a2block,a2+j,0],AB4,a1block/.{{},{}}:>{},AB6],{j,0,a1-1}];
term5=Sum[ Binomial[a1+j-1,j] c[insertion[AB1,a2-j,0],AB2,a2block/.{{},{}}:>{},AB4,insertion[a1block,a1+j,0],AB6],{j,0,a2-1}];
term1+term2+term3+term4+term5]


MerctriHSR456[mgf_]:=Module[{AB1,AB2,AB3,AB4,AB5,AB6,term1,term2,term3,term4,term5,a1,a2,col01,col02,a1block,a2block},
AB1=mgf[[1]];
AB2=mgf[[2]];
AB3=mgf[[3]];
AB4=mgf[[4]];
AB5=mgf[[5]];
AB6=mgf[[6]];
a1=Total[Extract[AB5,Position[AB5,0]/.{2,x_}:>{1,x}]];
a2=Total[Extract[AB4,Position[AB4,0]/.{2,x_}:>{1,x}]];
col01=Flatten[{Position[AB5,0],Position[AB5,0]/.{2,x_}:>{1,x}},1];
col02=Flatten[{Position[AB4,0],Position[AB4,0]/.{2,x_}:>{1,x}},1];
a1block=Delete[AB5,col01];
a2block=Delete[AB4,col02];
term1=(-1)^a1 c[AB1,AB2,AB3,a2block/.{{},{}}:>{},a1block/.{{},{}}:>{},insertion[AB6,a1+a2,0]];
term2=-(-1)^(a1+a2)Binomial[a1+a2-1,a1]c[AB1,AB2,AB3,insertion[a2block,a1+a2,0],a1block/.{{},{}}:>{},AB6];
term3=- Binomial[a1+a2-1,a2]c[AB1,AB2,AB3,a2block/.{{},{}}:>{},insertion[a1block,a1+a2,0],AB6];
term4=Sum[(-1)^(a1+a2) Binomial[a2+j-1,j] c[AB1,AB2,AB3,insertion[a2block,a2+j,0],a1block/.{{},{}}:>{},insertion[AB6,a1-j,0]],{j,0,a1-1}];
term5=Sum[ Binomial[a1+j-1,j] c[AB1,AB2,AB3,a2block/.{{},{}}:>{},insertion[a1block,a1+j,0],insertion[AB6,a2-j,0]],{j,0,a2-1}];
(-1)^a2 (term1+term2+term3+term4+term5)//Expand]


MercHSR[mgfs_]:=Module[{mgfslist,rulelist},
mgfslist=Cases[Variables[mgfs],c[___]];
rulelist=Table[Which[
isthereHSMerc[mgfslist[[i]]]===tri126,mgfslist[[i]]->MerctriHSR126[mgfslist[[i]]],
isthereHSMerc[mgfslist[[i]]]===tri135,mgfslist[[i]]->MerctriHSR135[mgfslist[[i]]],
isthereHSMerc[mgfslist[[i]]]===tri456,mgfslist[[i]]->MerctriHSR456[mgfslist[[i]]],
isthereHSMerc[mgfslist[[i]]]===tri234,mgfslist[[i]]->MerctriHSR234[mgfslist[[i]]],
isthereHSMerc[mgfslist[[i]]]===box1245,mgfslist[[i]]->MercboxHSR1245[mgfslist[[i]]],
isthereHSMerc[mgfslist[[i]]]===box1346,mgfslist[[i]]->MercboxHSR1346[mgfslist[[i]]],
isthereHSMerc[mgfslist[[i]]]===box2356,mgfslist[[i]]->MercboxHSR2356[mgfslist[[i]]],
1===1,##&[]],{i,Length[mgfslist]}];
CSimplify[mgfs/.rulelist,diHSR->False,triHSR->False]]


MercboxHSR1245[mgf_]:=MerctriHSR456[mgf]


MercboxHSR1346[mgf_]:=MerctriHSR126[mgf]


MercboxHSR2356[mgf_]:=MerctriHSR135[mgf]


(* ::Section:: *)
(*Combining the functions*)


(* ::Subsubsection:: *)
(*Final Functions*)


MCons[mgfs_]:=CSimplify[mgfs,diHSR->False,triHSR->False]//MMSI//KMS//KMS//BMS


HSR[mgfs_]:=mgfs//MercHSR//MercHSR//BKHSR//BHSR//triKiteHSR//THSR//PHSR


Tet[mgfs_]:=mgfs//MCons//HSR//CSort


End[];


EndPackage[];
Protect["TetSimplify`*"];
