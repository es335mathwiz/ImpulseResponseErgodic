(* Mathematica Package *)

(* Created by the Wolfram Workbench Jun 17, 2013 *)

(* Mathematica Package *)
BeginPackage["ImpulseResponseErgodic`", { "MatPert`","NumericAMA`","umbralCalculus`"}]

defaultOpenFile[]:=$openFiles[[-1]];
resetFile[]:=Map[OpenWrite[Close[#]]& , $openFiles]

closeFile[]:=Map[Close , $openFiles]
fileName[ostr_]:=ostr[[1]]
If[Length[$openFiles]<1,
$openFiles={OpenAppend[
If[StringMatchQ[$Version,"*Windows*"],"c:/temp/defaultTimingFile",
"/tmp/"<>ToString[RunThrough["whoami",""]]<>"defaultTimingFile"]]}];
createNewFile[]:=
With[{newfy=
OpenAppend["timingFile"<>ToString[Abs[Random[]]]<>ToString[SequenceForm[Date[]]]]},
AppendTo[$openFiles,newfy];newfy]
currentFile[]:=defaultOpenFile[]
Global`$globalIndent=""
prepAMAModel::usage = "prepAMAModel  "

newAMAModel::usage = "newAMAModel  "

AMAEquations::usage = "AMAEquations  "
 
isAMAModel::usage = "isAMAModel  "
(* Exported symbols added here with SymbolName::usage *)  
(*
If[$OperatingSystem=="Windows",
	AddToClassPath["s:/tryBenchWindows3.5/Perturbation/javaOutput/"],
AddToClassPath["/msu/home/m1gsa00/scratch/tryBenchWindows3.5/Perturbation/javaOutput/"]];*)
(*
  LoadJavaClass["gov.frb.ma.msu.MultiIndex",StaticsVisible->True,AllowShortContext->True]
*)
AMASS::usage = "AMASS  "

initSSGuess::usage = "initSSGuess  "

constructFOFDrvsBDrvs::usage = "constructFOFDrvsBDrvs  "

diffOrder::usage = "diffOrder  "

genPolys::usage = "genPolys  "

nextOrderPerturbation::usage = "nextOrderPerturbation  "

intOut::usage = "intOut  "

ssSolnSubs::usage = "ssSolnSubs  "

genPolysTPlusOne::usage = "genPolysTPlusOne  "

hmatLinPtSubs::usage = "hmatLinPtSubs  "

getAllFutureEps::usage = "getAllFutureEps  "

nxtOne::usage = "nxtOne  "

volterra::usage = "volterra  "

getAllCurrentEps::usage = "getAllCurrentEps  "

pascal::usage = "pascal  "

polysToModel::usage = "polysToModel  "


Begin["`Private`"] (* Begin Private Context *) 

numInFacet[dim_Integer,deg_Integer]:=
(pascal[dim,deg]-pascal[dim,deg-1])/;And[dim>0,deg>0]
numInFacet[dim_Integer,0]:=1/;dim>0

doFacetMi[aFunc_,theVars_,theMi_List]:=Flatten[
Map[Apply[(Apply[Derivative,#][aFunc]),theVars]&,theMi]]


miInFacet[dim_Integer,deg_Integer]:=
Drop[NestList[MultiIndex`algorithm2,
predMI[dim,deg],numInFacet[dim,deg]],1]/;And[dim>0,deg>0]


predMI[dim_Integer,deg_Integer]:=
Join[Table[0,{dim-1}],{deg-1}]/;And[dim>0,deg>0]

theIndex[beta_List]:=index[beta];(*for export*)


index[beta_List]:=
With[{nn=Length[beta]},
Sum[With[{sc=(Apply[Plus , Drop[beta,cc-1]])-1},
pascal[nn-cc+1,sc]],{cc,nn}]]



numCols[theMat_?MatrixQ]:=Length[theMat[[1]]]
numRows[theMat_?MatrixQ]:=Length[theMat]
numRows[xx___]:=Print["badArg numRows",xx];
numCols[xx___]:=Print["badArg numCols",xx];



doFacet[deg_Integer,aFunc_,theVars_List]:=
If[deg==1,
Map[D[aFunc,#]&,theVars]]


AMASS[model_Symbol,opts___?OptionQ]:=
(If[FreeQ[Flatten[{opts}],hmatLinPtSubs],
{ssSubs[],computeSteadyState[model,opts]},processLinPtSubs[model,hmatLinPtSubs/.Flatten[{opts}],opts]])/;
AMAEquations[model]=!=AMAundefinedModel;
AMASS[___]:=AMAundefinedModel;



lpSubs[]:=
{Global`eps[_][_]->0,x_Symbol[Global`t+_.]:>Symbol[SymbolName[x]<>"AMAlinPt"]};

processLinPtSubs[model_Symbol,linPtSubs_List,opts___?OptionQ]:=
With[{theVars=modelVars[model],theEqns=AMAEquations[model]},
	With[{theSubs=Thread[(Through[theVars[Global`t]]/.lpSubs[])->linPtSubs]},
		With[{subbedEqns=(theEqns/.lpSubs[])/.theSubs},
model/:valAtLinPt[model,opts]=subbedEqns;			
	{lpSubs[],theSubs}]]]

stateVariables[modelEquations_]:=
Module[{$AMAjustStateVariablesTime},
Global`AMAPrint[Global`$globalIndent,"timing AMAjustStateVariables"];
(Global`$globalIndent=Global`$globalIndent<>" ");$AMAjustStateVariablesTime=TimeUsed[];
With[{finalResultForTiming=
   Union[Cases[{modelEquations},x_[Global`t]|x_[Global`t+i_]->
   x,Infinity]]},
$AMAjustStateVariablesTime=TimeUsed[]-$AMAjustStateVariablesTime;
Global`AMAPrint[(Global`$globalIndent=StringDrop[Global`$globalIndent,1]),
"AMAjustStateVariables,","done"];
WriteString[defaultOpenFile[],"{AMAjustStateVariables,",
$AMAjustStateVariablesTime,",",MemoryInUse[],",",MaxMemoryUsed[],"}\n"];
finalResultForTiming]]


getAllFutureEps[eqns_List]:=
With[{allVars=Variables[eqns]},
Select[Cases[allVars,_[Global`t+_]],isEps]]

isEps[aVar_[Global`t+_]]:=StringMatchQ[ToString[aVar],RegularExpression["^eps\$.*"]]



getEpsVars[model_Symbol]:=
Union[Cases[AMAEquations[model],Global`eps[x_][_]->Global`eps[x],Infinity]]

computeSteadyState[model_Symbol,opts___?OptionQ]:=
model/:computeSteadyState[model,opts]=
With[{eqns=AMAEquations[model]},
With[{epsVars=getEpsVars[model]},
With[{sv=Complement[stateVariables[eqns],epsVars]},
With[{initGuess=ReplaceAll[(ReplaceAll[ReplaceAll[ReplaceAll[
initSSGuess,Flatten[{opts}]],AMASSGuess[model,opts]],
   {initSSGuess->Table[0,{Length[sv]}]}]),{{}->Table[0,{Length[sv]}]}],
exogXform=ReplaceAll[ReplaceAll[exogenizeVars,Flatten[{opts}]],
{exogenizeVars->{}}]
},
With[{ssVars=Transpose[{ReplaceAll[
Through[sv[Global`t]],ssSubs[]],initGuess}],
ssEqns=Thread[(ReplaceAll[eqns,ssSubs[]])==0]},
With[{theSoln=
Apply[FindRoot , (ReplaceAll[Join[{ssEqns},ssVars],exogXform])]},
If[FreeQ[theSoln,FindRoot],
model/:valAtLinPt[model,opts]=ConstantArray[0,{Length[AMAEquations[model]]}];
newAMAModel[model,AMAEquations[model],(initSSGuess->Map[Last,theSoln])]];
theSoln]]]]]]


newAMAModel[model_Symbol,eqns_List,opts___?OptionQ]:=
  Block[{},(*Clear[model];*)
AMAEquations[model]^=eqns;
model/:modelVars[model]=getStateVars[model];
model/:modelEps[model]=getEpsVars[model];
model/:AMASSGuess[model,opts]=If[FreeQ[Flatten[{opts}],initSSGuess],{},initSSGuess->(initSSGuess/.Flatten[{opts}])];
isAMAModel[model]^=True;
]
getStateVars[model_Symbol]:=
With[{eqns=AMAEquations[model]},
With[{allVars=stateVariables[eqns],epsVars=getEpsVars[model]},Complement[allVars,epsVars]]]

getStateVars[eqns_List]:=
With[{allVars=stateVariables[eqns],epsVars=getEpsVars[model]},Complement[allVars,epsVars]]

isAMAModel[___]:=False;

prepAMAModel[theModel_Symbol,eqns_List,opts___?OptionQ]:=
newAMAModel[theModel,eqns,opts];


AMASSGuess[___]={}


cmpKeepers[leadsNeeded_List,neq_Integer]:=
Union[Flatten[Map[aVarKeep[neq,#]&,leadsNeeded]]]


aVarKeep[neq_Integer,{varNo_Integer,varLeadsNeeded__}]:=
Map[varNo+neq*(#-1)&,{varLeadsNeeded}]



constructFDerivs[theModel_Symbol,opts___?OptionQ]:=
With[{mFuncStuff=
makeMatlabFuncs[theModel,opts],
cut=
errorVarCutoff[theModel],
neq=AMANeq[theModel],
nlags=AMALags[theModel]},
With[{theFuncs=mFuncStuff[[4]],
theVars=mFuncStuff[[3]],
ssSubs=mFuncStuff[[1]],
ssVals=
AMASS[theModel,opts],
vAppByFunc=mFuncStuff[[6]],
vApp=
variablesAppearing[mFuncStuff[[6]],cut]},
With[{theFuncsApplied=
Flatten[MapThread[Apply[#1,#2]&,{theFuncs,theVars}]],
vMappers=Map[variableMapping[vApp,#]&,vAppByFunc],
modNz=constructNz[vApp,neq,nlags],
modLeads=constructLeads[vApp],
modEta=constructEta[vApp,cut]},
With[{firstDrvs=
(MapThread[doFacet[1,#1,#2]&,{theFuncsApplied,theVars}]/.ssSubs)/.
ssVals},
With[{miVals=Map[miInFacet[Length[#],2]&,theVars]},
With[{secondDrvs=
(MapThread[doFacetMi,
{theFuncs,theVars,miVals}]/.ssSubs)/.ssVals},
With[{jaggedFuncVals=
Map[Apply[Join,#]&,
Transpose[{firstDrvs,secondDrvs}]],
squLen=pascal[Length[vApp],2]-1,
forExplode=Map[
Function[xx,Apply[variableExplode[#1,Length[#2]]&,xx]],vMappers]},
{doExplosions[jaggedFuncVals,forExplode,squLen],
modNz,modLeads,modEta,nlags}
]]]]]]]


theIndex[beta_List]:=index[beta];(*for export*)


index[beta_List]:=
With[{nn=Length[beta]},
Sum[With[{sc=(Apply[Plus , Drop[beta,cc-1]])-1},
pascal[nn-cc+1,sc]],{cc,nn}]]


pascal[cc_Integer,kk_Integer]:=
pascal/:pascal[cc,kk]=(*memoized*)
	    If[kk==-1, 0,If[cc==0||kk==0,1,
	      Binomial[cc+kk,kk]]]
	  

variableMapping[longVec_List,shortVec_List]:=
With[{varNos=Flatten[Map[Position[longVec,#]&,shortVec]]},
With[{mapper=Function[xx,
Module[{resVec=Table[0,{Length[longVec]}]},
resVec[[varNos]]=xx;resVec]]},
{mapper,varNos}]]

AMALags[model_Symbol]:=(AMALags[model]^=(-1)*lagsLeads[
AMAEquations[model]][[1]])/;AMAEquations[model]=!=AMAundefinedModel;
AMALags[___]:=AMAundefinedModel;

AMANeq[model_Symbol]:=Length[AMAEquations[model]]/;
AMAEquations[model]=!=AMAundefinedModel;
AMANeq[___]:=AMAundefinedModel;


lagsLeads[modelEquations_]:=
      Union[
Join[Cases[modelEquations,x_[Global`t_]->0,Infinity],
Cases[modelEquations,x_[Global`t+v_]->v,Infinity]]];


AMALeads[model_Symbol]:=(AMALeads[model]^=lagsLeads[
AMAEquations[model]][[-1]])/;AMAEquations[model]=!=AMAundefinedModel;
AMALeads[___]:=AMAundefinedModel;


(*
returns {linPtSubs,vars and shocks appearing in system,
vars and time appearing in each eqn, list of functions to evaluate medel equations,
vars appearing in the system(redundant), pair of numbers for each var appearing in each equation indicating var name and lead or lag position,

*)
makeMatlabFuncs[model_Symbol,opts___?OptionQ]:=
With[{eqns=AMAEquations[model]},
With[{linPtSubs=If[FreeQ[Flatten[{opts}],hmatLinPtSubs],
	Flatten[hmatSSSolnSubs[model,opts]],
	processLinPtSubs[model,hmatLinPtSubs/.Flatten[{opts}],opts]]},
With[{allv=completeArgList[eqns],
sv=stateVariables[eqns]},
With[{varsForSubbing=Table[Unique["subVar"],{Length[allv]}],
appears=Map[incompleteArgList,eqns]},
With[{},
With[{vPairs=ReplaceAll[appears,xx_[tt_]:>{First[First[Position[sv,xx]]],tt-Global`t+1}/;xx=!=List],
theSubs=Thread[allv->varsForSubbing]},
With[{listOfFuncs=Map[Apply[Function,#]&,
MapThread[{#1/.theSubs,({#2}/.theSubs)}&,{appears,eqns}]]},
{linPtSubs,sv,appears,listOfFuncs,sv,vPairs}]]]]]]]/;And[
AMAEquations[model]=!=AMAundefinedModel, 
FreeQ[hmatSSSolnSubs[model,opts],FindRoot]]
makeMatlabFuncs[___]:=AMAundefinedModel;



constructNz[incList_List,neq_Integer,nlag_Integer]:=
With[{appearing=Select[incList,#[[2]]<=0&]},
Map[#[[1]]+neq*(nlag+#[[2]]-1)&,appearing]]



constructLeads[incList_List]:=
With[{appearing=Select[incList,#[[2]]>1&]},
Map[{#[[1]],#[[2]]-1}&,appearing]]

constructEta[incList_List,cut_Integer]:=
{Count[incList,{yy_Integer,xx_Integer}/;Or[xx<1,yy>cut]],
Count[incList,{yy_,xx_Integer}/;And[xx==1,yy<=cut]],
Count[incList,{_,xx_Integer}/;xx>1]}



doAnExplosion[lilDerivs_List,targets_List,squareDim_Integer]:=
Module[{resMat=Table[0,{squareDim}]},
resMat[[targets]]=lilDerivs;
resMat]

doExplosions[jaggedDerivs_List,targets_List,squareDim_Integer]:=
MapThread[doAnExplosion[#1,#2,squareDim]&,
{jaggedDerivs,targets}]



variableExplode[mapper_Function,dim_Integer]:=
With[{allMi=Join[miInFacet[dim,1],miInFacet[dim,2]]},
Map[theIndex,Map[mapper,allMi]]]

errorVarCutoff[aModel_Symbol]:=
Module[{},
With[{sv=
stateVariables[AMAEquations[aModel]]},
With[{pos=Flatten[Position[sv,Global`eps[_]]]},
Min[pos]-1]]]



variablesAppearing[incList_List,cut_Integer]:=
With[{justThese=Sort[Union[Flatten[incList,1]],
Or[#1[[2]]<#2[[2]],
And[#1[[2]]==#2[[2]],#1[[2]]=!=1,#1[[1]]<#2[[1]]],
And[#1[[2]]==#2[[2]],#1[[2]]==1,
Or[And[#1[[1]]<=cut,#2[[1]]<=cut],And[#1[[1]]>cut,#2[[1]]>cut]],
#1[[1]]<#2[[1]]],
And[#1[[2]]==#2[[2]],#1[[2]]==1,
And[#1[[1]]>cut,#2[[1]]<=cut]]]&
]},
justThese]


ssSubs[]:=
{Global`eps[_][_]->0,x_Symbol[Global`t+_.]:>Symbol[SymbolName[x]<>"AMAss"]};


hmatSSSolnSubs[model_Symbol,opts___?OptionQ]:=
(Module[{},
model/:valAtLinPt[model,opts]=ConstantArray[0,{Length[AMAEquations[model]]}];	
model/:ssSolnSubs[model,opts]=
AMASS[model,opts]])/;AMAEquations[model]=!=AMAundefinedModel;
hmatSSSolnSubs[___]:=AMAundefinedModel;


completeArgList[modelEquations_]:=
Module[{$amacompleteArgListTime},
Global`AMAPrint[Global`$globalIndent,"timing AMAcompleteArgList"];
(Global`$globalIndent=Global`$globalIndent<>" ");$amacompleteArgListTime=TimeUsed[];
With[{finalResultForTiming=
With[{allv=stateVariables[modelEquations],
ll=lagsLeads[modelEquations]},
Flatten[Map[Through[allv[Global`t+#]]&,Range[-getLag[ll],getLead[ll]]]]]},
$amacompleteArgListTime=TimeUsed[]-$amacompleteArgListTime;
Global`AMAPrint[(Global`$globalIndent=StringDrop[Global`$globalIndent,1]),
"AMAcompleteArgList,","done"];WriteString[defaultOpenFile[],
"{AMAcompleteArgList,",$amacompleteArgListTime,",",
MemoryInUse[],",",MaxMemoryUsed[],"}\n"];
finalResultForTiming]]


getLag[llPair_List]:=-llPair[[1]]
getLead[llPair_List]:=llPair[[-1]]


incompleteArgList[modelEquations_]:=
                Union[Cases[{modelEquations},x_[Global`t]|x_[Global`t+i_],Infinity]]


AMABmat[model_Symbol,opts___?OptionQ]:=(AMASoln[model,opts][[-3]])/;
AMAEquations[model]=!=AMAundefinedModel;
AMABmat[___]:=AMAundefinedModel;
AMAQmat[model_Symbol,opts___?OptionQ]:=(AMASoln[model,opts][[-4]])/;
AMAEquations[model]=!=AMAundefinedModel;
AMAQmat[___]:=AMAundefinedModel;
AMASmat[model_Symbol,opts___?OptionQ]:=(AMASoln[model,opts][[-2]])/;
AMAEquations[model]=!=AMAundefinedModel;
AMASmat[___]:=AMAundefinedModel;
AMAS0Inv[model_Symbol,opts___?OptionQ]:=(AMASoln[model,opts][[-1]])/;
AMAEquations[model]=!=AMAundefinedModel;
AMAPhi[model_Symbol,opts___?OptionQ]:=AMAS0Inv[model,opts]/;
AMAEquations[model]=!=AMAundefinedModel;
AMAS0Inv[___]:=AMAundefinedModel;
AMAEigSystem[model_Symbol,opts___?OptionQ]:=(AMASoln[model,opts][[-5]])/;
AMAEquations[model]=!=AMAundefinedModel;
AMAEigSystem[___]:=AMAundefinedModel;

AMATheta[model_Symbol,opts___?OptionQ]:=
(model/:AMATheta[model,opts]=
With[{eqns=AMAEquations[model]},
With[{epsVars=Union[Cases[eqns,Global`eps[x_][_]->Global`eps[x],Infinity]]},
With[{theTheta=Outer[D,eqns,Through[epsVars[Global`t]]]},
theTheta]]])



AMAHmat[model_Symbol,opts___?OptionQ]:=
(model/:AMAHmat[model,opts]=makeHmat[model,opts])/;
AMAEquations[model]=!=AMAundefinedModel;
AMAHmat[___]:=AMAundefinedModel;



makeHmat[model_Symbol,opts___?OptionQ]:=
(With[{eqns=AMAEquations[model]},
With[{linPtSubs=If[FreeQ[Flatten[{opts}],hmatLinPtSubs],
	Flatten[hmatSSSolnSubs[model,opts]],
	processLinPtSubs[model,hmatLinPtSubs/.Flatten[{opts}],opts]]},
With[{allv=DeleteCases[completeArgList[eqns],Global`eps[_][_]]},
With[{raw=Outer[D,eqns,allv]},
If[linPtSubs==={},{{},raw},{ReplaceRepeated[raw,Flatten[linPtSubs]],raw}]]]]])/;And[
AMAEquations[model]=!=AMAundefinedModel,
FreeQ[hmatSSSolnSubs[model,opts],FindRoot]]




AMASoln[model_Symbol,opts___?OptionQ]:=
With[{finalResultForTiming=
(model/:AMASoln[model,opts]=
With[{ilag=ReplaceAll[ReplaceAll[infoLag,Flatten[{opts}]],infoLag->0]},
Chop[numericAMA[AMAHmat[model,opts][[1]],AMALags[
model],ilag]]])},
finalResultForTiming]/;VectorQ[Flatten[AMAHmat[model,opts][[1]]],NumberQ]


(*for now assume one lead one lag*)
(*assume that only need to check non zero columns of bmat to determine the state vars*)
constructFOFDrvsBDrvs[model_Symbol,eqns_List,opts___?OptionQ]:=
With[{},prepAMAModel[model,eqns,opts];
	With[{fDrvs=ArrayFlatten[{{AMAHmat[model,opts][[1]],AMATheta[model,opts]}}]},
		model/:outerDrvs[model,opts]=fDrvs;
		model/:diffOrder[model,opts]=1;
		model/:outerArgs[model]=3*Length[fDrvs]+1;(*assumes one lead one lag*)
	{fDrvs,fixB[model,opts]}]]

fixB[model_Symbol,opts___?OptionQ]:=
With[{qMat=AMAQmat[model,opts],hMat=AMAHmat[model,opts][[1]]},
With[{bphif=numericComputeBPhiF[hMat,qMat,AMALeads[model]]},(*Print["bphif",bphif];*)
	model/:AMAFmat[model,opts]=bphif[[3]];
	nonStochAdjust[model,opts];
With[{bMat=bphif[[1]](*AMABmat[model,opts]*),phiMat=bphif[[2]](*AMAS0Inv[model,opts]*)},
With[{bInfo=nonZeroCols[bMat]},
With[{lilB=bInfo[[2]],zMat=ConstantArray[0,{Length[bMat],1}],
	lilPhi=phiMat[[All,epsRows[model]]]},
	With[{finB=ArrayFlatten[{{lilB,lilPhi,zMat}}]},
		With[{epsPart=epsAug[getEpsVars[model],Length[finB[[1]]]]},
			model/:innerDrvsT[model,opts]=finB;
			model/:innerArgs[model]=Length[finB[[1]]];
			model/:innerDrvsBottomRows[model]=epsPart;
			model/:nonZeroBCols[model]=bInfo[[1]];
			model/:innerDrvsTPlusOne[model,opts]=
			lambdaFacetDiffOrder[diffOrder[model,opts],innerArgs[model],
				innerDrvsT[model,opts],
				Join[innerDrvsT[model,opts][[nonZeroBCols[model]]],
					innerDrvsBottomRows[model]]];
			model/:lagDrvsMat[model]=makeLagMat[nonZeroBCols[model],
				Length[bMat],Length[getEpsVars[model]]];
			model/:getStateVec[model]=makeState[nonZeroBCols[model],modelVars[model],modelEps[model]];
				{finB,epsPart}
		]]]]]]]


nonStochAdjust[model_Symbol,opts___?OptionQ]:=
model/:nonStochAdjust[model,opts]=
With[{fMat=AMAFmat[model,opts],phi=AMAPhi[model,opts]},
With[{neq=Length[fMat]},
Inverse[IdentityMatrix[neq]-fMat]. phi.valAtLinPt[model,opts]]]


makeState[nzCols_?VectorQ,varNames_?VectorQ,epsNames_?VectorQ]:=
With[{keep=Through[varNames[[nzCols]][Global`t-1]],theEps=Through[epsNames[Global`t]]},
	Join[keep,theEps,{Global`Sigma}]]

epsRows[model_Symbol]:=With[{eqns=AMAEquations[model],epsVars=getEpsVars[model]},
	First[Flatten[Position[eqns,#]]]&/@epsVars]

epsAug[epsVars_?VectorQ,numCols_Integer]:=
	With[{mEps=(mangleEps/@epsVars)/.t->t+1,
		zMat=ConstantArray[0,{Length[epsVars],numCols-1}],
		lastRow=ArrayFlatten[{{ConstantArray[0,{1,numCols-1}],{{1}}}}]},
		ArrayFlatten[{{ArrayFlatten[{{zMat,Transpose[{mEps}]}}]},{lastRow}}]]
	
mangleEps[Global`eps[xx_]]:=Symbol["eps$"<>ToString[xx]][Global`t+1]
	
nonZeroCols[aMat_?MatrixQ]:=
With[{zCols=Select[Range[Length[aMat[[1]]]],
	notZero[aMat[[All,#]]]&]},
	{zCols,aMat[[All,zCols]]}]
$zTol=10^-8;	
notZero[vec_?VectorQ]:=Norm[vec]>=$zTol



makeLagMat[nzCols_?VectorQ,totCols_Integer,numEps_Integer]:=
With[{iMat=IdentityMatrix[totCols],zMat=ConstantArray[0,{totCols,numEps+1}]},
ArrayFlatten[{{Transpose[iMat[[#]]&/@nzCols],zMat}}]
]
nextOrderPrep[model_Symbol,opts___?OptionQ]:=Module[{},
With[{
	iDrvst=nextInnerDrvsTSymbolic[model,diffOrder[model,opts]+1,opts],
	iDrvstp1=nextInnerDrvsTPlusOneSymbolic[model,diffOrder[model,opts]+1,opts],
	lDrvs=nextLagDrvs[model,diffOrder[model,opts]+1,opts],
	iBot=nextInnerDrvsBottomRows[model,diffOrder[model,opts]+1,opts]},
	Join[lDrvs,iDrvst,iDrvstp1,Drop[iBot,-1]]
]]


intOut[expr_,aSoln_List,epsVar_Symbol]:=Chop[Expand[expr/.aSoln]/.{epsVar^pp_:>Symbol["Global`mom$"<>ToString[epsVar]][pp],epsVar:>Symbol["Global`mom$"<>ToString[epsVar]][0]}]

intOut[expr_,aSoln_List,{}]:=Expand[expr/.aSoln]

intOut[expr_,aSoln_List,epsVars_List]:=Fold[intOut[#1,Flatten[aSoln],#2]&,Expand[expr],epsVars]


intOut[expr_,aSoln_List,(epsVar_Symbol)[Global`t+lead_Integer/;lead>0]]:=Chop[Expand[expr/.aSoln]/.
	{epsVar[Global`t+lead]^pp_:>Symbol["Global`mom$"<>ToString[epsVar]][pp],epsVar[Global`t+lead]:>Symbol["Global`mom$"<>ToString[epsVar]][0]}]

intOut[expr_,aSoln_List,{}]:=Expand[expr/.aSoln]

intOut[expr_,aSoln_List,epsVars_List]:=Fold[intOut[#1,Flatten[aSoln],#2]&,Expand[expr],epsVars]



doFac[nums_List]:=Apply[Times ,(Map[Factorial,nums])]


genTerm[vars_List,pows_List]:=(1/doFac[pows])*(Times @@ MapThread[#1^#2&,{vars,pows}])

allPows[numVars_Integer,pow_Integer]:=
With[{allFacets=(Reverse /@MatPert`allLambda[numVars,#])&/@Range[pow]}, Join @@ allFacets]

genAllProducts[vars_List,pow_Integer]:=With[{allP=allPows[Length[vars],pow]},
genTerm[vars,#]&/@allP]

(*varname followed by lin pt*)
genPolys[model_Symbol,opts___?OptionQ]:=
genPolys[getStateVec[model], Last/@(ssSolnSubs[model,opts][[2]]),diffOrder[model,opts],
innerDrvsT[model,opts]] // Expand // Chop


genPolysTPlusOne[model_Symbol,opts___?OptionQ]:=
genPolys[getStateVec[model], Last/@(ssSolnSubs[model,opts][[2]]),diffOrder[model,opts],
intOut[innerDrvsTPlusOne[model,opts],{},mangleEps/@getEpsVars[model]]] // Expand // Chop

genPolys[vars_?VectorQ,linPt_?NumberQ,pow_Integer,coeffs_?VectorQ]:=
With[{allP=genAllProducts[vars,pow]},linPt+Plus @@(allP*coeffs)]/;
pascal[Length[vars],pow]-1==Length[coeffs]

genPolys[vars_?VectorQ,linPts_?VectorQ,pow_Integer,coeffs_?MatrixQ]:=
MapThread[genPolys[vars,#1,pow,#2]&,{linPts,coeffs}]/;And[
	Length[linPts]==Length[coeffs],
	pascal[Length[vars],pow]-1==Length[coeffs[[1]]]]

genPolys[vars_?VectorQ,linPts_?VectorQ,pow_Integer,coeffs_?MatrixQ]:=
StringForm["Length[linPts] ``, should be the same as Length of coeffs ``. And the number of columns of  coeffs  ``, should be ``",
Length[linPts],Length[coeffs],Length[coeffs[[1]]],pascal[Length[vars],pow]-1]


momentQ[var_]:=Or[MatchQ[var,Global`mom[_,_]],momFormQ[var]]

momFormQ[var_Symbol[_]]:=With[{str=ToString[var]},StringMatchQ[str,RegularExpression["^mom\$eps\$.+"]]]


polysToMultiIndexed[thePolys_List]:=
With[{theVarsPerm=pertOrder[Union[Flatten[DeleteCases[Variables[thePolys],_?momentQ]]]]},
With[{oldRules=
		CoefficientRules[thePolys,theVarsPerm[[1]]]},	
	With[{cRules=multFac[#]&/@oldRules
		},
With[{order= Max[Plus @@ #[[1]]& /@
	Flatten[cRules,2]],numVars=Length[theVarsPerm[[1]]]},
With[{theMIs=theMIsToOrder[numVars,order]},
With[{forResult=SparseArray[{},{Length[thePolys],Length[theMIs]}],
		replacements=aRowPositionValuePair[theMIs,#]&/@cRules},
With[{repArgs=Flatten[MapIndexed[replacePairs[#1,#2[[1]]]&,replacements],1]},
		ReplacePart[forResult,repArgs]
	]]]]]]]



polysToModelInfo[thePolys_List]:=
With[{theVarsPerm=pertOrder[Union[Flatten[DeleteCases[Variables[thePolys],_?momentQ]]]]},
	With[{withSig=Append[theVarsPerm[[1]],Global`Sigma]},
With[{oldRules=
		CoefficientRules[thePolys,withSig]},	
	With[{cRules=multFac[#]&/@oldRules
		},
With[{order= Max[Plus @@ #[[1]]& /@
	Flatten[cRules,2]],numVars=Length[withSig]},
With[{theMIs=theMIsToOrder[numVars,order]},
With[{forResult=SparseArray[{},{Length[thePolys],Length[theMIs]}],
		replacements=aRowPositionValuePair[theMIs,#]&/@cRules},
With[{repArgs=Flatten[MapIndexed[replacePairs[#1,#2[[1]]]&,replacements],1]},
{theVarsPerm,order,		ReplacePart[forResult,repArgs]}
	]]]]]]]]
	
(*	

polysToModelInfo[aPoly_]:=polyToModelInfo[{aPoly}]
polyToModelInfo[thePolys_List]:=
With[{theVarsPerm=pertOrder[Union[Flatten[DeleteCases[Variables[thePolys],_?momentQ]]]]},
With[{oldRules=
		CoefficientRules[thePolys,theVarsPerm[[1]]]},	
	With[{cRules=multFac[#]&/@oldRules
		},
With[{order= Max[Plus @@ #[[1]]& /@
	Flatten[cRules,2]],numVars=Length[theVarsPerm[[1]]]},
With[{theMIs=theMIsToOrder[numVars,order]},
With[{forResult=SparseArray[{},{Length[thePolys],Length[theMIs]}],
		replacements=aRowPositionValuePair[theMIs,#]&/@cRules},
With[{repArgs=Flatten[MapIndexed[replacePairs[#1,#2[[1]]]&,replacements],1]},
{theVarsPerm,order,ReplacePart[forResult,repArgs]}
	]]]]]]]
*)


pertOrder[someVars_List]:=
With[{theEpsVars=Sort[Cases[someVars,Global`eps[_][t+_.]]],
theSigma=Cases[someVars,Global`Sigma]},
With[{theRest=Sort[Complement[someVars,Join[theEpsVars,theSigma]]]},
	With[{newVarsList=	Join[theRest,theEpsVars,theSigma]},
	{newVarsList,getPermutation[someVars,newVarsList]}]]]

getPermutation[oldVars_List,newVars_List]:=
Range[Length[newVars]]
	
theMIsToOrder[numVars_Integer,ord_Integer]:=
theMIsToOrder/:theMIsToOrder[numVars,ord]=(*memoized*)
Flatten[Join[Reverse[MatPert`allLambda[numVars,#]]&/@Range[ord]],1]


replacePairs[posValPair_?MatrixQ,theRow_Integer]:=
MapThread[{theRow,#1}->#2&,posValPair]

	
aRowPositionValuePair[theMIs_List,cRulesRow_List]:=
With[{noConstants=Select[cRulesRow,Plus@@ #[[1]]>0&]},
With[{locs=Flatten[Position[theMIs,#[[1]]]&/@
	noConstants]},
	{locs,Last/@noConstants}]]
multFac[oldRules_List]:=
(#[[1]]->(doFac[#[[1]]]*#[[2]]))&/@oldRules


nextOrderPerturbation[model_Symbol,opts___?OptionQ]:=
With[{allDrvs=nextOrderPrep[model,opts],mangled=mangleEps/@getEpsVars[model]},
	With[{preInt=lambdaFacetDiffOrder[diffOrder[model,opts]+1,innerArgs[model],
		nextOuterDrvs[model,diffOrder[model,opts]+1,opts],allDrvs]//Chop},
		With[{postInt=intOut[Flatten[preInt],{},mangled]//Chop},
			With[{varsToSolve=Union[Cases[Variables[postInt],_Symbol[_?VectorQ],Infinity]]},
			With[{theSys=Thread[DeleteCases[postInt,0]==0]},
				With[{theSoln=Flatten[Solve[theSys,varsToSolve]]},
					model/:innerDrvsT[model,opts]=nextInnerDrvsTSymbolic[model,diffOrder[model,opts]+1,opts]/.theSoln;
					model/:innerDrvsTPlusOne[model,opts]=nextInnerDrvsTPlusOneSymbolic[model,diffOrder[model,opts]+1,opts]/.theSoln;
					model/:outerDrvs[model,opts]=nextOuterDrvs[model,diffOrder[model,opts]+1,opts];
					model/:nextInnerDrvsTSymbolic[model,diffOrder[model,opts]+1,opts]=.;
					model/:nextInnerDrvsTPlusOneSymbolic[model,diffOrder[model,opts]+1,opts]=.;
					model/:nextInnerDrvsBottomRows[model,diffOrder[model,opts]+1,opts]=.;
					model/:nextOuterDrvs[model,diffOrder[model,opts]+1,opts]=.;
					model/:diffOrder[model,opts]=diffOrder[model,opts]+1
				]]]]]]

nextLagDrvs[model_Symbol,diff_Integer,opts___?OptionQ]:=
With[{neq=Length[AMAEquations[model]]},
ArrayFlatten[{{lagDrvsMat[model],
	ConstantArray[0,{neq,pascal[innerArgs[model],diffOrder[model,opts]+1]-innerArgs[model]-1}]}}]]

(*
allLambda[mm_Integer,nn_Integer]:=Reverse[Combinatorica`Compositions[nn,mm]]
*)
nextInnerDrvsTSymbolic[model_Symbol,diff_Integer,opts___?OptionQ]:=
model/:nextInnerDrvsTSymbolic[model,diff,opts]=
With[{nxtLambdas=Reverse[MatPert`allLambda[innerArgs[model],diffOrder[model,opts]+1]]},
	ArrayFlatten[{{innerDrvsT[model,opts],symbDrvs[#,nxtLambdas]&/@modelVars[model]}}]]

nextInnerDrvsTPlusOneSymbolic[model_Symbol,diff_Integer,opts___?OptionQ]:=	
	model/:nextInnerDrvsTPlusOneSymbolic[model,diff,opts]=
	ArrayFlatten[{{innerDrvsTPlusOne[model,opts],
			lambdaFacetDiffOrder[diffOrder[model,opts]+1,innerArgs[model],
				nextInnerDrvsTSymbolic[model,diff,opts],
				Join[nextInnerDrvsTSymbolic[model,diff,opts][[nonZeroBCols[model]]],
					nextInnerDrvsBottomRows[model,diff,opts]]]}}];

nextInnerDrvsBottomRows[model_Symbol,diff_Integer,opts___?OptionQ]:=
model/:nextInnerDrvsBottomRows[model,diff,opts]=
With[{idbr=innerDrvsBottomRows[model]},
ArrayFlatten[{{idbr,
	ConstantArray[0,{Length[idbr],numNewDrvsToGet[model,opts]}]}}]]

numNewDrvsToGet[model_Symbol,opts___?OptionQ]:=
With[{idbr=innerDrvsBottomRows[model]},
Length[nextInnerDrvsTSymbolic[model,diffOrder[model,opts]+1,opts][[1]]]-Length[idbr[[1]]]]


nextInnerLagDrvs[model_Symbol,diff_Integer,opts___?OptionQ]:=
With[{ldm=lagDrvsMat[model]},
ArrayFlatten[{{ldm,
	ConstantArray[0,{Length[idbr],paddingForLagDrvs[model]}]}}]]
	
paddingForLagDrvs[model_Symbol,opts___?OptionQ]:=
With[{ldm=lagDrvsMat[model]},
Length[nextInnerDrvsTSymbolic[model,opts][[1]]]-Length[ldm[[1]]]]



symbDrvs[var_Symbol,drvs_List]:=var[#]&/@drvs

nextOuterDrvs[model_Symbol,diff_Integer,opts___?OptionQ]:=
model/:nextOuterDrvs[model,diff,opts]=
With[{subbedFunc=getSubbedFunction[model]},
With[{theArg=makeArgList[model]},
With[{theMIs=Reverse[MatPert`allLambda[Length[theArg],diffOrder[model,opts]+1]]},
With[{newDrvs=Transpose[(Derivative[Sequence@@#][subbedFunc][Sequence@@theArg])//.
	(Join @@ssSolnSubs[model,opts])&/@theMIs]},
	ArrayFlatten[{{outerDrvs[model,opts],newDrvs}}]]]]]
	
makeArgList[model_Symbol]:=
With[{allv=DeleteCases[completeArgList[AMAEquations[model]],Global`eps[_][_]],
	allEps=Through[modelEps[model][Global`t]]},	
	Join[allv,allEps]]
	
	
getSubbedFunction[model_Symbol]:=	
getSubbedFunction[model]=
With[{eqns=AMAEquations[model]},
With[{theArg=makeArgList[model]},
	With[{funcSubs=Thread[theArg->
		Table[Unique["$vars"],{Length[theArg]}]]},	
		Function @@({theArg,eqns}/.funcSubs)]]]
	
	

compose[model_Symbol,outer_?MatrixQ,inner_?MatrixQ,
theSubs_List,theOpts___?OptionQ]:=
With[{$theOrder=diffOrder[model,theOpts],
nzCols=nonZeroBCols[model],
inArgs=innerArgs[model],
idb=innerDrvsBottomRows[model]/.theSubs},
  umbralCalculus`Private`lambdaSumsDiffOrder[$theOrder, inArgs,
  outer,
ArrayFlatten[{{inner[[nzCols]]},
{ArrayFlatten[{{
idb,
ConstantArray[0,{Length[idb],Length[inner[[1]]]-Length[idb[[1]]]}]}}]}}]]]




firstCompose[model_Symbol,outer_?MatrixQ,theOpts___?OptionQ]:=
With[{neq=Length[AMAEquations[model]],
idbr=innerDrvsBottomRows[model],
inArgs=innerArgs[model],
$theOrder=diffOrder[model,theOpts],
numState=Length[nonZeroBCols[model]]},
With[{totDrvs=pascal[inArgs,$theOrder]-1},
With[{identityDrvs=ArrayFlatten[{{IdentityMatrix[neq],
ConstantArray[0,
{neq,totDrvs-neq}]}}]},
  umbralCalculus`Private`lambdaSumsDiffOrder[$theOrder, inArgs,
  outer,
ArrayFlatten[{{identityDrvs[[Range[numState]]]},
{ArrayFlatten[{{
idbr,
ConstantArray[0,{Length[idbr],Length[identityDrvs[[1]]]-Length[idbr[[1]]]}]}}]}}]]]]]

volterra[model_Symbol,len_Integer,varSubs_List,theOpts_?OptionQ]:=
With[{fcDrvs=firstCompose[model,innerDrvsT[model,theOpts],theOpts]},
With[{farOutDrvs=NestList[doNext[model,#,theOpts]&,{fcDrvs,1,fcDrvs},len-1]},
With[{theSSSubs=ssSolnSubs[model,theOpts]},
With[{theLinPt=Last/@theSSSubs[[2]],
theAdj=nonStochAdjust[model,theOpts],
theSV=getStateVec[model]},
With[{thePolys=genPolys[theSV,theLinPt-theAdj,diffOrder[model,theOpts],#[[3]]]&/@farOutDrvs,
zapSV=Join[{Global`Sigma->Global`sigma},Thread[theSV->0]]},
thePolys/.Join[zapSV,varSubs]]]]]]


doNext[model_Symbol,{oneStep_?MatrixQ,timeNow_Integer,drvsNow_?MatrixQ},theOpts___?OptionQ]:=
With[{oneStepSubbed=oneStep/.Global`t->Global`t+timeNow},
{oneStep,timeNow+1,compose[model,oneStepSubbed,drvsNow,{},theOpts]}]



doubleJump[model_Symbol,oneJump_?MatrixQ,theOpts___?OptionQ]:=
With[{theEpsVals=getAllFutureEps[oneJump]},
With[{theEpsSubs=makeEpsSubs[theEpsVals]},
compose[model,oneJump/.theEpsSubs,oneJump,theEpsSubs,theOpts]]]

makeEpsSubs[someEpsVals_List]:=
With[{theLead=maxEpsLead[someEpsVals]},Thread[someEpsVals->(someEpsVals/.Global`t->Global`t+theLead)]]

maxEpsLead[someEpsVals_List]:=
Max[Cases[getAllFutureEps[someEpsVals],_[Global`t+ll_Integer]->ll]]

uniqueEpsHeads[epsVals_List]:=Union[Cases[getAllFutureEps[epsVals],xx_[t+_]->xx]]

ergodicMean[model_Symbol,
iterations_Integer,varSubs_List,theOpts___?OptionQ]:=
With[{fcDrvs=firstCompose[model,innerDrvsT[model,theOpts],theOpts]},
With[{farOutDrvs=Nest[doubleJump[model,#,theOpts]&,fcDrvs,iterations]},
With[{intFarOut=intOut[farOutDrvs,{},getAllFutureEps[farOutDrvs]]},
With[{theSSSubs=ssSolnSubs[model,theOpts]},
With[{theLinPt=Last/@theSSSubs[[2]],
theAdj=nonStochAdjust[model,theOpts],
theSV=getStateVec[model]},
With[{thePolys=genPolys[theSV,theLinPt-theAdj,diffOrder[model,theOpts],intFarOut],
zapSV=Join[{Global`Sigma->1},Thread[theSV->0]]},
thePolys/.Join[zapSV,varSubs]]]]]]]


ergodicMeanProj[model_Symbol,
iterations_Integer,varSubs_List,theOpts___?OptionQ]:=
With[{fcDrvs=firstCompose[model,innerDrvsT[model,theOpts],theOpts]},
With[{farOutDrvs=Nest[doubleJump[model,#,theOpts]&,fcDrvs,iterations]},
With[{intFarOut=intOut[farOutDrvs,{},getAllFutureEps[farOutDrvs]]},
With[{(*theSSSubs=ssSolnSubs[model,theOpts]*)},
With[{(*theLinPt=Last/@theSSSubs[[2]],
theAdj=nonStochAdjust[model,theOpts],*)
theSV=getStateVector[model]},
With[{thePolys=genPolys[theSV,0*theSV,diffOrder[model,theOpts],intFarOut],
zapSV=Join[{Global`Sigma->1},Thread[theSV->0]]},
thePolys/.Join[zapSV,varSubs]]]]]]]


nxtOne[model_Symbol,theOrder_Integer,leaps_Integer,theSubs_List,thisOne___?OptionQ]:=
Module[{},
constructFOFDrvsBDrvs[model, AMAEquations[model], thisOne];
Table[nextOrderPerturbation[model, thisOne],{theOrder-1}];
hmatLinPtSubs->ergodicMean[model,leaps,theSubs, thisOne]]


polysToModel[modName_Symbol,polys_List,ssSubs_List,stateRows_List]:=
With[{mInfo=polysToModelInfo[polys]},
	With[{epsPart=epsAug[{Global`eps[Global`zz]},4]},(*needs generalization*)
modName/:ssSolnSubs[modName]={{},ssSubs};
modName/:innerDrvsT[modName]=mInfo[[3]];
modName/:AMAEquations[modName]=polys;
modName/:diffOrder[modName]=mInfo[[2]];
modName/:modelVars[modName]=getStateVars[polys];
modName/:innerDrvsBottomRows[modName]=epsPart;
modName/:innerArgs[modName]=Length[mInfo[[1,1]]]+1;
modName/:nonZeroBCols[modName]=stateRows;
modName/:getStateVector[modName]=Append[mInfo[[1,1]],Global`Sigma];
modName
]]

End[] (* End Private Context *)

EndPackage[]