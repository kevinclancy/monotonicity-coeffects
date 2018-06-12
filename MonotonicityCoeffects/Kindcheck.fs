module Kindcheck

open PCF
open Microsoft.FSharp.Text.Lexing
open Ast
open CheckComputation

module P = PCF

let V = P.Var
let Ap = P.App
let Ab = P.Abs
let ListCase = P.ListCase
let BoolCase (scrut : P.Term, tCase : P.Term, fCase : P.Term) =
    P.SumCase(scrut, P.Abs("_",P.Unit, tCase), P.Abs("_",P.Unit, fCase))
let P1 = P.Proj1
let P2 = P.Proj2
let I1 = P.In1
let I2 = P.In2

/// tyVarEnv maps each identifier to a kind it is bound to
/// tyBaseEnv maps each base type name (they are semilattices) to its kind
type TypeEnvironment = { 
    tyVarEnv : Map<string, ProperKind> ; 
    tyBaseEnv : Map<string, Kind> ;  
    tyAliasEnv : Map<string, Ty> 
}

let getProper (role : string) (k : Kind) : Check< SemPoset * Option<SemToset> * Option<SemSemilat> > =
    match k with
    | KProper(semPoset, semToset, semSemilat,_) ->
        Result(semPoset, semToset, semSemilat)
    | _ ->
        Error [role + " does not have a proper kind", noRange]

type Range = Position * Position

 type KindSynthResult =
    | Success of result : Kind
    | Failure of stack : List<string*Range>

 let makeDictionarySemilat (pDomTy : P.Ty) (pCodTy : P.Ty) (domTy : Ast.Ty) (codDeltaTy : Ast.Ty) (pDomComp : P.Term) (jCod : P.Term)
                           (pCodDeltaTy : P.Ty) (pCodIso : P.Term)
                           : P.Ty * P.Term * P.Term * Ast.Ty * P.Term =

    let resTy = P.List (P.Prod(pDomTy, pCodTy))
    let elemTy = P.Prod(pDomTy, pCodTy)
    let bot = P.EmptyList(elemTy)
    let join = 
        P.LetRec("!f", "!x", resTy, P.Fun(resTy,resTy), P.Abs("!y", resTy, 
            P.ListCase(V("!x"), V("!y"), 
                P.Abs("!xh", elemTy, P.Abs("!xt", resTy, 
                    P.ListCase(V("!y"), V("!x"), P.Abs("!yh", elemTy, P.Abs("!yt", resTy, 
                        BoolCase(P.App(P.App(pDomComp, P.Proj1(V("!xh"))), P.Proj1(V("!yh"))),
                            P.Cons(P.Var("!xh"), P.App(P.App(V("!f"), V("!xt")), V("!y"))),
                            BoolCase(P.App(P.App(pDomComp, P.Proj1(V("!yh"))), P.Proj1(V("!xh"))),
                                P.Cons(P.Var("!yh"), P.App(P.App(V("!f"), V("!x")), V("!yt"))),
                                P.Cons(P.Pair(P.Proj1(V("!xh")), P.App(P.App(jCod,P.Proj2(V("!xh"))),P.Proj2(V("!yh")))), 
                                        P.App(P.App(V("!f"),V("!xt")), V("!yt")))))))))))))
    let pDeltaTy = P.Prod(pDomTy, pCodDeltaTy)
    let isoCodTy = P.List(pDeltaTy)
    // converts a pCodDeltaTy list 
    // d1 :: ... :: dn :: [] 
    // into the pDomTy * pCodDeltaTy list
    // (!x, d1) :: ... :: (!x, dn),
    // appending the result to !acc
    let pairWithList = 
        P.Abs("!x", pDomTy, P.Abs("!acc", isoCodTy, P.LetRec("!f", "!l", P.List(pCodDeltaTy), P.List(pDeltaTy),
            P.ListCase(P.Var("!l"), P.Var("!acc"), 
                P.Abs("!h", pCodDeltaTy, P.Abs("!t", P.List(pCodDeltaTy), 
                    P.Cons(P.Pair(P.Var("!x"), P.Var("!h")), P.App(P.Var("!f"), P.Var("!t")))))))))
    let resIso = 
        P.LetRec("!f", "!d", resTy, isoCodTy,
            P.ListCase(P.Var("!d"),
                P.EmptyList(isoCodTy),
                P.Abs("!h", elemTy, P.Abs("!t", resTy, 
                    P.App(P.App(P.App(pairWithList, P.Proj1(P.Var("!h"))), 
                                P.App(P.Var("!f"), P.Var("!t"))),
                          P.App(pCodIso, P.Proj2(P.Var("!h"))))))))
    resTy, bot, join, (Ast.Prod(Ast.Capsule(domTy, CoeffectAny, noRange), codDeltaTy, noRange)), resIso

let makeProdSemilat (pTyL : P.Ty) (pTyR : P.Ty) (bL : P.Term) (bR : P.Term) 
                    (jL : P.Term) (jR : P.Term) (deltaTyL : Ast.Ty) (deltaTyR : Ast.Ty) (pDeltaL : P.Ty) (pDeltaR : P.Ty)
                    (pIsoL : P.Term) (pIsoR : P.Term) : P.Ty * P.Term * P.Term * Ast.Ty * P.Term =

    let resTy = P.Prod(pTyL, pTyR)
    let resBot = P.Pair(bL, bR)
    let resJoin = P.Abs("!x", resTy, P.Abs("!y", resTy, 
                    P.Pair(P.App(P.App(jL, P.Proj1(V("!x"))),P.Proj1(V("!y"))),
                            P.App(P.App(jR,P.Proj2(V("!x"))), P.Proj2(V("!y"))))))    
    let pDeltaTy = P.Sum(pDeltaL, pDeltaR)
    let pIsoResTy = P.List(pDeltaTy)
    let deltasL = P.App(pIsoL, P.Proj1(P.Var("!p")))
    let deltasR = P.App(pIsoR, P.Proj2(P.Var("!p")))
    let pIso = 
        P.Abs("!p", resTy, 
            (append pDeltaTy 
                (forEach pDeltaL pDeltaTy (P.Abs("!d", pDeltaL, P.In1(pDeltaL, pDeltaR, P.Var("!d")))) deltasL)
                (forEach pDeltaR pDeltaTy (P.Abs("!d", pDeltaR, P.In2(pDeltaL, pDeltaR, P.Var("!d")))) deltasR)))
    resTy, resBot, resJoin, (Ast.Sum(deltaTyL, deltaTyR, noRange)), pIso

let makeIVarSemilat (elemTy : Ast.Ty) (pElemTy : P.Ty) (elemComp : P.Term) : P.Ty * P.Term * P.Term * Ast.Ty * P.Term =
    let resTy = P.List pElemTy
    let bot = EmptyList(pElemTy) 
    let join = 
        P.LetRec("!f", "!x", resTy, P.Fun(resTy,resTy), P.Abs("!y", resTy, 
            P.ListCase(V("!x"), V("!y"), 
                P.Abs("!xh", pElemTy, P.Abs("!xt", resTy, 
                    P.ListCase(V("!y"), V("!x"), P.Abs("!yh", pElemTy, P.Abs("!yt", resTy, 
                        BoolCase(P.App(P.App(elemComp, P.Proj1(V("!xh"))), P.Proj1(V("!yh"))),
                            P.Cons(P.Var("!xh"), P.App(P.App(V("!f"), V("!xt")), V("!y"))),
                            BoolCase(P.App(P.App(elemComp, P.Proj1(V("!yh"))), P.Proj1(V("!xh"))),
                                P.Cons(V("!yh"), P.App(P.App(V("!f"), V("!x")), V("!yt"))),
                                P.App(P.App(V("!f"),V("!xt")), V("!yt"))))))))))))
    let deltaTy = elemTy
    let pIso = P.Abs("!x", resTy, P.Var("!x"))
    resTy, bot, join, deltaTy, pIso

let makePartialSemilat (underlyingTy : Ty) (pTy : P.Ty) (deltaTy : Ty) (pDeltaTy : P.Ty) 
                       (bot : P.Term) (join : P.Term) (iso : P.Term) : P.Ty * P.Term * P.Term * Ast.Ty * P.Term =
    let resTy = P.Sum(pTy, P.Unit)
    let resBot = P.In1(pTy,P.Unit,bot)
    let resJoin =
        P.Abs("!x", resTy, P.Abs("!y", resTy, 
            P.SumCase(V("!x"), 
                P.Abs("!x'", pTy, 
                    P.SumCase(V("!y"), 
                        P.Abs("!y'", pTy, P.In1(pTy,P.Unit,P.App(P.App(join, V("!x'")), V("!y'")))),
                        P.In2(pTy,P.Unit,P.PrimUnitVal))),
                P.Abs("!x'", P.Unit, P.In2(pTy,P.Unit,P.PrimUnitVal)))))
    let resDeltaTy = Ast.Partial(deltaTy, noRange)
    let pResDeltaTy = P.Sum(pDeltaTy, P.Unit)
    let pMapDelta = P.Abs("!x", pDeltaTy, P.In1(pDeltaTy, P.Unit, P.Var("!x")))
    let pDeltasL = P.App(iso, P.Var("!l"))
    let resIso = 
        P.Abs("!x", resTy, 
            P.SumCase(P.Var("!x"), 
                P.Abs("!l", pTy, (forEach pDeltaTy pResDeltaTy pMapDelta pDeltasL)),
                P.Abs("!r", P.Unit, P.Cons(P.In2(pDeltaTy, P.Unit, P.PrimUnitVal), P.EmptyList(P.List(pResDeltaTy))))))
    resTy, resBot, resJoin, resDeltaTy, resIso

let makeProdToset (pTyL : P.Ty) (compL : P.Term) (pTyR : P.Ty) (compR : P.Term)
                  : P.Ty * P.Term =
    let resTy = P.Prod(pTyL, pTyR)
    resTy,
    P.Abs("!x", resTy, P.Abs("!y", resTy, BoolCase(P.App(P.App(compL, P.Proj1(P.Var("!x"))),P.Proj1(P.Var("!y"))),
                                                    pcfTrue,
                                                    BoolCase(P.App(P.App(compL, P.Proj1(P.Var("!y"))),P.Proj1(P.Var("!x"))),
                                                      pcfFalse,
                                                      P.App(P.App(compR, P.Proj2(P.Var("!x"))),P.Proj2(P.Var("!y")))))))

let makeSumToset (pTyL : P.Ty) (compL : P.Term) (pTyR : P.Ty) (compR : P.Term) =
    let resTy = P.Sum(pTyL, pTyR)
    resTy,
    P.Abs("!x", resTy, P.Abs("!y", resTy, 
        P.SumCase(P.Var("!x"), 
                P.Abs("!x'", pTyL, P.SumCase(P.Var("!y"), P.Abs("!y'", pTyL, P.App(P.App(compL,P.Var("!x'")), P.Var("!y'"))), P.Abs("!_", pTyL, pcfTrue))),
                P.Abs("!x'", pTyR, P.SumCase(P.Var("!y"), P.Abs("!y'", pTyR, P.App(P.App(compR,P.Var("!x'")), P.Var("!y'"))), P.Abs("!_", pTyR, pcfFalse))))))          

/// kCheckToset tenv ty = res
/// tenv - the type environment to check under
/// ty   - the type to check
/// res  - None if the type is a toset, 
///        (Some explanation), otherwise, where explanation is a stack of errors
let rec kCheckToset (tenv : TypeEnvironment) (ty : Ty) : Check<SemPoset * SemToset> =
    let errorMsg = "Type " + ty.ToString() + " is not a toset"
    let tyVarEnv, tyBaseEnv, tyAliasEnv = tenv.tyVarEnv, tenv.tyBaseEnv, tenv.tyAliasEnv
    match ty with
    | TyId(name,rng) ->
        match tyVarEnv.TryFind(name) with
        | Some(pk) ->
            match pk with
            | Poset ->
                Error ["type variable " + name + " bound to kind POSET", rng]
            | Toset ->
                let semPoset = P.TyVar("$" + name)
                let semToset = P.Var("$" + name + "_comp")
                Result (semPoset, semToset)
            | Semilattice ->
                Error ["type variable " + name + " bound to kind SEMILAT", rng]
        | None ->
            match tyBaseEnv.TryFind(name) with
            | Some( KProper(semPoset, Some(semToset),_,_) ) ->
                Result (semPoset, semToset)
            | Some ( KProper(_,_,_,_) ) ->
                Error [errorMsg, rng]
            | Some ( KOperator(_,_,rng) ) ->
                failwith "there should be no type operators in the base type environment"
            | None ->
                match tyAliasEnv.TryFind(name) with
                | Some(ty) ->
                    withError errorMsg rng (kCheckToset tenv ty)
                | None ->
                    Error ["type " + name + " not found", rng]                    
    | FunTy(_,_,_,rng) ->
        Error [errorMsg + ": no function type is considered a toset", rng]
    | Dictionary(dom, cod, rng) ->
        Error [errorMsg + ": no dictionary type is considered a toset", rng]
    | Capsule(ty,q, rng) ->
        Error [errorMsg + ": no capsule type is considered a toset", rng]
    | Prod(tyL, tyR, rng) ->
        check {
            let! (pTyL, compL) = withError (errorMsg + ": left component is not a toset type") rng (kCheckToset tenv tyL)
            let! (pTyR, compR) = withError (errorMsg + ": right component is not a toset type") rng (kCheckToset tenv tyR)
            let resTy, comp = makeProdToset pTyL compL pTyR compR
            return resTy, comp
        }
    | Sum(tyL, tyR, rng) ->
        check {
            let! (pTyL, compL) = withError (errorMsg + ": left component is not a toset type") rng (kCheckToset tenv tyL)
            let! (pTyR, compR) = withError (errorMsg + ": right component is not a toset type") rng (kCheckToset tenv tyR)
            let resTy, comp = makeSumToset pTyL compL pTyR compR
            return resTy, comp         
        }
    | IVar(_, rng) ->
        Error [(errorMsg + ": no ivar type is considered a toset", rng)]
    | TyOp(varId, kind, body, rng) ->
        Error [(errorMsg + ": no type operator is totally ordered", rng)]
    | ForallTy(varId, kind, body, rng) ->
        Error [(errorMsg + ": forall types do not denote tosets",rng)]
    | Partial(ty,rng) ->
        Error [(errorMsg + ": no type in the partiality monad is totally ordered",rng)]
    | TyApp(tyOp, tyArg, rng) ->
        check {
            // check that forall is type operator and argTy is proper type which matches domain of forall
            let! kOp = withError errorMsg rng (kSynth tenv tyOp)
            let! opDom, _ =
                match kOp with
                | KProper(_,_,_,rngOp) ->
                    Error [errorMsg + ": " + tyOp.ToString() + " is not a type operator", rngOp]
                | KOperator(dom, cod, _) ->
                    Result (dom, cod)
            let! kArg = withError errorMsg rng (kSynth tenv tyArg)
            let! _, _, _ = getProper (tyArg.ToString()) kArg
            let! _ = 
                match hasKind kArg opDom with
                | true -> 
                    Result ()
                | false -> 
                    Error ["kind " + kArg.ToString() + " of type argument " + tyArg.ToString() + " does not match expected kind " + opDom.ToString(), rng]
            let! pTy, pTermComp = withError errorMsg rng (kCheckToset tenv (Ty.normalize(tenv.tyAliasEnv, ty)))
            return (pTy, pTermComp)
        }

/// kCheckSemilattice tenv ty = res 
/// tenv - the type environment to check under
/// ty - the type to check
/// ty0 - If ty is a semilattice type, None
///       Otherwise, Some explanation, where explanation is an error stack
/// res = pTy, pBot, pJoin, tyDelta
/// where
///   pTy - Is the PCF translation of ty
///   pBot - Is a PCF term of type pTy (the bottom semilattice element)
///   pJoin - Is a PCF term of type pTy ->+ pTy ->+ pTy (the join operator)
///   tyDelta - Is the delta type corresponding of ty
///   pIso - Letting pTyDelta be the pcf translation of tyDelta,
///          pIso is the half of the iso from 
///            ty to O_{fin}(tyDelta)
///          or, in PCF,
///            pTy to (List pTyDelta)
and kCheckSemilattice (tenv : TypeEnvironment) (ty : Ty) : Check<P.Ty * P.Term * P.Term * Ast.Ty * P.Term> =
    let tyVarEnv, tyBaseEnv, tyAliasEnv = tenv.tyVarEnv, tenv.tyBaseEnv, tenv.tyAliasEnv
    let errorMsg = "Type " + ty.ToString() + " is not a semilattice"
    match ty with
    | TyId(name,rng) ->
        match tyVarEnv.TryFind(name) with
        | Some(pk) ->
            match pk with
            | Poset ->
                Error ["type variable " + name + " bound to kind POSET", rng]
            | Toset ->
                Error ["type variable " + name + " bound to kind TOSET", rng]
            | Semilattice ->
                let semPoset = P.TyVar("$" + name)
                let bot = P.Var("$" + name + "_bot")
                let join = P.Var("$" + name + "_join")
                let delta = Ast.TyId(name + "Delta", noRange)
                let iso = P.Var("$" + name + "_iso")
                Result (semPoset, bot, join, delta, iso)                
        | None ->
            match tyBaseEnv.TryFind(name) with
            | Some( KProper(semPoset,_, (Some {bot = bot ; join = join ; tyDelta = tyDelta ; iso = iso}) ,_) ) ->
                Result (semPoset, bot, join, tyDelta, iso)
            | Some ( KProper(_,_,_,_) ) ->
                Error [errorMsg, rng]
            | Some ( KOperator(_,_,_) ) ->
                failwith "there should be no type operators in the base type environment"
            | None ->
                match tyAliasEnv.TryFind(name) with
                | Some(ty) ->
                    withError errorMsg rng (kCheckSemilattice tenv ty)
                | None ->
                    Error ["type " + name + " not found", rng]  
    | FunTy(_,_,_,rng) ->
        Error [errorMsg + ": function types are not considered semilattice types", rng]
    | Dictionary(dom, cod, rng) ->
        check {
            let! (pDomTy, pDomComp) = withError (errorMsg + ": the domain of a dictionary must be a toset") rng (kCheckToset tenv dom)
            let! (pCodTy, _, jCod, tyDeltaCod, pIsoCod) = withError (errorMsg + ": the codomain of a dictionary must be a semilattice") rng (kCheckSemilattice tenv cod)
            let! pTyDeltaCod = kCheckProset tenv tyDeltaCod
            let resTy, bRes, jRes, tyDeltaRes, pIsoRes = makeDictionarySemilat pDomTy pCodTy dom tyDeltaCod pDomComp jCod pTyDeltaCod pIsoCod 
            return resTy, bRes, jRes, tyDeltaRes, pIsoRes
        }
    | Capsule(ty,q, rng) ->
        Error [errorMsg + ": capsule types are not considered semilattice types", rng]
    | Prod(tyL,tyR, rng) ->
        check {
            let! (tyL, bL, jL, deltaL, isoL) = withError (errorMsg + ": left component is not a semilattice type") rng (kCheckSemilattice tenv tyL)
            let! (tyR, bR, jR, deltaR, isoR) = withError (errorMsg + ": right component is not a semilattice type") rng (kCheckSemilattice tenv tyR)
            let! pDeltaL = kCheckProset tenv deltaL
            let! pDeltaR = kCheckProset tenv deltaR
            let resTy, resBot, resJoin, resDelta, resIso = makeProdSemilat tyL tyR bL bR jL jR deltaL deltaR pDeltaL pDeltaR isoL isoR
            return resTy, resBot, resJoin, resDelta, resIso
        }
    | Sum(_,_,rng) ->
        Error [(errorMsg + ": sum types are not semilattice types",rng)]
    | IVar(elemTy, rng) ->
        check {
            let! (pElemTy, pElemComp) = 
                withError (errorMsg + ": the content type of an ivar must be a toset type") rng (kCheckToset tenv elemTy)
            let resTy, resBot, resJoin, resDelta, resIso = makeIVarSemilat elemTy pElemTy pElemComp
            return (resTy, resBot, resJoin, resDelta, resIso)
        }    
    | TyOp(_,_,_,rng) ->
        Error [(errorMsg + ": type operators do not denote semilattices", rng)]
    | ForallTy(varId, kind, body, rng) ->
        Error [(errorMsg + ": forall types do not denote semilattices",rng)]
    | Partial(elemTy,rng) ->
        check {
            let! (pElemTy, bot, join, deltaTy, iso) = 
                withError (errorMsg + ": [ty] is only a semilattice if ty is a semilattice") rng (kCheckSemilattice tenv elemTy)
            let! pDeltaTy = kCheckProset tenv deltaTy
            let resTy, resBot, resJoin, resDelta, resIso = makePartialSemilat elemTy pElemTy deltaTy pDeltaTy bot join iso
            return (resTy, resBot, resJoin, resDelta, resIso)
        }
    | TyApp(tyOp, tyArg, rng) ->
        check {
            // check that forall is type operator and argTy is proper type which matches domain of forall
            let! kOp = withError errorMsg rng (kSynth tenv tyOp)
            let! opDom, _ =
                match kOp with
                | KProper(_,_,_,rngOp) ->
                    Error [errorMsg + ": " + tyOp.ToString() + " is not a type operator", rngOp]
                | KOperator(dom, cod, _) ->
                    Result (dom, cod)
            let! kArg = withError errorMsg rng (kSynth tenv tyArg)
            let! _, _, _ = getProper (tyArg.ToString()) kArg
            let! _ = 
                match hasKind kArg opDom with
                | true -> 
                    Result ()
                | false -> 
                    Error ["kind " + kArg.ToString() + " of type argument " + tyArg.ToString() + " does not match expected kind " + opDom.ToString(), rng]
            let! normTy, normBot, normJoin, normDelta, normIso = withError errorMsg rng (kCheckSemilattice tenv (Ty.normalize(tenv.tyAliasEnv, ty)))
            return (normTy, normBot, normJoin, normDelta, normIso)
        }
            
and kCheckProset (tenv : TypeEnvironment) (ty : Ty) : Check<P.Ty> =
    let tyVarEnv, tyBaseEnv, tyAliasEnv = tenv.tyVarEnv, tenv.tyBaseEnv, tenv.tyAliasEnv
    let errorMsg = "Type " + ty.ToString() + " is not a proset"
    match ty with
    | TyId(name,rng) ->
        match tyVarEnv.TryFind(name) with
        | Some(pk) ->
            Result (P.TyVar("$" + name))
        | None ->
            match tyBaseEnv.TryFind(name) with
            | Some( KProper(semPoset,_,_,_) ) ->
                Result (semPoset)
            | Some ( KOperator(_,_,_) ) ->
                failwith "there should be no type operators in the base type environment"
            | None ->
                match tyAliasEnv.TryFind(name) with
                | Some(ty) ->
                    withError errorMsg rng (kCheckProset tenv ty)
                | None ->
                    Error ["type " + name + " not found", rng]  
    | FunTy(dom,q,cod,rng) ->
        check {
            let! pTyDom = withError (errorMsg + ": domain is not a poset") rng (kCheckProset tenv dom)
            let! pTyCod = withError (errorMsg + ": codomain is not a poset") rng (kCheckProset tenv cod)
            return P.Fun(pTyDom, pTyCod)
        }
    | Dictionary(dom, cod, rng) ->
        check {
            let! pTyDom,_ = withError (errorMsg + ": domain is not a toset") rng (kCheckToset tenv dom)
            let! pTyCod = withError (errorMsg + ": codomain is not a poset") rng (kCheckProset tenv cod)
            return P.List(P.Prod(pTyDom,pTyCod))
        }
    | Capsule(tyContents, q, rng) ->
        check {
            let! pTyContents = withError (errorMsg + ": content type is not a poset") rng (kCheckProset tenv tyContents)
            return pTyContents
        }
    | Prod(tyL, tyR, rng) ->
        check {
            let! pTyL = withError (errorMsg + ": left component type is not a poset") rng (kCheckProset tenv tyL)
            let! pTyR = withError (errorMsg + ": right component type is not a poset") rng (kCheckProset tenv tyR)
            return P.Prod(pTyL, pTyR)
        }
    | Sum(tyL, tyR, rng) ->
        check {
            let! pTyL = withError (errorMsg + ": left component type is not a poset") rng (kCheckProset tenv tyL)
            let! pTyR = withError (errorMsg + ": right component type is not a poset") rng (kCheckProset tenv tyR)
            return P.Sum(pTyL, pTyR)
        }
    | IVar(tyContents, rng) ->
        check {
            let! pTyContents,_ = withError (errorMsg + ": content type is not a toset") rng (kCheckToset tenv tyContents)
            return P.List(pTyContents)
        }
    | TyOp(varId, kind, body, rng) ->
        Error [(errorMsg + ": type operators do not denote posets",rng)]
    | ForallTy(varId, kind, body, rng) ->
        check {
            let tenv' = { tenv with tyVarEnv = tenv.tyVarEnv.Add(varId,kind) }
            let! pBodyTy = withError errorMsg rng (kCheckProset tenv' body)
            match kind with
            | Poset ->
                return P.ForallTy("$" + varId, pBodyTy)
            | Toset ->
                let ty = P.TyVar("$" + varId)
                let compTy = Fun(ty,Fun(ty,pBoolTy))
                return P.ForallTy("$" + varId, P.Fun(compTy, pBodyTy))
            | Semilattice ->
                let ty = P.TyVar("$" + varId)
                let tyDelta = P.TyVar("$" + varId + "Delta")
                let joinTy = Fun(ty,Fun(ty,ty))
                let isoTy = Fun(ty, List(tyDelta))
                return P.ForallTy("$" + varId, P.Fun(ty, P.Fun(joinTy, P.ForallTy("$" + varId + "Delta", P.Fun(isoTy, pBodyTy)))))
        }
    | Partial(tyContents,rng) ->
        check {
            let! pTyContents = withError (errorMsg + ": underlying type is not a poset") rng (kCheckProset tenv tyContents)
            return P.Sum(pTyContents, P.Unit)
        }
    | TyApp(tyOp, tyArg, rng) ->
        check {
            // check that forall is type operator and argTy is proper type which matches domain of forall
            let! kOp = withError errorMsg rng (kSynth tenv tyOp)
            let! opDom, _ =
                match kOp with
                | KProper(_,_,_,rngOp) ->
                    Error [errorMsg + ": " + tyOp.ToString() + " is not a type operator", rngOp]
                | KOperator(dom, cod, _) ->
                    Result (dom, cod)
            let! kArg = withError errorMsg rng (kSynth tenv tyArg)
            let! _, _, _ = getProper (tyArg.ToString()) kArg
            let! _ = 
                match hasKind kArg opDom with
                | true -> 
                    Result ()
                | false -> 
                    Error ["kind " + kArg.ToString() + " of type argument " + tyArg.ToString() + " does not match expected kind " + opDom.ToString(), rng]
            let! pTy = withError errorMsg rng (kCheckProset tenv (Ty.normalize(tenv.tyAliasEnv, ty)))
            return pTy
        }    
    
and kSynth (tenv : TypeEnvironment) (ty : Ty) : Check<Kind> =
    let tyVarEnv, tyBaseEnv, tyAliasEnv = tenv.tyVarEnv, tenv.tyBaseEnv, tenv.tyAliasEnv
    let errorMsg = "Type " + ty.ToString() + " is not well-formed"
    match ty with
    | TyId(name,rng) ->
        match tyVarEnv.TryFind(name) with
        | Some(pk) ->
            match pk with
            | Poset ->
                Result (KProper(P.TyVar("$" + name), None, None, noRange))
            | Toset ->
                let semPoset = P.TyVar("$" + name)
                let comp = P.Var("$" + name + "_comp")
                Result (KProper(semPoset, Some(comp), None, noRange))    
            | Semilattice ->
                let semPoset = P.TyVar("$" + name)
                let bot = P.Var("$" + name + "_bot")
                let join = P.Var("$" + name + "_join")
                let tyDelta = Ast.TyId(name + "Delta", noRange)
                let iso = P.Var("$" + name + "_iso")
                Result (KProper(semPoset, None, Some { bot = bot ; join = join ; tyDelta = tyDelta ; iso = iso }, noRange))    
        | None ->
            match tyBaseEnv.TryFind(name) with
            | Some( KProper(_,_,_,_) as k ) ->
                Result k
            | Some ( KOperator(_,_,_) ) ->
                failwith "there should be no type operators in the base type environment"
            | None ->
                match tyAliasEnv.TryFind(name) with
                | Some(ty) ->
                    withError errorMsg rng (kSynth tenv ty)
                | None ->
                    Error ["type " + name + " not found", rng]  
    | FunTy(dom,q,cod,rng) ->
        check {
            let! kDom = withError (errorMsg + ": domain is not well-kinded") rng (kSynth tenv dom)
            let! kCod = withError (errorMsg + ": codomain is not well-kinded") rng (kSynth tenv cod)
            let! pDomTy, _, _ = getProper "domain type" kDom
            let! pCodTy, _, _ = getProper "codomain type" kCod
            return KProper(P.Fun(pDomTy,pCodTy), None, None, noRange)
        }
     | Dictionary(dom, cod, rng) ->
        check {
            let! kDom = withError (errorMsg + ": domain is not a well-kinded") rng (kSynth tenv dom)
            let! kCod = withError (errorMsg + ": codomain is not well-kinded") rng (kSynth tenv cod)
            let! pDomTy, domToset, domSemilat = getProper "domain type" kDom
            let! pCodTy, codToset, codSemilat = getProper "codomain type" kCod
            let! pDomComp = 
                match domToset with
                | Some(comp) -> Result comp
                | None -> Error ["dictionary domain " + dom.ToString() + " is not a toset type",rng]
            match codSemilat with
            | Some({bot = bCod ; join = jCod ; tyDelta = deltaCod ; iso = isoCod }) ->
                let! pCodDelta = kCheckProset tenv deltaCod
                let resTy,_,_,_,_  = makeDictionarySemilat pDomTy pCodTy dom deltaCod pDomComp jCod pCodDelta isoCod
                return KProper(resTy, None, None, noRange)
            | None ->
                let resTy = P.List (P.Prod(pDomTy,pCodTy))
                return KProper(resTy, None, None, noRange)
        }
    | Capsule(tyContents, q, rng) ->
        check {
            // should we generate an error here if q is *?
            let! pTyContents = withError (errorMsg + ": capsule content not a proset") rng (kCheckProset tenv tyContents)
            return KProper(pTyContents, None, None, noRange)
        }
    | Prod(tyL, tyR, rng) ->
        check {
            let! kL = withError (errorMsg + ": left type is not well-kinded") rng (kSynth tenv tyL)
            let! kR = withError (errorMsg + ": right type is not well-kinded") rng (kSynth tenv tyR)
            let! pTyL, optTosetL, optSemilatL = getProper "left type" kL
            let! pTyR, optTosetR, optSemilatR = getProper "right type" kR
            let pTy = P.Prod(pTyL, pTyR)
            let semToset = 
                match optTosetL, optTosetR with
                | Some(compL), Some(compR) ->
                    let _, comp = makeProdToset pTyL compL pTyR compR
                    Some(comp)
                | _ ->
                    None
            let! semSemilat =
                match optSemilatL, optSemilatR with
                | Some({bot = botL ; join = joinL ; tyDelta = deltaL ; iso = isoL }), Some({bot = botR ; join = joinR ; tyDelta = deltaR ; iso = isoR }) ->
                    check {
                        let! pDeltaL = kCheckProset tenv deltaL
                        let! pDeltaR = kCheckProset tenv deltaR
                        let _, bot, join, delta, iso = makeProdSemilat pTyL pTyR botL botR joinL joinR deltaL deltaR pDeltaL pDeltaR isoL isoR
                        return (Some {bot = bot; join = join ; tyDelta = delta ; iso = iso })
                    }
                | _ ->
                    Result None
            return KProper(pTy, semToset, semSemilat, noRange)
        }
    | Sum(tyL, tyR, rng) ->
        check {
            let! kL = withError (errorMsg + ": left type is not well-kinded") rng (kSynth tenv tyL)
            let! kR = withError (errorMsg + ": right type is not well-kinded") rng (kSynth tenv tyR)
            let! pTyL, optTosetL, optSemilatL = getProper "left type" kL
            let! pTyR, optTosetR, optSemilatR = getProper "right type" kR
            let pTy = P.Sum(pTyL, pTyR)
            let semToset = 
                match optTosetL, optTosetR with
                | Some(compL), Some(compR) ->
                    let _, comp = makeSumToset pTyL compL pTyR compR
                    Some(comp)
                | _ ->
                    None
            return KProper(pTy, semToset, None, noRange)
        }
    | IVar(elemTy, rng) ->
        check {
            let! pElemTy, pComp = withError (errorMsg + ": underlying type is not totally ordered") rng (kCheckToset tenv elemTy)
            let resTy, bot, join, delta, iso  = makeIVarSemilat elemTy pElemTy pComp
            return KProper(resTy, None, Some({bot = bot ; join = join ; tyDelta = delta ; iso = iso}), noRange) 
        }
    | TyOp(varId, kind, body, rng) ->
        // this case is purely for checking - we don't actually generate semantics 
        // of forall types until they are applied. However, we will still need to build some stub semantics 
        // to leverage other code.
        check {
            //let kDom = 
            //    match kind with
            //    | Poset ->
            //        KProper(P.Unit, None, None, noRange)
            //    | Semilattice ->
            //        KProper(P.Unit, None, Some({ bot = P.PrimUnitVal ; join = P.PrimUnitVal }), noRange)
            //    | Toset ->
            //        KProper(P.Unit, Some(P.PrimUnitVal), None, noRange)
            let! kCod = withError (errorMsg + ": body not well-formed") rng (kSynth {tenv with tyVarEnv = tyVarEnv.Add(varId,kind)} body)
            return KOperator(kind,kCod,noRange)
        }
    | ForallTy(varId, kind, body, rng) ->
        check {
            let! kCod = withError (errorMsg + ": body not well-formed") rng (kSynth {tenv with tyVarEnv = tyVarEnv.Add(varId,kind)} body)
            let! pBodyTy,_,_ = getProper "forall body" kCod
            match kind with
            | Poset ->
                let pTy = P.ForallTy("$" + varId, pBodyTy)
                return (KProper(pTy, None, None, noRange))
            | Toset ->
                let ty = P.TyVar("$" + varId)
                let compTy = Fun(ty,Fun(ty,pBoolTy))
                let pTy = P.ForallTy("$" + varId, P.Fun(compTy, pBodyTy))
                return (KProper(pTy,None,None,noRange))
            | Semilattice ->
                let ty = P.TyVar("$" + varId)
                let tyDelta = P.TyVar("$" + varId + "Delta")
                let joinTy = Fun(ty,Fun(ty,ty))
                let isoTy = Fun(ty, List(tyDelta))
                let pTy = P.ForallTy("$" + varId, P.Fun(ty, P.Fun(joinTy, P.ForallTy("$" + varId + "Delta", P.Fun(isoTy, pBodyTy)))))
                return KProper(pTy,None,None,noRange)
        }
    | Partial(tyContents, rng) ->
        check {
            let! k = withError errorMsg rng (kSynth tenv tyContents)
            let! resTy, optToset, optSemi = getProper "underlying type" k
            let! semi = 
                match optSemi with
                | Some {bot = bot'; join = join' ; tyDelta = delta' ; iso = iso'} ->
                    check {
                        let! pDelta' = kCheckProset tenv delta' 
                        let _, bot, join, delta, iso = makePartialSemilat tyContents resTy delta' pDelta' bot' join' iso'
                        return (Some {bot = bot; join = join; tyDelta = delta ; iso = iso })
                    }
                | None ->
                    Result None
            return KProper(P.Sum(resTy, Unit), None, semi, noRange)
        }
    | TyApp(forallTy, argTy, rng) ->
        check {
            // check that forall is type operator and argTy is proper type which matches domain of forall
            let! kOp = withError errorMsg rng (kSynth tenv forallTy)
            let! opDom, opCod =
                match kOp with
                | KProper(_,_,_,rngOp) ->
                    Error [errorMsg + ": " + forallTy.ToString() + " is not a type operator", rngOp]
                | KOperator(dom, cod, rng) ->
                    Result (dom, cod)
            let! kArg = withError errorMsg rng (kSynth tenv argTy)
            let! pArgTy, optArgToset, optArgSemi = getProper (argTy.ToString()) kArg
            let! _ = 
                match hasKind kArg opDom with
                | true -> 
                    Result ()
                | false -> 
                    Error ["kind " + kArg.ToString() + " of type argument " + argTy.ToString() + " does not match expected kind " + opDom.ToString(), rng]
            // compute semantics
            let! k = kSynth tenv (Ty.normalize(tenv.tyAliasEnv, ty))
            return k
        }
