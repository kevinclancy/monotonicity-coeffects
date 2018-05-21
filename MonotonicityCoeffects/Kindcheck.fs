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
let BoolCase = P.BoolCase
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
        Result (semPoset, semToset, semSemilat)
    | _ ->
        Error [role + " does not have a proper kind", noRange]



type Range = Position * Position

 type KindSynthResult =
    | Success of result : Kind
    | Failure of stack : List<string*Range>

 let makeDictionarySemilat(pDomTy : P.Ty) (pCodTy : P.Ty) (pDomComp : P.Term) (jCod : P.Term) =
    let resTy = P.List (P.Prod(pDomTy, pCodTy))
    let elemTy = pCodTy
    resTy,
    P.EmptyList,
    P.LetRec("!f", "!x", resTy, P.Fun(resTy,resTy), P.Abs("!y", resTy, 
        P.ListCase(V("!x"), V("!y"), 
            P.Abs("!xh", elemTy, P.Abs("!xt", resTy, 
                P.ListCase(V("!y"), V("!x"), P.Abs("!yh", elemTy, P.Abs("!yt", resTy, 
                    P.BoolCase(P.App(P.App(pDomComp, P.Proj1(V("!xh"))), P.Proj1(V("!yh"))),
                        P.Cons(P.Var("!xh"), P.App(P.App(V("!f"), V("!xt")), V("!y"))),
                        P.BoolCase(P.App(P.App(pDomComp, P.Proj1(V("!yh"))), P.Proj1(V("!xh"))),
                            P.Cons(P.Var("!yh"), P.App(P.App(V("!f"), V("!x")), V("!yt"))),
                            P.Cons(P.Pair(P.Proj1(V("!xh")), P.App(P.App(jCod,P.Proj2(V("!xh"))),P.Proj2(V("!yh")))), 
                                    P.App(P.App(V("!f"),V("!xt")), V("!yt")))))))))))))

let makeProdSemilat (pTyL : P.Ty) (pTyR : P.Ty) (bL : P.Term) (bR : P.Term) 
                    (jL : P.Term) (jR : P.Term) =
    let resTy = P.Prod(pTyL, pTyR)
    let resBot = P.Pair(bL, bR)
    let resJoin = P.Abs("!x", resTy, P.Abs("!y", resTy, 
                    P.Pair(P.App(P.App(jL, P.Proj1(V("!x"))),P.Proj1(V("!y"))),
                            P.App(P.App(jR,P.Proj2(V("!x"))), P.Proj2(V("!y"))))))    
    resTy, resBot, resJoin

let makeIVarSemilat (elemTy : P.Ty) (elemComp : P.Term) =
    let resTy = P.List elemTy
    resTy,
    EmptyList,
    P.LetRec("!f", "!x", resTy, P.Fun(resTy,resTy), P.Abs("!y", resTy, 
        P.ListCase(V("!x"), V("!y"), 
            P.Abs("!xh", elemTy, P.Abs("!xt", resTy, 
                P.ListCase(V("!y"), V("!x"), P.Abs("!yh", elemTy, P.Abs("!yt", resTy, 
                    P.BoolCase(P.App(P.App(elemComp, P.Proj1(V("!xh"))), P.Proj1(V("!yh"))),
                        P.Cons(P.Var("!xh"), P.App(P.App(V("!f"), V("!xt")), V("!y"))),
                        P.BoolCase(P.App(P.App(elemComp, P.Proj1(V("!yh"))), P.Proj1(V("!xh"))),
                            P.Cons(V("!yh"), P.App(P.App(V("!f"), V("!x")), V("!yt"))),
                            P.Cons(V("!xh"), P.App(P.App(V("!f"),V("!xt")), V("!yt")))))))))))))

let makePartialSemilat (ty : P.Ty) (bot : P.Term) (join : P.Term) =
    let resTy = P.Sum(ty, P.Unit)
    resTy,
    P.In1(bot),
    P.Abs("!x", resTy, P.Abs("!y", resTy, 
        P.SumCase(V("!x"), 
            P.Abs("!x'", ty, 
                P.SumCase(V("!y"), 
                    P.Abs("!y'", ty, P.In1(P.App(P.App(join, V("!x'")), V("!y'")))),
                    P.In2(P.PrimUnitVal))),
            P.Abs("!x'", P.Unit, P.In2(P.PrimUnitVal)))))

let makeProdToset (pTyL : P.Ty) (compL : P.Term) (pTyR : P.Ty) (compR : P.Term) =
    let resTy = P.Prod(pTyL, pTyR)
    resTy,
    P.Abs("!x", resTy, P.Abs("!y", resTy, P.BoolCase(P.App(P.App(compL, P.Proj1(P.Var("!x"))),P.Proj1(P.Var("!y"))),
                                                    P.BBTrue,
                                                    P.App(P.App(compR, P.Proj2(P.Var("!x"))),P.Proj2(P.Var("!y"))))))

let makeSumToset (pTyL : P.Ty) (compL : P.Term) (pTyR : P.Ty) (compR : P.Term) =
    let resTy = P.Sum(pTyL, pTyR)
    resTy,
    P.Abs("!x", resTy, P.Abs("!y", resTy, 
        P.SumCase(P.Var("!x"), 
                P.Abs("!x'", pTyL, P.SumCase(P.Var("!y"), P.Abs("!y'", pTyL, P.App(P.App(compL,P.Var("!x'")), P.Var("!y'"))), BBFalse)),
                P.Abs("!x'", pTyR, P.SumCase(P.Var("!y"), P.Abs("!y'", pTyR, P.App(P.App(compR,P.Var("!x'")), P.Var("!y'"))), BBFalse)))))          

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
and kCheckSemilattice (tenv : TypeEnvironment) (ty : Ty) : Check<P.Ty * P.Term * P.Term> =
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
                Result (semPoset, bot, join)                
        | None ->
            match tyBaseEnv.TryFind(name) with
            | Some( KProper(semPoset,_,Some({bot = bot ; join = join}),_) ) ->
                Result (semPoset, bot, join)
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
            let! (pCodTy, _, jCod) = withError (errorMsg + ": the domain of a dictionary must be a semilattice") rng (kCheckSemilattice tenv cod)
            let resTy, bRes, jRes = makeDictionarySemilat pDomTy pCodTy pDomComp jCod
            return resTy,bRes,jRes
        }
    | Capsule(ty,q, rng) ->
        Error [errorMsg + ": capsule types are not considered semilattice types", rng]
    | Prod(tyL,tyR, rng) ->
        check {
            let! (tyL, bL, jL) = withError (errorMsg + ": left component is not a semilattice type") rng (kCheckSemilattice tenv tyL)
            let! (tyR, bR, jR) = withError (errorMsg + ": right component is not a semilattice type") rng (kCheckSemilattice tenv tyR)
            let resTy, resBot, resJoin = makeProdSemilat tyL tyR bL bR jL jR
            return resTy, resBot, resJoin
        }
    | Sum(_,_,rng) ->
        Error [(errorMsg + ": sum types are not semilattice types",rng)]
    | IVar(tyContents, rng) ->
        check {
            let! (elemTy, elemComp) = 
                withError (errorMsg + ": the content type of an ivar must be a toset type") rng (kCheckToset tenv tyContents)
            let resTy, resBot, resJoin = makeIVarSemilat elemTy elemComp
            return (resTy, resBot, resJoin)
        }    
    | TyOp(_,_,_,rng) ->
        Error [(errorMsg + ": type operators do not denote semilattices", rng)]
    | ForallTy(varId, kind, body, rng) ->
        Error [(errorMsg + ": forall types do not denote semilattices",rng)]
    | Partial(tyContents,rng) ->
        check {
            let! (ty, bot, join) = withError (errorMsg + ": [ty] is only a semilattice if ty is a semilattice") rng (kCheckSemilattice tenv tyContents)
            let resTy, resBot, resJoin = makePartialSemilat ty bot join
            return (resTy, resBot, resJoin)
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
            let! normTy, normBot, normJoin = withError errorMsg rng (kCheckSemilattice tenv (Ty.normalize(tenv.tyAliasEnv, ty)))
            return (normTy, normBot, normJoin)
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
            return pTyContents
        }
    | TyOp(varId, kind, body, rng) ->
        Error [(errorMsg + ": type operators do not denote posets",rng)]
    | ForallTy(varId, kind, body, rng) ->
        check {
            let tenv' = { tenv with tyVarEnv = tenv.tyVarEnv.Add(varId,kind) }
            let! pBodyTy = withError errorMsg rng (kCheckProset tenv' body)
            return P.ForallTy("$" + varId, pBodyTy)
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
                Result (KProper(semPoset, None, Some { bot = bot ; join = join }, noRange))    
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
            | Some({bot = bCod ; join = jCod}) ->
                let resTy, bot, join = makeDictionarySemilat pDomTy pCodTy pDomComp jCod
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
            let semSemilat =
                match optSemilatL, optSemilatR with
                | Some({bot = botL ; join = joinL }), Some({bot = botR ; join = joinR}) ->
                    let _, bot, join = makeProdSemilat pTyL pTyR botL botR joinL joinR
                    Some({bot = bot; join = join})
                | _ ->
                    None
            return KProper(pTy, semToset, semSemilat, noRange)
        }
    | Sum(tyL, tyR, rng) ->
        check {
            let! kL = withError (errorMsg + ": left type is not well-kinded") rng (kSynth tenv tyL)
            let! kR = withError (errorMsg + ": right type is not well-kinded") rng (kSynth tenv tyR)
            let! pTyL, optTosetL, optSemilatL = getProper "left type" kL
            let! pTyR, optTosetR, optSemilatR = getProper "right type" kR
            let pTy = P.Prod(pTyL, pTyR)
            let semToset = 
                match optTosetL, optTosetR with
                | Some(compL), Some(compR) ->
                    let _, comp = makeSumToset pTyL compL pTyR compR
                    Some(comp)
                | _ ->
                    None
            return KProper(pTy, semToset, None, noRange)
        }
    | IVar(tyContents, rng) ->
        check {
            let! pTy, pComp = withError (errorMsg + ": underlying type is not totally ordered") rng (kCheckToset tenv tyContents)
            let resTy, bot, join = makeIVarSemilat pTy pComp
            return KProper(resTy, None, Some({bot = bot ; join = join}), noRange) 
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
            return KOperator(kind,kCod,noRange)
        }
    | Partial(tyContents, rng) ->
        check {
            let! k = withError errorMsg rng (kSynth tenv tyContents)
            let! resTy, optToset, optSemi = getProper "underlying type" k
            let semi = 
                match optSemi with
                | Some {bot = bot'; join = join'} ->
                    let _, bot, join = makePartialSemilat resTy bot' join' 
                    Some {bot = bot; join = join}
                | None ->
                    None
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
            let! normSynth = kSynth tenv (Ty.normalize(tenv.tyAliasEnv, ty))
            let! normTy, normToset, normSemi = getProper "normalized application" normSynth
            return KProper(normTy, normToset, normSemi, noRange)
        }
