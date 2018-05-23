open System
open Lexer
open Microsoft.FSharp.Text.Lexing
open Microsoft.FSharp.Text.Parsing
open Microsoft.FSharp.Text.Parsing.ParseHelpers
open System.IO
open Parser
open Typecheck
open Ast
open System
open Kindcheck
open CheckComputation
open PCF

module P = PCF

let goneWrong = "This program has 'gone wrong'. Oops."

let joinNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let joinNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                P.PrimNatVal(Math.Max(m,n))
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("joinNat'", P.Prim("Nat"), P.Prim("Nat"), joinNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let primJoinNat = P.PrimFun("joinNat", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), joinNat)

let lessNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let joinNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                if m < n then
                    pcfTrue
                else
                    pcfFalse
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("lessNat'", P.Prim("Nat"), P.Prim("Nat"), joinNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let primLessNat = P.PrimFun("lessNat", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.pBoolTy), lessNat)

let joinBool (t : P.Term)  =
    match t with
    | PCFBool(a) ->
        let joinBool' (s : P.Term) =
            match s with
            | PCFBool(b) ->
                makePcfBool (a || b)
        P.Abs("b", P.pBoolTy, P.App(P.PrimFun("joinBool'", P.pBoolTy, P.pBoolTy, joinBool'), P.Var("b")))

let primJoinBool = P.PrimFun("joinBool", P.pBoolTy, P.Fun(P.pBoolTy, P.pBoolTy), joinBool)

let lessBool (t : P.Term)  =
    match t with
    | PCFBool(a) -> //false
        let lessBool' (s : P.Term) : P.Term =
            match s with
            | PCFBool(b) ->
                makePcfBool (a = false && b = true)
        P.Abs("b", P.pBoolTy, P.App(P.PrimFun("lessBool'", P.pBoolTy, P.pBoolTy, lessBool'), P.Var("b")))

let primLessBool = P.PrimFun("lessBool", P.pBoolTy, P.Fun(P.pBoolTy, P.pBoolTy), lessBool)

let joinUnit (t : P.Term)  =
    match t with
    | P.PrimUnitVal ->
        let joinUnit' (s : P.Term) =
            match s with
            | P.PrimUnitVal ->
                P.PrimUnitVal
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("b", P.pUnitTy, P.App(P.PrimFun("jUnit'", P.pUnitTy, P.pUnitTy, joinUnit'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let primJoinUnit = P.PrimFun("joinUnit", P.pUnitTy, P.Fun(P.pUnitTy, P.pUnitTy), joinBool)

let lessUnit (t : P.Term)  =
    match t with
    | P.PrimUnitVal ->
        let lessUnit' (s : P.Term) =
            match s with
            | P.PrimUnitVal ->
                pcfFalse
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("b", P.pUnitTy, P.App(P.PrimFun("<'", P.pUnitTy, P.pBoolTy, lessUnit'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let primLessUnit = P.PrimFun("lessUnit", P.pUnitTy, P.Fun(P.pUnitTy, P.pBoolTy), lessUnit)

let baseTyMap =
    Map<string, Kind>(
        [("Nat", KProper(
                    P.Prim("Nat"), 
                    Some(primLessNat), 
                    Some { bot = PrimNatVal(0) ; join = primJoinNat }, 
                    noRange));

         ("Unit", KProper(
                    P.Unit,
                    Some(primLessUnit),
                    Some{bot = PrimUnitVal ; join = primJoinUnit },
                    noRange));

         ("Bool", KProper(
                    P.Sum(P.Unit, P.Unit),
                    Some(primLessBool),
                    Some{bot = makePcfBool false ; join = primJoinBool},
                    noRange))])
 
let plus (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let plus' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n + m)
            | _ ->
                failwith goneWrong
        P.PrimFun("plus'", P.Prim("Nat"), P.Prim("Nat"), plus')
    | _ ->
        failwith goneWrong

let primPlus = P.PrimFun("plus", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), plus)

let mult (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let mult' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n * m)
            | _ ->
                failwith goneWrong
        P.PrimFun("mult'", P.Prim("Nat"), P.Prim("Nat"), mult')
    | _ ->
        failwith goneWrong

let primMult = P.PrimFun("mult", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), mult)

let minus (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let minus' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n - m)
            | _ ->
                failwith goneWrong
        P.PrimFun("minus'", P.Prim("Nat"), P.Prim("Nat"), minus')
    | _ ->
        failwith goneWrong

let primMinus = P.PrimFun("minus", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), minus)

let bAnd (t1 : P.Term) : P.Term =
    match t1 with
    | PCFBool(a) ->
        let and' (t2 : P.Term) =
            match t2 with
            | PCFBool(b) ->
                makePcfBool (a && b)
        P.PrimFun("and'", P.pBoolTy, P.pBoolTy, and')

let primAnd = P.PrimFun("bAnd", P.pBoolTy, P.Fun(P.pBoolTy, P.pBoolTy), bAnd)

let bOr (t1 : P.Term) : P.Term =
    match t1 with
    | PCFBool(a) ->
        let or' (t2 : P.Term) =
            match t2 with
            | PCFBool(b) ->
                makePcfBool (a || b)
        P.PrimFun("or'", P.pBoolTy, P.pBoolTy, or')

let primOr = P.PrimFun("bOr", P.pBoolTy, P.Fun(P.pBoolTy, P.pBoolTy), bOr)

let bNot (t1 : P.Term) : P.Term =
    match t1 with
    | PCFBool(a) ->
        makePcfBool (not a)

let primNot = P.PrimFun("bNot", P.pBoolTy, P.pBoolTy, bNot)

let leq (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let leq' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                makePcfBool (n <= m)
            | _ ->
                failwith goneWrong
        P.PrimFun("leq'", P.Prim("Nat"), P.pBoolTy, leq')
    | _ ->
        failwith goneWrong

let primLeq = P.PrimFun("leq", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.pBoolTy), leq)

let geq (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let geq' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                makePcfBool (n >= m)
            | _ ->
                failwith goneWrong
        P.PrimFun("geq'", P.Prim("Nat"), P.pBoolTy, geq')
    | _ ->
        failwith goneWrong

let primGeq = P.PrimFun("geq", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.pBoolTy), geq)

let baseVEnv =
    Map<string, Ast.Ty * P.Term>(
        [("plus", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   primPlus))
         ("mult", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   primMult))
         ("minus",(FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("Nat", noRange), noRange), noRange),
                   primMinus))
         ("bAnd", (FunTy(TyId("Bool",noRange), CoeffectMonotone, FunTy(TyId("Bool",noRange), CoeffectMonotone, TyId("Bool", noRange), noRange), noRange),
                   primAnd))
         ("bOr", (FunTy(TyId("Bool",noRange), CoeffectMonotone, FunTy(TyId("Bool",noRange), CoeffectMonotone, TyId("Bool", noRange), noRange), noRange),
                  primOr))
         ("bNot", (FunTy(TyId("Bool",noRange), CoeffectAntitone, TyId("Bool",noRange), noRange),
                   primNot))
         ("leq", (FunTy(TyId("Nat",noRange), CoeffectAntitone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Bool", noRange), noRange), noRange),
                  primLeq))
         ("geq", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("Bool", noRange), noRange), noRange),
                  primGeq))
         //("eq", (FunTy(TyId("Nat",noRange), CoeffectAny, FunTy(TyId("Nat",noRange), CoeffectAny, TyId("Bool", noRange), noRange), noRange))
        // TODO: we need primitive unit values in syntax
         ("unit", (TyId("Unit", noRange),
                  P.PrimUnitVal))] 
        
    )

let tenv = { tyVarEnv = Map.empty ; tyBaseEnv = baseTyMap; tyAliasEnv = Map.empty }
let ctxt = { tenv = tenv ; venv = Map.empty ; bvenv = baseVEnv}

let rec printStack (stack : List<string*Range>) =
    match stack with
    | (error,(startPos,_)) ::  rest ->
        let location = "line: " + startPos.Line.ToString() + " column: " + startPos.Column.ToString() 
        printfn ("%s\n  %s\n") location error
        printStack rest
    | [] ->
        ()

[<EntryPoint>]
let main argv =
    try 
        let reader = new StreamReader(argv.[0])
        let lexbuffer : LexBuffer<char> = LexBuffer.FromString(reader.ReadToEnd())
        let ty = 
          try 
            Parser.start(Lexer.token) lexbuffer
          with
          | e ->
            let message = e.Message
            printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) lexbuffer.StartPos.Column
            exit 1
        
        match progCheck ctxt ty with
        | Error(stack) ->
            printStack stack
        | Result(ty,R,pTerm) ->
            let mapCoeffectEntry (id : string) (q: Coeffect) =
                q.ToString() + " " + id
            let stringEntriesR = (Map.toList (Map.map mapCoeffectEntry R))
            let stringR = String.concat ", " (List.map (fun (_,v) -> v) stringEntriesR)
            let result = normalize pTerm
            printf "Successfully checked program.\nType: %s\nCoeffect: %s\nValue: %s\n" (ty.ToString()) stringR (result.ToString())
        0 // return an integer exit code
    with 
    | :? IndexOutOfRangeException ->
        printfn "provide the name of a text file as the command line argument"
        1
    | :? FileNotFoundException ->
        printfn "file not found"
        1