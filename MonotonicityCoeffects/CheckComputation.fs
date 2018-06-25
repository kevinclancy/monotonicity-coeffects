module CheckComputation

open Microsoft.FSharp.Text.Lexing

type Range = Position * Position

let noPos : Position = {
    pos_fname = ""
    pos_lnum = 0
    pos_bol = 0
    pos_cnum = 0
}

let noRange = (noPos, noPos)

type Check<'A> =
    | Error of List<string * Range>
    // | ValidPendingError of msg : string * rng : Range
    | Result of result : 'A

type CheckBuilder () =
    member x.Bind(comp : Check<'A>, func : 'A -> Check<'B>) =
        match comp with
        | Error(stack) ->
            Error(stack)
        | Result(r) ->
            func r

    member x.Return(value : 'A) : Check<'A> =
        Result(value)

let withError (msg : string) (rng : Range) (comp : Check<'A>) : Check<'A> =
    match comp with
    | Error(stack) ->
        Error( (msg,rng) :: stack )
    | Result(r) ->
        Result(r)
  
let rec sequence (l : List<Check<Unit>>) : Check<Unit> =
    match l with
    | Error(stack) :: _ ->
        Error(stack)
    | _ :: rest ->
        sequence rest
    | [] ->
        Result ()

// let setError (msg : string) (rng : Range) : Check<Unit> =
//    ValidPendingError(msg, rng)   

let check = new CheckBuilder()