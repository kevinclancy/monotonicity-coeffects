module CheckComputation

// I don't actually use this very much: it would have been more useful if I had written this *before* the type-checking code

open Microsoft.FSharp.Text.Lexing

type Range = Position * Position

type Check<'A> =
    | Error of List<string * Range>
    | Result of 'A

type CheckBuilder () =
    member x.Bind(comp : Check<'A>, func : 'A -> Check<'B>) =
        match comp with
        | Error(stack) ->
            Error(stack)
        | Result(r) ->
            func r
    
    member x.Return(value : 'A) : Check<'A> =
        Result(value)

let check = new CheckBuilder()