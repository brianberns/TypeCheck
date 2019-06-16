(*
 * Based on _Types and Programming Languages_
 * https://www.cis.upenn.edu/~bcpierce/tapl/
 *)

open System

/// Context for a variable, accessed by de Bruijn indexes.
type Context<'a> = List<string (*variable name*) * 'a>

module Context =

    /// Empty context.
    let empty : Context<'a> = []

    /// Adds the given binding to the context.
    let add name value (ctx : Context<_>) : Context<_> =
        (name, value) :: ctx

/// Classification of terms.
[<StructuredFormatDisplay("{String}")>]
type Type =

    /// E.g. True.
    | Boolean

    /// E.g. Boolean -> Boolean.
    | Function of (Type (*input*) * Type (*output*))

    /// Converts type to string.
    member this.String =
        match this with
            | Boolean -> "Boolean"
            | Function (typ1, typ2) ->
                sprintf "(%s -> %s)" typ1.String typ2.String

    /// Converts type to string.
    override this.ToString() = this.String

/// Lambda-calculus with Booleans.
[<StructuredFormatDisplay("{String}")>]
type Term =

    (* Lambda-calculus *)

    /// E.g. "x", but using de Bruijn index instead of actual name.
    | Variable of int

    /// Lambda abstraction (i.e. anonymous function definition).
    /// E.g. "λx.x" (which is λ.0 using de Bruijn indexes).
    | Abstraction of (
        string (*original parameter name*) *
        Type (*type of parameter*) *
        Term (*body*))

    /// Function application. E.g. "(x y)" applies function x to value y.
    | Application of (Term * Term)

    (* Booleans *)

    /// Literal.
    | True

    /// Literal.
    | False

    /// If-then-else expression. E.g. "If b then x else y".
    | If of (Term (*condition*) * Term (*then*) * Term (*else*))

    /// Converts term to string.
    member this.String =

        let rec loop (ctx : Context<_>) = function
            | Variable index ->
                if index < ctx.Length then
                    fst ctx.[index]
                else
                    (int 'a' + (index - ctx.Length))   // make up a name
                        |> char
                        |> string
            | Application (func, arg) ->
                sprintf "(%s %s)" (loop ctx func) (loop ctx arg)
            | Abstraction (name, typ, body) ->
                let ctx' = ctx |> Context.add name ()
                sprintf "λ%s:%A.%s" name typ (loop ctx' body)
            | True -> "True"
            | False -> "False"
            | If (cond, thenBranch, elseBranch) ->
                sprintf "(If %A Then %A Else %A)"
                    cond thenBranch elseBranch

        this |> loop Context.empty

    /// Converts term to string.
    override this.ToString() = this.String

module Term =

    /// Shifts a term by the given amount
    let shift amount term =

        /// The d-place shift of a term above cutoff c.
        let rec loop c (d : int) = function
            | Variable k ->
                Variable (
                    if k < c then k
                    else k + d)
            | Abstraction (name, typ, t1) ->
                Abstraction (
                    name,
                    typ,
                    loop (c + 1) d t1)
            | Application (t1, t2) ->
                Application (
                    loop c d t1,
                    loop c d t2)
            | True -> True
            | False -> False
            | If (t1, t2, t3) ->
                If (
                    loop c d t1,
                    loop c d t2,
                    loop c d t3)

        term |> loop 0 amount

    /// The substitution of a term s for variable number j in a term t.
    let rec substitute j s t =
        match t with
            | Variable k ->
                if k = j then s
                else t
            | Abstraction (name, typ, t1) ->
                let j' = j + 1
                let s' = shift 1 s
                Abstraction (
                    name,
                    typ,
                    t1 |> substitute j' s')
            | Application (t1, t2) ->
                Application (
                    t1 |> substitute j s,
                    t2 |> substitute j s)
            | True -> True
            | False -> False
            | If (t1, t2, t3) ->
                If (
                    t1 |> substitute j s,
                    t2 |> substitute j s,
                    t3 |> substitute j s)

    /// Is the given term a value?
    let isValue = function
        | Abstraction _   // call-by-value evaluation stops when it reaches a lambda abstraction
        | True
        | False -> true
        | _ -> false

    /// Fully evaluates the given term, reducing it to normal form.
    let rec eval term =

        /// Active pattern for a value.
        let rec (|Value|_|) term =
            if isValue term then
                Some term
            else None

        /// Active pattern for a term that can take a step.
        let rec (|Step|_|) term =
            step term

        /// Reduces a term by one step, if it's not already in normal form.
        and step = function

                // try to reduce first term
            | Application (Step t1', t2) ->
                Application (t1', t2) |> Some

                // try to reduce second term if first term is a value
            | Application (Value v1, Step t2') ->
                Application (v1, t2') |> Some

                // function application (beta-reduction)
            | Application (Abstraction (_, _, t12), Value v2) ->
                t12
                    |> substitute 0 (shift 1 v2)
                    |> shift -1
                    |> Some

                // then-branch
            | If (True, t2, _) ->
                Some t2

                // else-branch
            | If (False, _, t3) ->
                Some t3

                // try to reduce conditional
            | If (Step t1', t2, t3) ->
                If (t1', t2, t3) |> Some

                // normal form - no further reduction possible
            | _ -> None

            // evaluate the given term recursively, one step at a time
        step term
            |> Option.map eval
            |> Option.defaultValue term

    /// Determines the type of a term without evaluating it.
    let typeOf term =

        let rec loop (ctx : Context<_>) = function
        
            | True
            | False -> Ok Boolean

                // conditional term must be a boolean and
                // types of the then/else branches must match
            | If (t1, t2, t3) ->
                let typ1Res = t1 |> loop ctx
                let typ2Res = t2 |> loop ctx
                let typ3Res = t3 |> loop ctx
                match (typ1Res, typ2Res, typ3Res) with
                    | (Ok Boolean, Ok typ2, Ok typ3) ->
                        if typ2 = typ3 then
                            Ok typ2
                        else
                            sprintf "Type mismatch: %A and %A" t2 t3 |> Error
                    | (Ok _, Ok _, Ok _) ->
                        sprintf "Not a Boolean: %A" t1 |> Error
                    | (Error msg, _, _) -> Error msg
                    | (_, Error msg, _) -> Error msg
                    | (_, _, Error msg) -> Error msg

            | Variable index ->
                if index < ctx.Length then
                    ctx.[index] |> snd |> Ok
                else
                    Error "Free variable"

                // add parameter type to the context then
                // determine type of body
            | Abstraction (name, paramTyp, body) ->
                let ctx' = ctx |> Context.add name paramTyp
                body
                    |> loop ctx'
                    |> Result.map (fun bodyTyp ->
                        Function (paramTyp, bodyTyp))

                // type of argument must match input type of function
            | Application (func, arg) ->
                let funcTypRes = loop ctx func
                let argTypRes = loop ctx arg
                match (funcTypRes, argTypRes) with
                    | (Ok (Function (funcTypIn, funcTypOut)), Ok argTyp) ->
                        if argTyp = funcTypIn then
                            Ok funcTypOut
                        else
                            sprintf "Type mismatch: %A and %A" funcTypIn argTyp |> Error
                    | (Ok _, Ok _) ->
                        sprintf "Not a function: %A" func |> Error
                    | (Error msg, _) -> Error msg
                    | (_, Error msg) -> Error msg

        term |> loop Context.empty

[<EntryPoint>]
let main argv =

    // display λ chars correctly
    Console.OutputEncoding <- Text.Encoding.Unicode

    let terms =
        [
            True
            If (True, If (False, False, False), True)
            Abstraction ("x", Boolean, Variable 0)
            Abstraction ("x", Function(Boolean, Boolean), Variable 0)
            Application(Abstraction ("x", Boolean, Variable 0), True)
            Application(Abstraction ("x", Boolean, Variable 0), Abstraction ("x", Boolean, Variable 0))
        ]
    for term in terms do
        printfn ""
        printfn "Input: %A" term
        match Term.typeOf term with
            | Ok typ ->
                printfn "Type: %A" typ
                let term' = Term.eval term
                printfn "Output: %A" term'
                if term' |> Term.isValue |> not then
                    printfn "*** ERROR ***"
            | Error msg -> printfn "%s" msg

    0
