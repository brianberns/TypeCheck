﻿(*
 * Based on _Types and Programming Languages_
 * https://www.cis.upenn.edu/~bcpierce/tapl/
 *)

open System

/// Abstract syntax for lambda calculus.
[<StructuredFormatDisplay("{String}")>]
type Term =

    /// e.g. "x", but using de Bruijn index instead of actual name
    | Variable of int

    /// E.g. "λx.x", which is λ.0 using de Bruijn indexes
    | Abstraction of Term

    /// E.g. "(x y)"
    | Application of (Term * Term)

    /// Converts term to string.
    member this.String =

        let nLevels =
            let rec depth = function
                | Variable _ -> 0
                | Application (func, arg) ->
                    max (depth func) (depth arg)
                | Abstraction body ->
                    depth body + 1
            depth this

        let toParam index =
            char (((nLevels - index - 1 + 26) % 26) + int 'a') |> string

        let rec loop iLevel term =
            match term with
                | Variable index ->
                    toParam (index + nLevels - iLevel)
                | Application (func, arg) ->
                    sprintf "(%s %s)" (loop iLevel func) (loop iLevel arg)
                | Abstraction body ->
                    let param = toParam (nLevels - iLevel - 1)
                    sprintf "λ%s.%s" param (loop (iLevel + 1) body)

        this |> loop 0

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
            | Abstraction t1 ->
                Abstraction (
                    loop (c + 1) d t1)
            | Application (t1, t2) ->
                Application (
                    loop c d t1,
                    loop c d t2)

        term |> loop 0 amount

    /// Interop with F# quotations.
    module private FSharp =

        open Microsoft.FSharp.Quotations.Patterns

        /// Constructs a term from an F# quotation.
        let ofQuot quot =
            let rec loop names = function
                | Var var ->
                    names
                        |> List.findIndex (fun name ->
                            var.Name = name)
                        |> Variable
                | Lambda (param, body) ->
                    let names' = param.Name :: names
                    Abstraction (body |> loop names')
                | Application (func, arg) ->
                    Application (
                        func |> loop names,
                        arg |> loop names)
                | expr -> failwithf "Not supported: %A" expr
            quot |> loop []

    /// Constructs a term from an F# quotation.
    let ofQuot = FSharp.ofQuot

    /// Text parsing.
    module private Parse =

        open FParsec

        type State = List<string (*variable name*)>

        let private parseTerm, private parseTermRef =
            createParserForwardedToRef<Term, State>()

        let private parseName =
            many1Chars (satisfy (fun c ->
                Char.IsLetterOrDigit(c) && (c <> 'λ')))

        let private parseIndex =
            pipe2
                getUserState
                parseName
                (fun names name ->
                    names |> List.findIndex (fun n -> n = name))

        let private parseVariable =
            parseIndex
                |>> Variable

        let private pushName =
            parseName
                >>= (fun param ->
                    updateUserState (fun names -> param :: names))

        let private popName =
            updateUserState List.tail

        let private parseAbstraction =
            pipe4
                (skipAnyOf ['λ'; '^'; '\\'])
                pushName
                (skipChar '.')
                parseTerm
                (fun _ _ _ body ->
                    Abstraction body)
                .>> popName

        let private parseApplication =
            pipe5
                (skipChar '(')
                parseTerm
                (many1 <| skipChar ' ')
                parseTerm
                (skipChar ')')
                (fun _ func _ arg _ ->
                    Application (func, arg))

        do parseTermRef :=
            choice [
                parseVariable
                parseAbstraction
                parseApplication
            ]

        let parse str =
            let parser = !parseTermRef .>> eof   // force consumption of entire string
            match runParserOnString parser [] "" str with
                | Success (term, _, _) -> term
                | Failure (msg, _, _) -> failwith msg

    /// Parses a term from a string.
    let parse = Parse.parse

    /// The substitution of a term s for variable number j in a term t.
    let rec substitute j s t =
        match t with
            | Variable k ->
                if k = j then s
                else t
            | Abstraction t1 ->
                let j' = j + 1
                let s' = shift 1 s
                Abstraction (
                    t1 |> substitute j' s')
            | Application (t1, t2) ->
                Application (
                    t1 |> substitute j s,
                    t2 |> substitute j s)

    /// Is the given term a value?
    let isValue = function
        | Abstraction _ -> true   // call-by-value evaluation stops when it reaches a lambda, so values can be arbitrary lambda-terms
        | _ -> false

    /// Active pattern for values.
    let rec (|Value|_|) term =
        if isValue term then
            Some term
        else None

    /// Fully evaluates the given term, reducing it to normal form.
    let rec eval term =

        /// Reduces a term by one step, if it's not already in normal form.
        let rec step = function

                // try to reduce first term
            | Application (Step t1', t2) ->
                Application (t1', t2) |> Some

                // try to reduce second term if first term is a value
            | Application (Value v1, Step t2') ->
                Application (v1, t2') |> Some

                // function application (beta-reduction)
            | Application (Abstraction t12, Value v2) ->
                t12
                    |> substitute 0 (shift 1 v2)
                    |> shift -1
                    |> Some

                // normal form - no further reduction possible
            | _ -> None

        /// Active pattern for a term that can take a step.
        and (|Step|_|) term =
            step term

            // evaluate the given term recursively, one step at a time
        step term
            |> Option.map (fun term' ->
                eval term')
            |> Option.defaultValue term

[<AutoOpen>]
module Lang =

    let True = <@@ fun x y -> x @@> |> Term.ofQuot
    let False = <@@ fun x y -> y @@> |> Term.ofQuot
    let If = <@@ fun b x y -> b x y @@> |> Term.ofQuot
    let And = sprintf "λp.λq.((p q) %A)" False |> Term.parse
    let Or = sprintf "λp.λq.((p %A) q)" True |> Term.parse

[<EntryPoint>]
let main argv =

    // display λ chars correctly
    Console.OutputEncoding <- Text.Encoding.Unicode

    let terms =
        [
            sprintf "((%A %A) %A)" Or True False
            sprintf "((%A %A) %A)" And True False
            sprintf "(((%A %A) %A) %A)" If True True False
        ] |> Seq.map Term.parse
    for term in terms do
        printfn ""
        printfn "Input:  %A" term
        let term' = Term.eval term
        printfn "Output: %A" term'
        if term' |> Term.isValue |> not then
            printfn "*** ERROR ***"

    0
