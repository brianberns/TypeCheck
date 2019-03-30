(*
 * Based on _Types and Programming Languages_
 * https://www.cis.upenn.edu/~bcpierce/tapl/
 *)

open System

type Binding = Dummy

type Context = List<string (*variable name*) * Binding>

module Context =

    /// Empty context.
    let empty : Context = []

/// Lambda-calculus with Booleans.
[<StructuredFormatDisplay("{String}")>]
type Term =

    (* Lambda-calculus *)

    /// E.g. "x", but using de Bruijn index instead of actual name.
    | Variable of int

    /// Lambda abstraction (i.e. anonymous function definition).
    /// E.g. "λx.x" (which is λ.0 using de Bruijn indexes).
    | Abstraction of (string (*original parameter name*) * Term (*body*))

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

        let rec loop (ctx : Context) = function
            | Variable index ->
                if index < ctx.Length then
                    fst ctx.[index]
                else
                    (int 'a' + (index - ctx.Length))   // make up a name
                        |> char
                        |> string
            | Application (func, arg) ->
                sprintf "(%s %s)" (loop ctx func) (loop ctx arg)
            | Abstraction (name, body) ->
                let ctx' = (name, Dummy) :: ctx
                sprintf "λ%s.%s" name (loop ctx' body)
            | True -> "True"
            | False -> "False"
            | If (cond, thenBranch, elseBranch) ->
                sprintf "If %A Then %A Else %A"
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
            | Abstraction (name, t1) ->
                Abstraction (
                    name,
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
                    Abstraction (
                        param.Name,
                        body |> loop names')
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
                    updateUserState (fun names -> param :: names)
                        >>% param)

        let private popName =
            updateUserState List.tail

        let private parseAbstraction =
            pipe4
                (skipAnyOf ['λ'; '^'; '\\'])
                pushName
                (skipChar '.')
                parseTerm
                (fun _ param _ body ->
                    Abstraction (param, body))
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
            | Abstraction (name, t1) ->
                let j' = j + 1
                let s' = shift 1 s
                Abstraction (
                    name,
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
        | Abstraction _      // call-by-value evaluation stops when it reaches a lambda, so values can be arbitrary lambda-terms
        | True
        | False -> true
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
            | Application (Abstraction (_, t12), Value v2) ->
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

        /// Active pattern for a term that can take a step.
        and (|Step|_|) term =
            step term

            // evaluate the given term recursively, one step at a time
        step term
            |> Option.map (fun term' ->
                eval term')
            |> Option.defaultValue term

module Lambda =

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
            sprintf "((%A %A) %A)"
                Lambda.Or Lambda.True Lambda.False |> Term.parse
            sprintf "((%A %A) %A)"
                Lambda.And Lambda.True Lambda.False |> Term.parse
            sprintf "(((%A %A) %A) %A)"
                Lambda.If Lambda.True Lambda.True Lambda.False |> Term.parse
            (Application (Variable 0, Variable 1))
            If (True, If (False, False, False), True)
            If (Lambda.True, True, False)
        ]
    for term in terms do
        printfn ""
        printfn "Input:  %A" term
        let term' = Term.eval term
        printfn "Output: %A" term'
        if term' |> Term.isValue |> not then
            printfn "*** ERROR ***"

    0
