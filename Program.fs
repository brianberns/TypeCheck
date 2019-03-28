(*
 * Based on _Types and Programming Languages_
 * https://www.cis.upenn.edu/~bcpierce/tapl/
 *)

/// Make our own default unsigned integer since F# doesn't have one.
type uint = uint32

[<AutoOpen>]
module uint =

    /// Cast to unsigned.
    let uint = uint32

/// Abstract syntax for lambda calculus.
[<StructuredFormatDisplay("{String}")>]
type Term =

    /// e.g. "x", using de Bruijn index instead of actual name
    | Variable of uint

    /// E.g. "λx.x", which is λ.0 using de Bruijn indexes
    | Abstraction of Term

    /// E.g. "x y"
    | Application of (Term * Term)

    /// Converts expression to string.
    member this.String =
        match this with
            | Variable index -> index.ToString()
            | Application (func, arg) -> sprintf "(%A %A)" func arg
            | Abstraction body -> sprintf "λ.%A" body

    /// Converts expression to string.
    override this.ToString() = this.String

module Term =

    /// Shifts a term by the given amount
    let shift amount term =

        /// The d-place shift of a term above cutoff c.
        let rec loop c (d : int) = function
            | Variable k ->
                Variable (
                    if k < c then k
                    else
                        let k' = int k + d
                        if k' < 0 then failwith "Negative index"
                        uint k')
            | Abstraction t1 ->
                Abstraction (
                    loop (c + 1u) d t1)
            | Application (t1, t2) ->
                Application (
                    loop c d t1,
                    loop c d t2)

        term |> loop 0u amount

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
                        |> uint
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

    let ofQuot = FSharp.ofQuot

    /// The substitution of a term s for variable number j in a term t.
    let rec substitute j s t =
        match t with
            | Variable k ->
                if k = j then s
                else t
            | Abstraction t1 ->
                let j' = j + 1u
                let s' = shift 1 s
                Abstraction (
                    t1 |> substitute j' s')
            | Application (t1, t2) ->
                Application (
                    t1 |> substitute j s,
                    t2 |> substitute j s)

    /// Is the given term a value?
    let isValue = function
        | Abstraction _ -> true   // Call-by-value evaluation stops when it reaches a lambda, values can be arbitrary lambda-terms
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

                // reduce first term
            | Application (Step t1', t2) ->
                Application (t1', t2) |> Some

                // reduce second term if first term is a value
            | Application (Value v1, Step t2') ->
                Application (v1, t2') |> Some

                // function application (beta-reduction)
            | Application (Abstraction t12, Value v2) ->
                t12
                    |> substitute 0u (shift 1 v2)
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
    let Or =
        Abstraction (
            Abstraction (
                Application (
                    Application (Variable 1u, True),
                    Variable 0u)))

    /// Inline or.
    let (.||.) t1 t2 =
        Abstraction (
            Abstraction (
                Application (
                    Application (Or, t1),
                    t2)))

[<EntryPoint>]
let main argv =

    // display λ chars correctly
    System.Console.OutputEncoding <- System.Text.Encoding.Unicode

    let terms =
        [
            Application (Application (Or, True), False)
        ]
    for term in terms do
        printfn ""
        printfn "%A" term
        let term' = Term.eval term
        printfn "Eval: %A" term'
        if term' |> Term.isValue |> not then
            printfn "*** ERROR ***"
    0
