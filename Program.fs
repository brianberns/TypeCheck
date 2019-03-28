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
type Term =

    /// e.g. "x", using de Bruijn index instead of actual name
    | Variable of uint

    /// E.g. "λx.x", which is λ.0 using de Bruijn indexes
    | Abstraction of Term

    /// E.g. "x y"
    | Application of (Term * Term)

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
            | Application (t1, t2) ->
                step t1
                    |> Option.map (fun t1' ->
                        Application (t1', t2))

                // reduce second term if first term is a value
            | Application (Value v1, t2) ->
                step t2
                    |> Option.map (fun t2' ->
                        Application (v1, t2'))

                // function application (beta-reduction)
            | Application (Abstraction t12, Value v2) ->
                t12
                    |> substitute 0u (shift 1 v2)
                    |> shift -1
                    |> Some

                // normal form - no further reduction possible
            | _ -> None

            // evaluate the given term recursively, one step at a time
        step term
            |> Option.map (fun term' ->
                eval term')
            |> Option.defaultValue term

[<AutoOpen>]
module Lang =

    let True = Abstraction (Abstraction (Variable 1u))
    let False = Abstraction (Abstraction (Variable 0u))
    let Or =
        Abstraction (
            Abstraction (
                Application (
                    Application (Variable 1u, True),
                    Variable 0u)))

[<EntryPoint>]
let main argv =
    let terms =
        [
            Application (
                Application (Or, True),
                False)
        ]
    for term in terms do
        printfn ""
        printfn "%A" term
        let term' = Term.eval term
        printfn "Eval: %A" term'
        if term' |> Term.isValue |> not then
            printfn "*** ERROR ***"
    0
