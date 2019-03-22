(*
 * Based on _Types and Programming Languages_
 * https://www.cis.upenn.edu/~bcpierce/tapl/
 *)

/// Language syntax.
type Term =

    (* Boolean *)
    | True
    | False
    | If of (Term (*t1*) * Term (*t2*) * Term (*t3*))

    (* Numeric *)
    | Zero
    | Succ of Term
    | Pred of Term
    | IsZero of Term

module Term =

    /// Active pattern for numeric values.
    let rec (|NumericValue|_|) = function
        | Zero -> Some Zero
        | Succ (NumericValue nv) -> Some (Succ nv)
        | _ -> None

    /// Fully evaluates the given term, reducing it to normal form.
    let rec eval term =

        /// Reduces a term by one step, if it's not already in normal form.
        let rec step = function

                // boolean
            | If (True, t2, _) -> Some t2
            | If (False, _, t3) -> Some t3
            | If (t1, t2, t3) ->
                step t1
                    |> Option.map (fun t1' ->
                        If (t1', t2, t3))

                // numeric
            | Succ t1 ->
                step t1
                    |> Option.map (fun t1' ->
                        Succ t1')
            | Pred Zero -> Some Zero
            | Pred (Succ (NumericValue nv1)) ->
                Some nv1
            | Pred t1 ->
                step t1
                    |> Option.map (fun t1' ->
                        Pred t1')
            | IsZero Zero -> Some True
            | IsZero (Succ (NumericValue _)) ->
                Some False
            | IsZero t1 ->
                step t1
                    |> Option.map (fun t1' ->
                        IsZero t1')

                // normal form - no further reduction possible
            | _ -> None

            // evaluate the given term recursively, one step at a time
        step term
            |> Option.map (fun term' ->
                eval term')
            |> Option.defaultValue term

    /// Is the given term a value?
    let isValue = function
        | True
        | False -> true
        | NumericValue _ -> true
        | _ -> false

[<EntryPoint>]
let main argv =

    let terms =
        [
            If (True, If (False, False, False), True)
            If (True, True, If (False, False, False))
            Pred (Succ (Pred Zero))
            If (Zero, Zero, Zero)
        ]
    for term in terms do
        printfn ""
        printfn "%A" term
        let term' = Term.eval term
        printfn "Eval: %A" term'
        if term' |> Term.isValue |> not then
            printfn "*** ERROR ***"
    0
