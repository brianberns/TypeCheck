(*
 * Based on _Types and Programming Languages_
 * https://www.cis.upenn.edu/~bcpierce/tapl/
 *)

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

    let rec eval term  =

        let rec (|NumericValue|_|) = function
            | Zero -> Some Zero
            | Succ (NumericValue nv) -> Some (Succ nv)
            | _ -> None

        let rec step = function

            (* Boolean *)
            | If (True, t2, _) -> t2
            | If (False, _, t3) -> t3
            | If (t1, t2, t3) ->
                let t1' = step t1
                If (t1', t2, t3)

            | Succ t1 ->
                let t1' = step t1
                Succ t1'
            | Pred Zero -> Zero
            | Pred (Succ (NumericValue nv1)) ->
                nv1
            | Pred t1 ->
                let t1' = step t1
                Pred t1'
            | IsZero Zero -> True
            | IsZero (Succ (NumericValue _)) ->
                False
            | IsZero t1 ->
                let t1' = step t1
                IsZero t1'

            (* Normal form *)
            | term -> term

        let term' = step term
        if term' = term then term
        else eval term'

[<EntryPoint>]
let main argv =

    let terms =
        [
            If (True, If (False, False, False), True)
            If (True, True, If (False, False, False))
            Pred (Succ (Pred Zero))
        ]
    for term in terms do
        printfn ""
        printfn "%A" term
        printfn "Eval: %A" <| Term.eval term
    0
