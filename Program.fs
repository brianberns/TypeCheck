type Term =
    | True
    | False
    | Zero
    | IfThenElse of (Term * Term * Term)
    | Succ of Term
    | Pred of Term
    | IsZero of Term

let rec eval term =

    let simplify term =
        let term' = eval term
        if term' = term then
            failwithf "Could not simplify term: %A" term
        else term'

    match term with
        | True -> True
        | False -> False
        | Zero -> Zero
        | IfThenElse (True, t2, t3) -> eval t2
        | IfThenElse (False, t2, t3) -> eval t3
        | IfThenElse (t1, t2, t3) ->
            let t' = simplify t1
            eval <| IfThenElse (t', t2, t3)
        | Succ t1 ->
            let t' = simplify t1
            Succ t'
        | Pred Zero -> Zero
        | Pred (Succ k) -> eval k
        | Pred t1 ->
            let t' = simplify t1
            eval <| Pred t'
        | IsZero Zero -> True
        | IsZero (Succ t) -> False
        | IsZero t1 ->
            let t' = simplify t1
            eval <| IsZero t'

type Type =
    | Bool
    | Nat

let rec typeOf =
    function
        | True
        | False -> Ok Bool
        | Zero -> Ok Nat
        | IfThenElse (trm1, trm2, trm3) ->
            typeOf trm1
                |> Result.bind (function
                    | Bool ->
                        let typ2 = typeOf trm2
                        let typ3 = typeOf trm3
                        if typ2 = typ3 then typ2
                        else Error "Types mismatch"
                    | _ -> Error "Unsupported type for IfThenElse")
        | Succ k ->
            typeOf k
                |> Result.bind (function
                    | Nat -> Ok Nat
                    | _ -> Error "Unsupported type for Succ")
        | Pred k ->
            typeOf k
                |> Result.bind (function
                    | Nat -> Ok Nat
                    | _ -> Error "Unsupported type for Pred")
        | IsZero k ->
            typeOf k
                |> Result.bind (function
                    | Nat -> Ok Bool
                    | _ -> Error "Unsupported type for IsZero")

[<EntryPoint>]
let main argv =
    let terms =
        [
            // IfThenElse (Zero, Zero, Zero)
            // IfThenElse (True, Zero, (Succ Zero))
            IfThenElse (False, Zero, (Succ Zero))
        ]
    for term in terms do
        try
            printfn ""
            printfn "%A" term
            printfn "Type: %A" <| typeOf term
            printfn "Eval: %A" <| eval term
        with
            | ex -> printfn "%s" ex.Message
    0
