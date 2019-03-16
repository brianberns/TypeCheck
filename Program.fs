type Term =
    | True
    | False
    | Zero
    | IfThenElse of (Term * Term * Term)
    | Succ of Term
    | Pred of Term
    | IsZero of Term
    | Var of string
    | Let of (string * Term * Term)

type TermEnv = List<string * Term>

module Term =

    let addTerm (env : TermEnv) name term : TermEnv =
        (name, term) :: env

    let rec getTerm (env : TermEnv) name =
        match env with
            | [] -> Error <| sprintf "Variable not found: %s" name
            | ((name', term) :: tail) ->
                if name' = name then Ok term
                else getTerm tail name

    let rec eval (env : TermEnv) term  =

        let eval' = eval env

        let simplify term =
            match eval' term with
                | Ok term' ->
                    if term' = term then
                        Error <| sprintf "Could not simplify term: %A" term
                    else Ok term'
                | err -> err

        match term with
            | True -> Ok True
            | False -> Ok False
            | Zero -> Ok Zero
            | IfThenElse (True, t2, t3) -> eval' t2
            | IfThenElse (False, t2, t3) -> eval' t3
            | IfThenElse (t1, t2, t3) ->
                simplify t1
                    |> Result.bind (fun t' ->
                        eval' <| IfThenElse (t', t2, t3))
            | Succ t1 ->
                eval' t1
                    |> Result.map Succ
            | Pred Zero -> Ok Zero
            | Pred (Succ k) -> eval' k
            | Pred t1 ->
                simplify t1
                    |> Result.bind (fun t' ->
                        eval' <| Pred t')
            | IsZero Zero -> Ok True
            | IsZero (Succ t) -> Ok False
            | IsZero t1 ->
                simplify t1
                    |> Result.bind (fun t' ->
                        eval' <| IsZero t')
            | Var v -> getTerm env v
            | Let (name, term1, term2) ->
                eval' term1
                    |> Result.bind (fun term1' ->
                        let env = addTerm env name term1'
                        eval env term2)

type Type =
    | Bool
    | Nat

type TypeEnv = List<string * Type>

module Type =

    let addType (env : TypeEnv) name typ : TypeEnv =
        (name, typ) :: env

    let rec getType (env : TypeEnv) name =
        match env with
            | [] -> Error <| sprintf "Type not found: %s" name
            | ((name', typ) :: tail) ->
                if name' = name then Ok typ
                else getType tail name

    let rec typeOf (env : TypeEnv) term =

        let typeOf' = typeOf env

        match term with
            | True
            | False -> Ok Bool
            | Zero -> Ok Nat
            | IfThenElse (term1, term2, term3) ->
                typeOf' term1
                    |> Result.bind (function
                        | Bool ->
                            let typ2 = typeOf' term2
                            let typ3 = typeOf' term3
                            if typ2 = typ3 then typ2
                            else Error <| sprintf "Types mismatch: %A and %A" typ2 typ3
                        | _ -> Error "Unsupported type for IfThenElse")
            | Succ k ->
                typeOf' k
                    |> Result.bind (function
                        | Nat -> Ok Nat
                        | typ -> Error <| sprintf "Unsupported type for Succ: %A" typ)
            | Pred k ->
                typeOf' k
                    |> Result.bind (function
                        | Nat -> Ok Nat
                        | typ -> Error <| sprintf "Unsupported type for Pred: %A" typ)
            | IsZero k ->
                typeOf' k
                    |> Result.bind (function
                        | Nat -> Ok Bool
                        | typ -> Error <| sprintf "Unsupported type for IsZero: %A" typ)
            | Var name -> getType env name
            | Let (name, term1, term2) ->
                typeOf' term1
                    |> Result.bind (fun typ1 ->
                        let env = addType env name typ1
                        typeOf env term2)

[<EntryPoint>]
let main argv =

    let typeEnv =
        [
            "a", Nat
            "b", Nat
            "c", Bool
        ] |> Seq.fold (fun env (name, typ) ->
            Type.addType env name typ) []
    printfn ""
    printfn "Types"
    for pair in typeEnv |> List.rev do
        printfn "%A" pair

    let termEnv =
        [
            "a", Zero
            "b", Succ Zero
            "c", False
        ] |> Seq.fold (fun env (name, term) ->
            Term.addTerm env name term) []
    printfn ""
    printfn "Terms"
    for pair in termEnv |> List.rev do
        printfn "%A" pair

    let terms =
        [
            IfThenElse (True, Var "a", Var "b")
        ]
    for term in terms do
        printfn ""
        printfn "%A" term
        printfn "Type: %A" <| Type.typeOf typeEnv term
        printfn "Eval: %A" <| Term.eval termEnv term
    0
