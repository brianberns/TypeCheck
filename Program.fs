type IfThenElse =
    {
        Cond : Expr
        If : Expr
        Else : Expr
    }

/// An expression that can be evaluated.
and Expr =
    | True
    | False
    | Zero
    | IfThenElse of IfThenElse
    | Succ of Expr
    | Pred of Expr
    | IsZero of Expr
    | Var of (string (*variable name*))
    | Let of (string (*variable name*) * Expr (*variable value*) * Expr (*resulting expression*))

type ExprEnv = List<string * Expr>

module Expr =

    let addExpr (env : ExprEnv) name expr : ExprEnv =
        (name, expr) :: env

    let rec getExpr (env : ExprEnv) name =
        match env with
            | [] -> Error <| sprintf "Variable not found: %s" name
            | ((name', expr) :: tail) ->
                if name' = name then Ok expr
                else getExpr tail name

    let rec eval (env : ExprEnv) expr  =

        let eval' = eval env

        let simplify expr =
            match eval' expr with
                | Ok expr' ->
                    if expr' = expr then
                        Error <| sprintf "Could not simplify expr: %A" expr
                    else Ok expr'
                | err -> err

        match expr with
            | True -> Ok True
            | False -> Ok False
            | Zero -> Ok Zero
            | IfThenElse { Cond=True; If=expr; Else=_ } -> eval' expr
            | IfThenElse { Cond=False; If=_; Else=expr } -> eval' expr
            | IfThenElse { Cond=cond; If=ifExpr; Else=elseExpr } ->
                simplify cond
                    |> Result.bind (fun cond' ->
                        eval' <| IfThenElse { Cond=cond'; If=ifExpr; Else=elseExpr })
            | Succ expr ->
                eval' expr
                    |> Result.map Succ
            | Pred Zero -> Ok Zero
            | Pred (Succ expr) -> eval' expr
            | Pred expr ->
                simplify expr
                    |> Result.bind (fun expr' ->
                        eval' <| Pred expr')
            | IsZero Zero -> Ok True
            | IsZero (Succ _) -> Ok False
            | IsZero expr ->
                simplify expr
                    |> Result.bind (fun expr' ->
                        eval' <| IsZero expr')
            | Var name -> getExpr env name
            | Let (name, expr1, expr2) ->
                eval' expr1
                    |> Result.bind (fun expr1' ->
                        let env = addExpr env name expr1'
                        eval env expr2)

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

    let rec typeOf (env : TypeEnv) expr =

        let typeOf' = typeOf env

        match expr with
            | True
            | False -> Ok Bool
            | Zero -> Ok Nat
            | IfThenElse { Cond=expr1; If=expr2; Else=expr3 } ->
                typeOf' expr1
                    |> Result.bind (function
                        | Bool ->
                            let typ2 = typeOf' expr2
                            let typ3 = typeOf' expr3
                            if typ2 = typ3 then typ2
                            else Error <| sprintf "Type mismatch: %A and %A" typ2 typ3
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
            | Let (name, expr1, expr2) ->
                typeOf' expr1
                    |> Result.bind (fun typ1 ->
                        let env = addType env name typ1
                        typeOf env expr2)

[<EntryPoint>]
let main argv =

    let typeEnv =
        [
            "zero", Nat
            "one", Nat
            "never", Bool
        ] |> Seq.fold (fun env (name, typ) ->
            Type.addType env name typ) []
    printfn ""
    printfn "Types"
    for pair in typeEnv |> List.rev do
        printfn "%A" pair

    let exprEnv =
        [
            "zero", Zero
            "one", Succ Zero
            "never", False
        ] |> Seq.fold (fun env (name, expr) ->
            Expr.addExpr env name expr) []
    printfn ""
    printfn "Exprs"
    for pair in exprEnv |> List.rev do
        printfn "%A" pair

    let exprs =
        [
            IfThenElse { Cond=True; If=Var "zero"; Else=Var "one" }
            IfThenElse { Cond=True; If=Var "zero"; Else=Var "never" }
            IfThenElse { Cond=True; If=False; Else=Var "never" }
            IfThenElse { Cond=Zero; If=Zero; Else=Zero }
        ]
    for expr in exprs do
        printfn ""
        printfn "%A" expr
        printfn "Type: %A" <| Type.typeOf typeEnv expr
        printfn "Eval: %A" <| Expr.eval exprEnv expr
    0
