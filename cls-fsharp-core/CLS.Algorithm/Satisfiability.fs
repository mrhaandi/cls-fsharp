module CLS.Algorithm.Satisfiability

open CLS.Model.ID
open CLS.Model.Type

open Util
open Type
open Subtyping
open Orthogonality
open Matching

/// <summary>
/// Maps a variable id to (set of varible lower bounds, set of varible upper bounds).
/// </summary>
type VariableConstraintSystem = Map<ID, Set<ID> * Set<ID>>

type State = {BasicContraints : BasicConstraintSystem; VariableConstraints: VariableConstraintSystem; Substitution : Substitution; QueuedConstraints : Constraint list; SubstitutableVariables : Map<ID, Variance>; HasChanged : bool} 


/// <summary>
/// Tries to enumerate some substitutions for given constraints (assuming no variable substituted by omega).
/// </summary>
let enumerateSatisfyingSubstitutions (isAtomicSubtype : ID -> ID -> bool) (substitutableVariables : Map<ID, Variance>) (constraints : seq<IntersectionType * IntersectionType>) : seq<Substitution> = 
    
    /// <summary>
    /// Tries deterministically decompose queued constraints.
    /// </summary>
    let decomposeConstraint (state : State) : option<State> =
        state.QueuedConstraints
        |> List.fold ( function
            | None -> (fun _ -> None)
            | Some(state) -> function
                | (l, Intersect(ts)) ->
                    let newConstraints = ts |> Seq.map (fun t -> (l, t)) |> Seq.toList
                    Some({state with QueuedConstraints = newConstraints @ state.QueuedConstraints; HasChanged = true})
                | (Arrow(s1, t1), Arrow(s2, t2)) -> 
                    let newConstraints = [(s2, s1); (t1, t2)]
                    Some({state with QueuedConstraints = newConstraints @ state.QueuedConstraints; HasChanged = true})
                | (Constructor(id1, cvs1), Constructor(id2, cvs2)) -> 
                    if (List.length cvs1) = (List.length cvs2) && isAtomicSubtype id1 id2 then 
                        let newConstraints = List.zip cvs1 cvs2
                        Some({state with QueuedConstraints = newConstraints @ state.QueuedConstraints; HasChanged = true})
                    else None
                //(*
                //filter intersection using isRelated approximation
                | (Intersect(ts) & l, r) -> 
                    match ts |> Seq.filter (fun t1 -> isRelated isAtomicSubtype t1 r) |> intersectSimplifiedTypes with
                    | Intersect(newTs) & newL -> 
                        Some({state with QueuedConstraints = (newL, r) :: state.QueuedConstraints})
                    | newL -> 
                        //Some({state with QueuedConstraints = (l, r) :: state.QueuedConstraints})
                        //printfn "OLD: \n %O\n %O" (Intersect(ts)) r
                        //printfn "NEW: \n %O" l
                        //let kewey = System.Console.ReadKey()
                        Some({state with QueuedConstraints = (newL, r) :: state.QueuedConstraints; HasChanged = true})
                //*)
                | c -> Some({state with QueuedConstraints = c :: state.QueuedConstraints})
                        ) (Some({state with QueuedConstraints = []; HasChanged = false}))
 
    let processPartiallyClosedConstraint (state : State) : option<State> =
        state.QueuedConstraints
        |> List.fold ( function
            | None -> (fun _ -> None)
            | Some(state) -> function
                | (l, r) when not (isPossiblySatisfiable isAtomicSubtype (l, r)) -> None
                | (_, r) when isOmega r -> Some({state with HasChanged = true})
                | (l, _) when isOmega l -> None
                | (l, r) when isSimplifiedSubType isAtomicSubtype l r -> 
                     Some({state with HasChanged = true})
                | (l, r) when isClosed l && isClosed r -> None
                | (Intersect(ts), Arrow(s2, t2)) when isClosed s2 && Set.forall (function | Arrow(s1, t1) -> isClosed s1 | Var(_) -> false | _ -> true) ts ->
                    let targets = Seq.choose (function | Arrow(s1, t1) when isSimplifiedSubType isAtomicSubtype s2 s1 -> Some t1 | _ -> None) ts
                    Some({state with QueuedConstraints = ((intersectSimplifiedTypes targets), t2) :: state.QueuedConstraints; HasChanged = true})
                | (Intersect(ts) & l, Constructor(id2, cvs2) & r) when Set.forall (function | Var(_) -> false | _ -> true) ts ->
                    match cvs2 with
                    | [] -> if isSimplifiedSubType isAtomicSubtype l r then Some({state with HasChanged = true}) else None
                    | _ ->  let argumentLists : IntersectionType list list = 
                                ts
                                |> Seq.choose (function 
                                       | Constructor(id1, cvs1) when List.length cvs1 = List.length cvs2 
                                                                     && isAtomicSubtype id1 id2 -> Some(cvs1)
                                       | _ -> None)
                                |> List.ofSeq
                            if List.isEmpty argumentLists then None
                            else 
                                let newConstraints = List.zip (intersectArgumentLists argumentLists) cvs2
                                Some({state with QueuedConstraints = newConstraints @ state.QueuedConstraints; HasChanged = true})
                | ((Var(x), r) & c) when isClosed r ->
                        let newBounds = 
                            match Map.tryFind x state.BasicContraints with
                            | Some(None, ub) -> Some(None, getInfimumOfSimplifiedTypes [r; ub])
                            | Some(Some(lb), ub) -> 
                                let newUb = getInfimumOfSimplifiedTypes [r; ub]
                                if isSimplifiedSubType isAtomicSubtype lb newUb then
                                    Some(Some(lb), newUb)
                                else None
                            | None -> Some(None, r)
                        match newBounds with
                        | Some(lbo, ub) ->
                                Some({state with BasicContraints = Map.add x (lbo, ub) state.BasicContraints; HasChanged = true})
                        | None -> None
                | (l, Var(x)) when isClosed l ->
                        let newBounds = 
                            match Map.tryFind x state.BasicContraints with
                            | Some(None, ub) -> 
                                if isSimplifiedSubType isAtomicSubtype l ub then
                                    Some(Some(l), ub)
                                else None
                            | Some(Some(lb), ub) -> 
                                let newLb = getSupremumOfSimplifiedTypes isAtomicSubtype [l; lb]
                                if isSimplifiedSubType isAtomicSubtype newLb ub then
                                    Some(Some(newLb), ub)
                                else None
                            | None -> Some(Some(l), Omega)
                        match newBounds with
                        | Some(Some(lb), ub) ->
                                Some({state with BasicContraints = Map.add x (Some(lb), ub) state.BasicContraints; HasChanged = true})
                        | _ -> None
                | c -> Some({state with QueuedConstraints = c :: state.QueuedConstraints})
                        ) (Some({state with QueuedConstraints = []; HasChanged = false}))

    //does not use proper kinding
    let substituteSomeVariables (state : State) : option<State> =
        let mutable newState = {state with HasChanged = false}
        for entry in state.BasicContraints do
            let x = entry.Key
            match entry.Value with
            | (Some(lb), ub) when lb = ub ->
                newState <- {newState with 
                                BasicContraints = Map.remove x newState.BasicContraints; 
                                QueuedConstraints = List.map (fun (l, r) -> (l, r) |>> substituteSimplified (Map.ofList [(x, ub)])) newState.QueuedConstraints; 
                                Substitution = if Map.containsKey x newState.SubstitutableVariables then Map.add x ub newState.Substitution else newState.Substitution;
                                SubstitutableVariables = Map.remove x newState.SubstitutableVariables;
                                HasChanged = true}
            | (_, ub) 
                when let variance = Map.tryFind x state.SubstitutableVariables
                     (variance = Some(Covariant) || variance = Some(UnknownVariance) || variance = None) &&
                        state.QueuedConstraints |> List.forall (fun (l, r) -> 
                            let vl = getVariance x l
                            let vr = getVariance x r
                            (vl = Contravariant || vl = UnknownVariance) && (vr = Covariant || vr = UnknownVariance)) 
                -> newState <- {newState with 
                                    BasicContraints = Map.remove x newState.BasicContraints; 
                                    QueuedConstraints = List.map (fun (l, r) -> (l, r) |>> substituteSimplified (Map.ofList [(x, ub)])) newState.QueuedConstraints; 
                                    Substitution = if Map.containsKey x newState.SubstitutableVariables then Map.add x ub newState.Substitution else newState.Substitution;
                                    SubstitutableVariables = Map.remove x newState.SubstitutableVariables;
                                    HasChanged = true}
            | (Some(lb), _) 
                when let variance = Map.tryFind x state.SubstitutableVariables
                     (variance = Some(Contravariant) || variance = Some(UnknownVariance) || variance = None) &&
                        state.QueuedConstraints |> List.forall (fun (l, r) -> 
                            let vl = getVariance x l
                            let vr = getVariance x r
                            (vl = Covariant || vl = UnknownVariance) && (vr = Contravariant || vr = UnknownVariance)) 
                -> newState <- {newState with 
                                    BasicContraints = Map.remove x newState.BasicContraints; 
                                    QueuedConstraints = List.map (fun (l, r) -> (l, r) |>> substituteSimplified (Map.ofList [(x, lb)])) newState.QueuedConstraints; 
                                    Substitution = if Map.containsKey x newState.SubstitutableVariables then Map.add x lb newState.Substitution else newState.Substitution;
                                    SubstitutableVariables = Map.remove x newState.SubstitutableVariables;
                                    HasChanged = true}
            | _ -> ()
        Some(newState)
    (*
        state.BasicContraints
        |> Map.fold ( function
            | None -> (fun _ -> None)
            | Some(state) -> (fun x -> function
                | (None, ub)
                        ) (Some({state with HasChanged = false}))*)


    let rec updateConstraintSystem : State -> option<State> = 
        let allStateTransformers = [processPartiallyClosedConstraint; decomposeConstraint; substituteSomeVariables; ]
        let rec updateConstraintSystemRec stateTransformers state =
            match stateTransformers with
            | [] -> if (state.QueuedConstraints = []) then Some(state) else None
            | stateTransformer :: remaningTransformers ->
                match stateTransformer state with
                | None -> None
                | Some({HasChanged = true} & newState) -> updateConstraintSystemRec allStateTransformers newState
                | Some(_) -> updateConstraintSystemRec remaningTransformers state
        updateConstraintSystemRec allStateTransformers

    (*
    //preconditions: no variable is matched with omega
    let rec enumerateMatchableSubstitutionsRec (basicContraints : BasicConstraintSystem, 
                                                queuedConstraints : Constraint list) : Substitution seq = 

        match updateConstraintSystem (Map.empty, List.empty) (Seq.toList constraints) with
        | Some(constraintSystem) -> enumerateMatchableSubstitutionsRec constraintSystem
        | None -> Seq.empty*)
    let rec enumerateSubstitutionsRec (state : State) : option<State> = 
        if Map.isEmpty state.SubstitutableVariables then Some(state)
        else
            match Map.tryPick (fun (x : ID) variance -> 
                match (variance, Map.tryFind x state.BasicContraints) with
                | Covariant, None when (state.VariableConstraints |> Map.tryFind x |> Option.forall (fun (_, ub) -> Set.isEmpty ub)) -> 
                    Some({state with Substitution = Map.add x Omega state.Substitution; SubstitutableVariables = Map.remove x state.SubstitutableVariables })
                | Covariant, Some(_, ub) when (state.VariableConstraints |> Map.tryFind x |> Option.forall (fun (_, ub) -> Set.isEmpty ub)) -> 
                    Some({state with Substitution = Map.add x ub state.Substitution; SubstitutableVariables = Map.remove x state.SubstitutableVariables })
                | Contravariant, None -> None
                | Contravariant, Some(Some(lb), _) when (state.VariableConstraints |> Map.tryFind x |> Option.forall (fun (lb, _) -> Set.isEmpty lb)) ->
                    Some({state with Substitution = Map.add x lb state.Substitution; SubstitutableVariables = Map.remove x state.SubstitutableVariables })
                | _ -> None) state.SubstitutableVariables with
            | Some(newState) -> enumerateSubstitutionsRec newState
            | None -> None

    (*
    for c in constraints do
        printfn "%O" c
    printfn ""
    //*)

    let initialState = {
        BasicContraints = Map.empty; 
        VariableConstraints = Map.empty; 
        Substitution = Map.empty; 
        QueuedConstraints = List.ofSeq constraints; 
        SubstitutableVariables = substitutableVariables; 
        HasChanged = false;}


    let initialConstraintSystem = updateConstraintSystem initialState
    match initialConstraintSystem with
    | Some(state) -> 
        match enumerateSubstitutionsRec state with
        | Some(state) -> Seq.singleton state.Substitution
        | None -> Seq.empty
    | None -> Seq.empty