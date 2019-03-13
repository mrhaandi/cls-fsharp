module CLS.Algorithm.Matching

open CLS.Model.ID
open CLS.Model.Type

open Util
open Type
open Subtyping
open Orthogonality


/// <summary>
/// Given a type t, checks whether omega leq! t. If true then returns Some(set of variables that have to be substituted by omega).
/// </summary>
let rec getVariablesToMatchOmega = function
    | t when isOmega t -> Some(Set.empty)
    | Var(_) & v -> Some(Set.singleton v)
    | Arrow(_, t) -> getVariablesToMatchOmega t
    | Intersect(ts) -> 
        Seq.fold (function 
            | Some(accumulatedVars) -> fun t ->
                match getVariablesToMatchOmega t with 
                | Some(vars) -> Some(Set.union accumulatedVars vars)
                | None -> None
            | None -> fun t -> None) (Some(Set.empty)) ts
    | _ -> None //Constructor

/// <summary>
/// (optional lower bound type, upper bound type).
/// </summary>
type BasicConstraint = Option<IntersectionType> * IntersectionType
/// <summary>
/// Maps a variable id to (lower bound type, upper bound type).
/// </summary>
type BasicConstraintSystem = Map<ID, BasicConstraint>

/// <summary>
/// lhs has to be a subtype of rhs.
/// </summary>
type Constraint = IntersectionType * IntersectionType

let tryGetLowerBound (basicCounstraints : BasicConstraintSystem) (variable : ID) =
    match Map.tryFind variable basicCounstraints with
    | Some(Some(lb), _) -> Some(lb)
    | _ -> None


/// <summary>
/// Returns true if every substitution that is allowed in basicConstraintSystem1 is also allowed in basicConstraintSystem2.
/// </summary>
let isBasicConstraintSubsystem (isAtomicSubtype : ID -> ID -> bool) (basicConstraintSystem1 : BasicConstraintSystem) 
    (basicConstraintSystem2 : BasicConstraintSystem) = 
    basicConstraintSystem2 |> Map.forall (fun id -> function
        | (Some(lowerBound2), upperBound2) -> 
            match Map.tryFind id basicConstraintSystem1 with
            | Some(Some(lowerBound1), upperBound1) -> 
                //upper bound check && lower bound check
                (isSubType isAtomicSubtype upperBound1 upperBound2) && (isSubType isAtomicSubtype lowerBound2 lowerBound1)
            | _ -> false
        | (None, upperBound2) -> 
            match Map.tryFind id basicConstraintSystem1 with
            | Some(_, upperBound1) -> isSubType isAtomicSubtype upperBound1 upperBound2
            | _ -> isOmega upperBound2)

/// <summary>
/// Enumerates basic constraint systems that satisty given constraints.
/// </summary>
let enumerateBasicConstraintSystems (isAtomicSubtype : ID -> ID -> bool) : seq<IntersectionType * IntersectionType> -> seq<BasicConstraintSystem> = 
    /// <summary>
    /// Given a type tau, decides whether S(tau) can be arbitrarily large respecting basic constraints.
    /// </summary>
    let rec isArbitrarilyLarge (basicContraints : BasicConstraintSystem) = function
        | t when isOmega t -> true
        | Var(x) -> 
            match Map.tryFind x basicContraints with
            | Some(_, ub) -> isOmega ub
            | None -> true
        | Arrow(_, t) -> isArbitrarilyLarge basicContraints t
        | Intersect(ts) -> Seq.forall (isArbitrarilyLarge basicContraints) ts
        | _ -> false //Constructor
        
    
    /// <summary>
    /// Overapproximates (false positives) whether tau leq! sigma is matchable wrt. basic constraints.
    /// Still misses cases.
    /// </summary>
    let rec isPossiblyMatched (basicContraints : BasicConstraintSystem) = function
        | _, r when isOmega r -> true
        | l, r when isOmega l -> isArbitrarilyLarge basicContraints r
        | Var(x), r -> 
            match Map.tryFind x basicContraints with
            | Some(Some(lb), _) -> isSimplifiedSubType isAtomicSubtype lb r
            | _ -> true
        | l, Var(x) -> 
            match Map.tryFind x basicContraints with
            | Some(_, ub) -> isSimplifiedSubType isAtomicSubtype l ub
            | _ -> true
        | l, Intersect(ts) -> ts |> Seq.forall (fun r -> isPossiblyMatched basicContraints (l, r))
        | _, r when isArbitrarilyLarge basicContraints r -> true
        //r cannot be omega
        | Arrow(x1, y1), Arrow(x2, y2) -> isPossiblyMatched basicContraints (x2, x1) && isPossiblyMatched basicContraints (y1, y2)
        | Constructor(id1, cvs1), Constructor(id2, cvs2) -> 
            (List.length cvs1) = (List.length cvs2) && isAtomicSubtype id1 id2 
            && (List.forall2 (fun t1 t2 -> isPossiblyMatched basicContraints (t1, t2)) cvs1 cvs2)
        //if lhs contains an unbounded variable
        | Intersect(ts), _ when Set.exists (function | Var(x) -> x |> tryGetLowerBound basicContraints |> Option.isNone | _ -> false) ts -> true
        //l cannot be arbitrarily small (all lhs variables have a lower bound)
        | Intersect(ts), Constructor(id2, cvs2) -> 
            let argumentLists : IntersectionType list list = 
                ts
                |> Seq.map (function | Var(x) -> x |> tryGetLowerBound basicContraints |> Option.get | t -> t)
                |> Seq.choose (function 
                    | Constructor(id1, cvs1) when List.length cvs1 = List.length cvs2 && isAtomicSubtype id1 id2 -> Some(cvs1) 
                    | _ -> None) |> List.ofSeq
            if List.isEmpty argumentLists then false
            else List.forall2 (fun t1 t2 -> isPossiblyMatched basicContraints (t1, t2)) (intersectArgumentLists argumentLists) cvs2
        | Intersect(ts), Arrow(x2, y2) -> 
            let targets = 
                ts
                |> Seq.map (function | Var(x) -> x |> tryGetLowerBound basicContraints |> Option.get | t -> t)
                |> Seq.choose (function 
                    | Arrow(x1, y1) when isPossiblyMatched basicContraints (x2, x1) -> Some y1 
                    | _ -> None)
            isPossiblyMatched basicContraints ((intersectSimplifiedTypes targets), y2)
        | _, _ -> false


    /// <summary>
    /// Enumerate all constraints list non-deterministically arising from a given constraint that cannot be reduced deterministically.
    /// </summary>
    let enumerateNewConstraintsLists (basicContraints : BasicConstraintSystem) : Constraint -> seq<list<Constraint>> = function
        | (Arrow(x1, y1), Arrow(x2, y2)) -> 
            seq { 
                yield [(x2, x1); (y1, y2)]
                match getVariablesToMatchOmega y2 with
                | Some(variables) -> 
                    yield [for variable in variables do yield (Omega, variable)]
                | None -> () }
                
        | (Intersect(ts), (Constructor(id2, [])) & r) -> 
            ts |> Seq.choose (function 
                      //| Const y when (isAtomicSubtype y x) -> ... //already covered by a deterministic case
                      | Var _ & t -> Some([ (t, r) ])
                      | _ -> None)
                    
        | (Intersect(ts) & l, Constructor(id2, cvs2) & r) -> 
            seq {
                let argumentLists : IntersectionType list list = 
                    ts
                    |> Seq.choose (function 
                            | Constructor(id1, cvs1) when List.length cvs1 = List.length cvs2 
                                                            && isAtomicSubtype id1 id2 -> Some(cvs1)
                            | _ -> None)
                    |> List.ofSeq
                if List.isEmpty argumentLists then ()
                else yield (List.zip (intersectArgumentLists argumentLists) cvs2)

                let pathsWithRest = r |> enumeratePathsWithRest |> Seq.cache
                yield!
                    ts |> Seq.collect (function 
                               | Var _ & v -> 
                                   pathsWithRest |> Seq.map (fun (p, ps) -> [ (v, p); (l, ps) ])
                               | _ -> Seq.empty) }
                        
        | (Intersect(ts) & l, Arrow(x2, y2) & r) -> 
            seq {
                
                match getVariablesToMatchOmega y2 with
                | Some(variables) -> yield [for variable in variables do if isPossiblyMatched basicContraints (Omega, variable) then yield (Omega, variable)]
                | None -> ()

                match (isClosed l, isClosed x2, isClosed y2, getNumberOfPaths r) with
                | (true, true, _, _) -> 
                    let targets = 
                        Seq.choose (function 
                            | Arrow(x1, y1) & t when isSimplifiedSubType isAtomicSubtype x2 x1 -> Some y1
                            | _ -> None) ts
                    yield [ ((intersectSimplifiedTypes targets), y2) ]
                //ERROR? What if the single path ends in a variable and two arrows are required?
                | (true, _, _, 1) -> 
                    for t in ts do
                        match t with
                        | Arrow _ & t -> yield [ (t, r) ]
                        | _ -> () 
                | (true, false, true, _) when 
                    let targets = Seq.choose (function | Arrow(_, y1) -> Some y1 | _ -> None) ts
                    not (isSimplifiedSubType isAtomicSubtype (intersectSimplifiedTypes targets) y2) ->
                        ()
                | (true, _, _, numberOfPaths) -> 
                    yield!
                        ts
                        |> Set.filter (function 
                                | Arrow _ -> true
                                | _ -> false)
                        |> enumerateSubsetsUpToSize numberOfPaths
                        |> Seq.choose (fun subset -> 
                                let sourceConstraints, targets = 
                                    subset |> Seq.fold (fun (scs, tgts) -> 
                                                    function 
                                                    | Arrow(x1, y1) -> ((x2, x1) :: scs, y1 :: tgts)
                                                    | _ -> failwith "not an arrow") ([], [])
                       
                                let newConstraints = (intersectSimplifiedTypes targets, y2) :: sourceConstraints
                                Some(newConstraints))
                | (false, true, true, 1) -> 
                    for t in ts do
                        match t with
                        | Arrow _ & t | Var _ & t -> yield [ (t, r) ]
                        | _ -> () 
                //use sorce information in arrows (isProbablyMatchableWrtBasicConstraintSystem)
                | (false, true, true, numberOfPaths) -> 
                    yield!
                        ts
                        |> Set.filter (function | Arrow (x1, _) -> isPossiblyMatched basicContraints (x2, x1) | _ -> false)
                        |> enumerateSubsetsUpToSize numberOfPaths
                        |> Seq.choose (fun subset -> 
                                let sourceConstraints, targets = 
                                    subset |> Seq.fold (fun (scs, tgts) -> 
                                                    function 
                                                    | Arrow(x1, y1) -> ((x2, x1) :: scs, y1 :: tgts)
                                                    | _ -> failwith "not an arrow") ([], [])
                                   
                                let newConstraints = (intersectSimplifiedTypes targets, y2) :: sourceConstraints
                                Some(newConstraints)) 
                                        
                    //either r is matched by a subset of arrows in ts or a path in r is matched by a variable in ts
                    let pathsWithRest = r |> enumeratePathsWithRest
                    yield!
                        ts |> Seq.collect (function 
                                | Var _ & v -> 
                                    pathsWithRest 
                                    |> Seq.map (fun (p, ps) -> [ (v, p); (l, ps) ])
                                | _ -> Seq.empty)
                | _ -> failwith (sprintf "illegal queued constraint (%O, %O)" l r) }

        | _ -> Seq.empty

    /// <summary>
    /// Checks whether a given basic constraint system entry is consistent, i.e. lower bound leq upper bound.
    /// </summary>
    let isConsistent = function
        | (None, upperBound) -> true
        | (Some(lowerBound), upperBound) -> isSimplifiedSubType isAtomicSubtype lowerBound upperBound
    
    /// <summary>
    /// Checks whether a given basic constraint system entry identivies a value, i.e. lower bound = upper bound.
    /// </summary>
    let isPrecise = function
        | (None, upperBound) -> false
        | (Some(lowerBound), upperBound) -> isSimplifiedSubType isAtomicSubtype upperBound lowerBound

    /// <summary>
    /// Deterministically update constraint system consistently with "newConstaints". If an inconsistency is detected return None. 
    /// Renew "newConstaints" recursively for all deterministic steps. 
    /// </summary>
    let rec updateConstraintSystem (basicContraints : BasicConstraintSystem, queuedConstraints : Constraint list) (newConstraints : Constraint list) : option<BasicConstraintSystem * Constraint list> = 
        let (bcs, qcs) = (basicContraints, queuedConstraints)
        
        let updateBasicConstraintSystem (x : ID) (basicConstraint : BasicConstraint) (remainingConstraints : Constraint list) = 
            if isConsistent basicConstraint then 
                if isPrecise basicConstraint then
                    let substitution = Map.ofList [(x, snd basicConstraint)]
                    //reasses queued constraints that contain the identified variable
                    let (newConstraints, qcs) = 
                        List.partition (fun (l, r) -> containsVariableId x l || containsVariableId x r) qcs
                    let remainingConstraints = 
                        List.map (fun (l, r) -> (l, r) |>> (substituteSimplified substitution)) (newConstraints @ remainingConstraints)
                    updateConstraintSystem (Map.add x basicConstraint bcs, qcs) remainingConstraints
                else updateConstraintSystem (Map.add x basicConstraint bcs, qcs) remainingConstraints
            else None

        match newConstraints with
        //if there are no new constraints, i.e. queued constraints are to be analyzed non-deterministically
        | [] -> 
            if Seq.forall (isPossiblyMatched bcs) qcs then Some(bcs, qcs)
            else None
        | firstConstraint :: remainingConstraints ->
            match firstConstraint with
            //early abort for closed types or cases such as Intersect({a,x}) <= a
            | (l, r) when isSimplifiedSubType isAtomicSubtype l r -> updateConstraintSystem (bcs, qcs) remainingConstraints
            //if l and r are closed but not in subtype relation (above case) then abort
            | (l, r) when isClosed l && isClosed r -> None
            | (l, Intersect(ts)) -> 
                let newConstraints = ts |> Seq.map (fun t -> (l, t)) |> Seq.toList
                updateConstraintSystem (bcs, qcs) (newConstraints @ remainingConstraints)
            | (Arrow(x1, y1), Arrow(x2, y2)) when not (isArbitrarilyLarge bcs y2) -> 
                updateConstraintSystem (bcs, qcs) ((x2, x1) :: (y1, y2) :: remainingConstraints)
            | (Constructor(id1, cvs1), Constructor(id2, cvs2)) -> 
                if (List.length cvs1) = (List.length cvs2) && isAtomicSubtype id1 id2 then 
                    let newConstraints = List.zip cvs1 cvs2
                    updateConstraintSystem (bcs, qcs) (newConstraints @ remainingConstraints)
                else None
            | (Var(x), r) -> 
                let newBounds = 
                    match Map.tryFind x bcs with
                    | Some(lbo, ub) -> (lbo, getInfimumOfSimplifiedTypes [r; ub])
                    | None -> (None, r)
                updateBasicConstraintSystem x newBounds remainingConstraints
            | (l, Var(x)) -> 
                let newBounds = 
                    match Map.tryFind x bcs with
                    | Some(None, ub) -> (Some(l), ub)
                    | Some(Some(lb), ub) -> (Some(getSupremumOfSimplifiedTypes isAtomicSubtype [l; lb]), ub)
                    | None -> (Some(l), Omega)
                updateBasicConstraintSystem x newBounds remainingConstraints
            | (l, r) when isOmega l ->
                match getVariablesToMatchOmega r with
                | Some(variables) -> 
                    let newConstraints = [for variable in variables do yield (Omega, variable)]
                    updateConstraintSystem (bcs, qcs) (newConstraints @ remainingConstraints)
                | None -> None
            | (Constructor(_, _), Arrow(_, r)) -> 
                match getVariablesToMatchOmega r with
                | Some(variables) -> 
                    let newConstraints = [for variable in variables do yield (Omega, variable)]
                    updateConstraintSystem (bcs, qcs) (newConstraints @ remainingConstraints)
                | None -> None
            | (Intersect(ts), r) & c -> 
                match ts |> Seq.filter (fun t1 -> isRelated isAtomicSubtype t1 r) |> intersectSimplifiedTypes with
                | Intersect(newTs) -> updateConstraintSystem (bcs, (Intersect(newTs), r) :: qcs) remainingConstraints
                | l -> updateConstraintSystem (bcs, qcs) ((l, r) :: remainingConstraints)
            //queue constraint for non deterministic analysis
            | ((l, r) & c) -> updateConstraintSystem (bcs, c :: qcs) remainingConstraints

    let rec addConstraints (basicContraints : BasicConstraintSystem, queuedConstraints : Constraint list) (newConstraints : Constraint list) = 
        match updateConstraintSystem (basicContraints, queuedConstraints) newConstraints with
        | Some(basicConstraintSystem, []) -> Seq.singleton basicConstraintSystem
        | Some(basicConstraintSystem, c :: constraints) -> 
            enumerateNewConstraintsLists basicConstraintSystem c
            |> Seq.collect (addConstraints (basicConstraintSystem, constraints))
        | None -> Seq.empty

    fun constraints -> addConstraints (Map.empty, List.empty) (Seq.toList constraints)

/// <summary>
/// Decides whether given constraints are matchable.
/// </summary>
let isMatchable (isAtomicSubtype : ID -> ID -> bool) (constraints : seq<IntersectionType * IntersectionType>) = 
    (not << Seq.isEmpty) (enumerateBasicConstraintSystems isAtomicSubtype constraints)

/// <summary>
/// Enumerates maximal (wrt. isBasicConstraintSubsystem) basic constraint systems that satisty given constraints.
/// </summary>
let enumerateMaximalBasicConstraintSystems (isAtomicSubtype : ID -> ID -> bool) : seq<IntersectionType * IntersectionType> -> seq<BasicConstraintSystem> = 
    fun constraints ->
        constraints
        |> enumerateBasicConstraintSystems isAtomicSubtype
        |> enumerateMaximalElements (isBasicConstraintSubsystem isAtomicSubtype)