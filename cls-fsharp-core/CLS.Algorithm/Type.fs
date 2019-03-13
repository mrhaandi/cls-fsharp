module CLS.Algorithm.Type

open CLS.Model.ID
open CLS.Model.Type
open Util
open System.Collections.Generic

/// <summary>
/// Returns true iff the given type is an empty intersection (i.e. syntactically is the universal type Omega).
/// </summary>
let isOmega : IntersectionType -> bool = function | Intersect(ts) when Set.isEmpty ts -> true | _ -> false

/// <summary>
/// Returns true iff the given type contains the constructor id.
/// </summary>
let rec containsConstructor (id : ID) = 
    function 
    | Var _ -> false
    | Arrow(x, y) -> containsConstructor id x || containsConstructor id y
    | Constructor(id2, cvs) -> id = id2 || List.exists (containsConstructor id) cvs
    | Intersect(ts) -> Set.exists (containsConstructor id) ts

/// <summary>
/// Returns the simplified type which is the intersection of given simplified types.
/// </summary>
let rec intersectSimplifiedTypes (types : seq<IntersectionType>) = 
    let flatTypes = seq { for t in types do match t with | Intersect(ts) -> yield! ts | _ -> yield t } |> Set.ofSeq
    match flatTypes.Count with
    | 1 -> Seq.head flatTypes
    | _ -> Intersect(flatTypes)

/// <summary>
/// Recursively tests that whether a given type is simplified.
/// </summary>
let rec isSimplifiedType = 
    function
    | Arrow(s, t) -> (not (isOmega t)) && isSimplifiedType s && isSimplifiedType t
    | Intersect(ts) -> ts.Count > 1 && Set.forall (function | Intersect(_) -> false | t -> isSimplifiedType t) ts
    | Constructor(_, cvs) -> List.forall isSimplifiedType cvs
    | _ -> true

/// <summary>
/// Recursively simplifies type and reduces it wrt. Omega.
/// <para>Postcondition: (simplifyType tau) contains no nested or empty Intersect, no t->Omega and no equal constructors in an intersection. </para>
/// </summary>
let rec simplifyType tau = 
    if isSimplifiedType tau then tau 
    else
        match tau with 
        | Arrow(s, t) -> 
            match simplifyType t with
            | t when isOmega t -> Omega
            | simplifiedTarget -> Arrow(simplifyType s, simplifiedTarget)
        | Intersect(ts) -> 
            ts |> Seq.map simplifyType |> intersectSimplifiedTypes
        | Constructor(id, cvs) -> Constructor(id, List.map simplifyType cvs)
        | tau -> tau //Omega, Var

/// <summary>
/// Given a nonempty list of lists with n types each,
/// returns the list n intersections of individual entries of those lists.
/// <para> Example [[a1;a2];[b1;b2]] |-> [a1 cap b1; a2 cap b2]. </para>
/// </summary>
let intersectArgumentLists (argumentLists : IntersectionType list list) = 
    match argumentLists with
    | [] -> failwith "Unable to intersect zero argument lists."
    | [l] -> l
    | l::ls ->
        let mutable aggregatedArgumentList = 
            l |> List.map (fun argument -> [ argument ])
        for argumentList in ls do
            aggregatedArgumentList <- List.map2 (curry List.Cons) argumentList aggregatedArgumentList
        aggregatedArgumentList |> List.map intersectSimplifiedTypes

//Path functions

/// <summary>
/// Returns true iff the given simplified type is a path.
/// </summary>
let rec isPath = 
    function 
    | Intersect(_) -> false
    | Arrow(_, y) -> isPath y
    | Constructor(_, cvs) when List.forall isOmega cvs -> true
    | Constructor(_, cvs) -> 
        match List.filter (isOmega >> not) cvs with
        | [cv] -> isPath cv
        | _ -> false
    | Var(_) -> true


/// <summary>
/// Returns true if the given simplified type is a path under any substitution.
/// Main retunrn false negatives when variables are kinded by singletons.
/// </summary>
let rec isPathUnderAnySubstitution = 
    function 
    | Intersect(_) -> false
    | Arrow(x, y) -> isPathUnderAnySubstitution y
    | Constructor(_, cvs) when List.forall isOmega cvs -> true
    | Constructor(_, cvs) -> 
        match List.filter (isOmega >> not) cvs with
        | [cv] -> isPathUnderAnySubstitution cv
        | _ -> false
    | _ -> false //Omega, Var

/// <summary>
/// Returns the min path length of a given simplified type.
/// </summary>
let getMinPathLength tau = 
    let rec getMinPathLengthRec depth = 
        function 
        | Intersect(ts) -> 
            ts
            |> Seq.map (getMinPathLengthRec depth)
            |> Seq.min
        | Arrow(x, y) -> getMinPathLengthRec (depth + 1) y
        | Constructor(id, []) -> depth
        | Constructor(id, cvs) -> 
            cvs
            |> Seq.map (getMinPathLengthRec depth)
            |> Seq.min
        | t -> depth //Omega, Var
    getMinPathLengthRec 0 tau

/// <summary>
/// Returns the max path length of a given simplified type.
/// </summary>
let getMaxPathLength tau = 
    let rec getMaxPathLengthRec depth = 
        function 
        | Intersect(ts) -> 
            ts
            |> Seq.map (getMaxPathLengthRec depth)
            |> Seq.max
        | Arrow(x, y) -> getMaxPathLengthRec (depth + 1) y
        | Constructor(id, []) -> depth
        | Constructor(id, cvs) -> 
            cvs
            |> Seq.map (getMaxPathLengthRec depth)
            |> Seq.max
        | t -> depth //Omega, Var
    getMaxPathLengthRec 0 tau


/// <summary>
/// Enumerates all paths of a given simplified type (note: omega is not a path).
/// </summary>
let rec enumeratePaths = 
    function 
    | Intersect(ts) -> 
        seq { 
            for t in ts do
                yield! (enumeratePaths t)
        }
    | Arrow(s, t) -> 
        seq { 
            for x in enumeratePaths t do
                yield Arrow(s, x)
        }
    | Constructor(id, []) & t -> Seq.singleton t
    | Constructor(id, cvs) & t when List.forall isOmega cvs -> Seq.singleton t
    | Constructor(id, cvs) -> 
        let numberOfArguments = List.length cvs
        seq { 
            for (i, argument) in List.mapi (fun i argument -> (i, argument)) cvs do
                for path in enumeratePaths argument do
                    yield Constructor(id, 
                                      List.init numberOfArguments (fun index -> 
                                          if index = i then path
                                          else Omega))
        }
    | t -> Seq.singleton t //Var

/// <summary>
/// Return the number of paths of a given simplified type (note: omega is not a path).
/// </summary>
let rec getNumberOfPaths = 
    function 
    | Intersect(ts) -> 
        ts |> Seq.sumBy getNumberOfPaths
    | Arrow(s, t) -> getNumberOfPaths t
    | Constructor(id, []) -> 1
    | Constructor(_, cvs) -> 
        cvs
        |> Seq.sumBy getNumberOfPaths
        |> max 1 //if all arguments are Omega then there is only one path
    | t -> 1 //Var


/// <summary>
/// Enumerates all pairs (p, rest) of for the argument tau so that p is a path and Intersect[p,rest]=tau 
/// (think: tau is split in a path p and the rest) (note: omega is not a path).
/// </summary>
let rec enumeratePathsWithRest = 
    function 
    | t when isOmega t -> Seq.empty
    | Intersect(ts) -> 
        seq { 
            for t in ts do
                let remainingTerms = Set.remove t ts
                for (p, rest) in enumeratePathsWithRest t do
                    match (rest, Set.count remainingTerms) with
                    | _, 1 when isOmega rest -> yield (p, Set.minElement remainingTerms)
                    | _, _ when isOmega rest -> yield (p, Intersect(remainingTerms))
                    | _, _ -> 
                        let newTs = Set.add rest remainingTerms
                        match Set.count newTs with
                        | 1 -> yield (p, Set.minElement newTs)
                        | _ -> yield (p, Intersect(newTs))
        }
    | t when isPath t -> Seq.singleton (t, Omega) //Var
    //if t is not a path then the rest is never Omega
    | Arrow(s, t) -> 
        t
        |> enumeratePathsWithRest
        |> Seq.map (fun (p, rest) -> (Arrow(s, p), Arrow(s, rest)))
    | Constructor(id, cvs) -> 
        seq { 
            let length = List.length cvs
            for index in [ 0..length - 1 ] do
                if not (isOmega cvs.[index]) then 
                    for (p, rest) in enumeratePathsWithRest cvs.[index] do
                        yield (Constructor(id, 
                                           List.init length (fun i -> 
                                               if i = index then p
                                               else Omega)), 
                               Constructor(id, 
                                           List.mapi (fun i t -> 
                                               if i = index then rest
                                               else t) cvs))
        }
    | t -> failwith (sprintf "Missing case for %O in enumeratePathsWithRest." t)

/// <summary>
/// Reverses organization by combining paths.
/// </summary>
let rec deOrganize = 
    function 
    | Arrow(x, y) -> Arrow(x, deOrganize y)
    | Constructor(id, cvs) -> Constructor(id, List.map deOrganize cvs)
    | Intersect(ts) -> 
        let arrows = new Dictionary<IntersectionType, IntersectionType list>()
        let constructors = new Dictionary<ID, IntersectionType list list>()
        let mutable otherTypes : IntersectionType list = []
        for t in ts do
            match t with
            | Arrow(x, y) -> 
                arrows.[x] <- y :: (findWithDefault arrows [] x)
            | Constructor(id, cvs) -> 
                let argumentLists = findWithDefault constructors (List.replicate (List.length cvs) []) id
                constructors.[id] <- List.map2 (curry List.Cons) cvs argumentLists
            | _ -> otherTypes <- t :: otherTypes
        
        otherTypes
        |> Seq.append (seq { for entry in constructors do yield Constructor(entry.Key, List.map (intersectSimplifiedTypes >> deOrganize) entry.Value) })
        |> Seq.append (seq { for entry in arrows do yield Arrow(entry.Key, entry.Value |> intersectSimplifiedTypes |> deOrganize) })
        |> intersectSimplifiedTypes
    | tau -> tau //Omega, Var

/// <summary>
/// Returns the source of a given Arrow(source, target).
/// </summary>
let getArrowSorce = 
    function 
    | Arrow(x, _) -> x
    | _ -> failwith "not an arrow"

/// <summary>
/// Returns the target of a given Arrow(source, target).
/// </summary>
let getArrowTarget = 
    function 
    | Arrow(_, y) -> y
    | _ -> failwith "not an arrow"

/// <summary>
/// Returns the maximal number of arguments of a path in tau.
/// getMaxNumberOfArguments is not equivalent to path length because of Box which allows longer paths.
/// </summary>
let getMaxNumberOfArguments tau = 
    let rec getMaxNumberOfArgumentsRec depth = 
        function 
        | Intersect(ts) -> 
            ts
            |> Seq.map (getMaxNumberOfArgumentsRec depth)
            |> Seq.max
        | Arrow(x, y) -> getMaxNumberOfArgumentsRec (depth + 1) y
        | t -> depth //Omega, Var, Constructor
    getMaxNumberOfArgumentsRec 0 tau

/// <summary>
/// Returns the set ids of variables occurring in the given type.
/// </summary>
let rec getVariableIds = 
    function 
    | Var(x) -> Set.singleton x
    | Arrow(x, y) -> Set.union (getVariableIds x) (getVariableIds y)
    | Intersect(ts) -> 
        ts
        |> Seq.map getVariableIds
        |> Set.unionMany
    | Constructor(_, []) -> Set.empty
    | Constructor(_, cvs) -> Set.unionMany (List.map getVariableIds cvs)

/// <summary>
/// Checks whether the given type contains the given variable IDs. 
/// </summary>
let rec containsVariableId (variableId : ID) = function
    | Var(x) -> x = variableId
    | Arrow(x, y) -> (containsVariableId variableId x) || (containsVariableId variableId y)
    | Intersect(ts) -> Seq.exists (containsVariableId variableId) ts
    | Constructor(_, cvs) -> Seq.exists (containsVariableId variableId) cvs

/// <summary>
/// Checks whether the given type contains the given variable IDs. 
/// </summary>
let rec containsAnyVariableId (variableIds : Set<ID>) = function
    | Var(x) -> Set.contains x variableIds
    | Arrow(x, y) -> (containsAnyVariableId variableIds x) || (containsAnyVariableId variableIds y)
    | Intersect(ts) -> Seq.exists (containsAnyVariableId variableIds) ts
    | Constructor(_, cvs) -> Seq.exists (containsAnyVariableId variableIds) cvs

/// <summary>
/// Checks whether the given type contains no variables.
/// </summary>
let rec isClosed = 
    function 
    | Var _ -> false
    | Arrow(x, y) -> isClosed x && isClosed y
    | Constructor(_, cvs) -> List.forall isClosed cvs
    | Intersect(ts) -> Seq.forall isClosed ts

/// <summary>
/// Given a type tau, split t in a closed type t1 and a maximal (wrt. subtyping) open type t2 so that tau = t1 cap t2.
/// </summary>
let rec separateClosedType = function
    | t when isClosed t -> (t, None)
    | Var(_) & t -> (Omega, Some(t))
    | Arrow(s, t) -> 
        if isClosed s then
            match separateClosedType t with
            | (t1, Some(t2)) when isOmega t1 -> (Omega, Some(Arrow(s, t2)))
            | (t1, Some(t2)) -> (Arrow(s, t1), Some(Arrow(s, t2)))
            | _ -> failwith "illegal argument in separateClosedType"
        else (Omega, Some(Arrow(s, t)))
    | Constructor(id, cvs) & t -> 
        let (closedCvs, openCvs) = cvs |> List.map separateClosedType |> List.unzip
        //explicitly return C(omega) as a closed path
        (Constructor(id, closedCvs), Some(Constructor(id, openCvs |> List.map (function | None -> Omega | Some(cv) -> cv))))
    | Intersect(ts) -> 
        let (closedTs, openTs) = 
            ts |> Seq.fold (fun (closedTs, openTs) t -> 
                match separateClosedType t with
                | (ct, None) when isOmega ct -> (closedTs, openTs)
                | (ct, Some(ot)) when isOmega ct -> (closedTs, ot :: openTs)
                | (ct, None) -> (ct :: closedTs, openTs)
                | (ct, Some(ot)) -> (ct :: closedTs, ot :: openTs)) ([],[])
        (intersectSimplifiedTypes closedTs, Some(intersectSimplifiedTypes openTs))
    | _ -> failwith "illegal argument in separateClosedType"

/// <summary>
/// Substitutes variables in the second argument by simplified types according to substitution.
/// <para>Precondition: all partaking types are simplified.</para>  
/// </summary>
let substituteSimplified (substitution : Substitution) = 
    let rec substituteRec = 
        function 
        //expensive early abort 
        | t when isClosed t -> t
        | Var(x) & v -> 
            match Map.tryFind x substitution with
            | Some t -> t
            | None -> v
        | Arrow(x, y) -> 
            match substituteRec y with
            | t when isOmega t -> Omega
            | t -> Arrow(substituteRec x, t)
        | Constructor(id, cvs) -> Constructor(id, List.map substituteRec cvs)
        | Intersect(ts) -> 
            ts
            |> Seq.map substituteRec
            |> intersectSimplifiedTypes
        | tau -> tau
    if Map.isEmpty substitution then Operators.id
    else substituteRec

/// <summary>
/// Rename variables in tau according to injective renaming.
/// </summary>
let renameVariables (injectiveRenaming : ID -> ID) tau = 
    let rec renameRec = function
        | Var(x) -> Var (injectiveRenaming x)
        | Arrow(x,y) -> Arrow(renameRec x, renameRec y)
        | Intersect(ts) -> Intersect(Set.map renameRec ts)
        | Constructor(id, cvs) -> Constructor(id, List.map renameRec cvs)
    renameRec tau


/// <summary>
/// Returns the depth of the algebraic data type tree that represents the given type.
/// </summary>
let rec getTreeRepsentationDepth = function
    | Arrow(s, t) -> 1 + (max (getTreeRepsentationDepth s) (getTreeRepsentationDepth t))
    | Constructor(_, []) -> 0
    | Constructor(_, cvs) -> 1 + (cvs |> Seq.map getTreeRepsentationDepth |> Seq.max)
    | t when isOmega t -> 0
    | Intersect(ts) -> 1 + (ts |> Seq.map getTreeRepsentationDepth |> Seq.max)
    | _ -> 0 //Omega, Var

/// <summary>
/// Replace Bracket(t) by t in a given type.
/// </summary>
let rec removeBracketsFromType = function
    | Arrow(s, t) -> 
        match removeBracketsFromType t with
        | t' when isOmega t' -> Omega
        | t' -> Arrow(removeBracketsFromType s, t')
    | Intersect(ts) -> ts |> Set.map removeBracketsFromType |> intersectSimplifiedTypes
    | Constructor("Bracket", [t]) -> removeBracketsFromType t
    | Constructor(id, cvs) -> Constructor(id, List.map removeBracketsFromType cvs)
    | t -> t //Omega, Var

//-
//Variance functions
//-
type Variance = 
    | UnknownVariance
    | Covariant
    | Contravariant
    | Invariant

/// <summary>
/// Returns the supremum of multiple variance values.
/// </summary>
let rec getVarianceSupremum varianceValues = 
    varianceValues 
    |> Seq.fold (fun supremum variance -> 
        if supremum = UnknownVariance then variance
        else if variance = UnknownVariance then supremum
        else if supremum = variance then supremum
        else Invariant) UnknownVariance

/// <summary>
/// Flips co- and contravariance.
/// </summary>
let flipVariance = 
    function 
    | Covariant -> Contravariant
    | Contravariant -> Covariant
    | v -> v

/// <summary>
/// Returns the supremum of the variances of the occurrence of the variable "id" in the given type.
/// </summary>
let rec getVariance id = 
    function 
    | Var(id2) when id = id2 -> Covariant
    | Arrow(s, t) -> 
        [ flipVariance (getVariance id s)
          getVariance id t ]
        |> getVarianceSupremum
    | Constructor(_, cvs) -> 
        cvs
        |> Seq.map (getVariance id)
        |> getVarianceSupremum
    | Intersect(ts) -> 
        ts
        |> Seq.map (getVariance id)
        |> getVarianceSupremum
    | _ -> UnknownVariance //Omega

/// <summary>
/// Returns the map containing least upper bounds of variances of variables occurring in the given types.
/// </summary>
let getAccumulatedVariances (ids : Set<ID>) (types : seq<IntersectionType>) : Map<ID, Variance> =
    ids
    |> Seq.map (fun id -> (id, types |> Seq.map (getVariance id) |> getVarianceSupremum))
    |> Map.ofSeq

/// <summary>
/// Returns the number of nodes in the syntax tree in the given type.
/// </summary>
let rec getTypeSize =
    function
    | Var(_) -> 1
    | Arrow(s, t) -> 1 + (getTypeSize s) + (getTypeSize t)
    | Constructor(_, ts) -> 1 + (ts |> List.sumBy getTypeSize)
    | Intersect(ts) -> 1 + (ts |> Seq.sumBy getTypeSize)