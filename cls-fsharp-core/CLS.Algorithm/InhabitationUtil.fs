module CLS.Algorithm.InhabitationUtil

open CLS.Model.ID
open CLS.Model.Type
open CLS.Model.CombinatorTerm

open System.Collections.Generic

open Type
open Matching 
open CombinatorTerm
open Util
open Subtyping 
open Satisfiability

open CLS.Algorithm.Orthogonality

type ILogger = int -> Lazy<string> -> unit

type MultiArrowArguments = IntersectionType list
type MultiArrowTarget = IntersectionType
//MultiArrow consists of a list of arguments a a single target
type MultiArrow = MultiArrowArguments * MultiArrowTarget

/// <summary>
/// Gets target of a multiarrow source->b->c->...->target.
/// </summary>
let getTargetOfMultiarrow ((_, target) : MultiArrow) = target

/// <summary>
/// Gets the first argument of a multiarrow a->b->c->...->target.
/// </summary>
let getFirstArgument : (MultiArrowArguments -> IntersectionType) = List.head

/// <summary>
/// Apply "substitution" to a multiarrow.
/// </summary>
let substituteMultiarrow substitution ((arguments, target) : MultiArrow) : MultiArrow =
    (List.map (substituteSimplified substitution) arguments, substituteSimplified substitution target)

/// <summary>
/// Lists all multiarrows in tau with "numberOfArguments" arguments.
/// </summary>
let listMultiarrowsWithNArguments numberOfArguments tau = 
    let rec listArrowsRec n t = 
        if n = 0 then 
            let multiArrow : MultiArrow = ([], t)
            [multiArrow]
        else
            match t with
            | Arrow(x, y) -> y 
                             |> listArrowsRec (n-1)
                             |> List.choose (function | (_, target) when isOmega target -> None | (arguments, target) -> Some((x :: arguments, target)))
            | Intersect(ts) -> ts
                               |> Seq.collect (listArrowsRec n)
                               |> Seq.toList
            | _ -> [] //Var _, Constructor _, Omega
    listArrowsRec numberOfArguments (deOrganize tau)

type EnvironmentEntry =
    { Id : ID;
      NumberOfArguments : int;
      MultiArrows : MultiArrow list;
      IntersectionOfNthTargets : IntersectionType;
      //for each argument a list of relevant entries
      RelevantEnvironments : list<list<Ref<EnvironmentEntry>>> }


/// <summary>
/// Given a type environment, constructs a list of ContextEntry entries, respectfully removing Bracket constructors from any accurring types.
/// </summary>
let preprocessEnvironment (atomicSubtypes : ID -> ID -> bool) (environment : Environment) : EnvironmentEntry list = 

    //Initializes a list of ContextEntry entries. No RelevantContexts are set.
    let initializeContext (context : list<string * IntersectionType>) : EnvironmentEntry list = 
        context
        |> List.collect (fun (id, sigma) -> 
            let simplifiedSigma = sigma |> simplifyType |> deOrganize
            [0..(getMaxNumberOfArguments simplifiedSigma)] 
            |> List.map (fun numberOfArguments -> 
                let multiArrows = simplifiedSigma |> listMultiarrowsWithNArguments numberOfArguments
                //intersection of all (open) n-th targets
                let targets = multiArrows |> List.map getTargetOfMultiarrow |> intersectSimplifiedTypes
                { Id = id; 
                  NumberOfArguments = numberOfArguments; 
                  MultiArrows = multiArrows; 
                  IntersectionOfNthTargets = targets;
                  RelevantEnvironments = [] }))

    /// <summary>
    /// Replace Bracket(t) by t in the given context.
    /// </summary>
    let removeBracketsFromContext (preprocessedContext : EnvironmentEntry list) =
        preprocessedContext 
        |> List.map (fun entry -> 
            let multiArrows = 
                entry.MultiArrows 
                |> List.map (fun (arguments, target) -> 
                    (List.map removeBracketsFromType arguments, removeBracketsFromType target))
            let intersectionOfNthTargets = multiArrows |> Seq.map getTargetOfMultiarrow |> intersectSimplifiedTypes
            { entry with MultiArrows = multiArrows; IntersectionOfNthTargets = intersectionOfNthTargets })


    /// <summary>
    /// Remove context entries that have uninhabited arguments.
    /// </summary>
    let filterPreprocessedContext (preprocessedContext : EnvironmentEntry list) = 
        //preliminary, wrt. preprocessedContext which is unfiltered
        let existsSatisfyingTarget =
            let allTargets = preprocessedContext |> List.map (fun entry -> entry.IntersectionOfNthTargets)
            fun (tau : IntersectionType) -> allTargets |> List.exists (fun target -> isPossiblySatisfiable atomicSubtypes (target, tau))

        preprocessedContext
        |> List.choose (fun (entry : EnvironmentEntry) -> 
            let filteredMultiarrows = 
                entry.MultiArrows
                |> List.filter (fun (arguments, _) ->
                    arguments
                    |> List.forall existsSatisfyingTarget)
            if filteredMultiarrows = [] then None else Some({entry with MultiArrows = filteredMultiarrows}))

    /// <summary>
    /// Link each argument to a (overapproximated) relevant subcontext.
    /// </summary>
    let extendPreprocessedContext (preprocessedContext : EnvironmentEntry list) : EnvironmentEntry list = 
            let extendedContext = List.map ref preprocessedContext
        
            let getRelevantSubcontext (arguments : list<IntersectionType>) =
                extendedContext
                |> List.filter (fun relevantEntry ->
                    arguments
                    |> List.exists (fun argument ->
                        isPossiblySatisfiable atomicSubtypes ((!relevantEntry).IntersectionOfNthTargets, argument)))

            for entry in extendedContext do
                let relevantContexts = 
                    List.init (!entry).NumberOfArguments (fun i -> 
                        let arguments = List.map (fun (multiArrowArguments, _) -> (multiArrowArguments : list<_>).[i]) (!entry).MultiArrows
                        getRelevantSubcontext arguments)
                entry := { !entry with RelevantEnvironments = relevantContexts}

            List.map (!) extendedContext
    
    environment |> initializeContext |> removeBracketsFromContext |> filterPreprocessedContext |> extendPreprocessedContext

/// <summary>
/// Given a type "tau" and a list of multiarrows, returns a list of necessary multiarrows to match tau 
/// and a list of relevant multiarrows which might be needed.
/// Not related multiarrows are filtered out.
/// </summary>
let categorizeMultiarrows (atomicSubtypes : ID -> ID -> bool) (tau : IntersectionType) (multiArrows : list<MultiArrow>) : list<MultiArrow> * list<MultiArrow> = 
    let rec categorizeMultiarrowsRec necessaryMultiArrows relevantMultiArrows = function
        | [] -> (necessaryMultiArrows, relevantMultiArrows)
        | ((_, target) & multiArrow) :: remainingMultiArrows -> 
            if not (isRelated atomicSubtypes target tau) then
                categorizeMultiarrowsRec necessaryMultiArrows relevantMultiArrows remainingMultiArrows
            else
                let intersectionOfTargets = 
                    (necessaryMultiArrows @ relevantMultiArrows @ remainingMultiArrows) |> Seq.map getTargetOfMultiarrow |> intersectSimplifiedTypes
                //if tau is matched without the current multiArrow, then the current multiArrow is not strictly necessary
                if isMatchable atomicSubtypes [(intersectionOfTargets, tau)] then 
                    categorizeMultiarrowsRec necessaryMultiArrows (multiArrow :: relevantMultiArrows) remainingMultiArrows
                else 
                    categorizeMultiarrowsRec (multiArrow :: necessaryMultiArrows) relevantMultiArrows remainingMultiArrows

    categorizeMultiarrowsRec [] [] multiArrows


/// <summary>
/// Remove non-terminals (types) from memo that do not have a closed combinatory term.
/// </summary>
let rec refuteNotInhabitedTypes (memo : Dictionary<IntersectionType, Set<CombinatorExpression>>) (failCache : HashSet<IntersectionType>) =
    let inverseMap = new Dictionary<IntersectionType, HashSet<IntersectionType>>(Map.ofSeq (memo.Keys |> Seq.map (fun tau -> (tau, new HashSet<IntersectionType>()))))

    for entry in memo do
        for (_, arguments) in entry.Value do
            for argument in arguments do
                inverseMap.[argument].Add entry.Key |> ignore

    let rec getEmptyNonTerminalsRec (relevantNonTerminals : HashSet<IntersectionType>) (emptyNonTerminals : HashSet<IntersectionType>) = 
        let newRelevantNonTerminals = new HashSet<IntersectionType>()
        for nonTerminal in relevantNonTerminals do
            if memo.[nonTerminal] |> Set.exists (fun (_, arguments) -> 
                    List.forall (fun argument -> not (emptyNonTerminals.Contains(argument))) arguments) then
                emptyNonTerminals.Remove(nonTerminal) |> ignore
                newRelevantNonTerminals.UnionWith(inverseMap.[nonTerminal])
        newRelevantNonTerminals.IntersectWith(emptyNonTerminals)
        if newRelevantNonTerminals.Count > 0 then getEmptyNonTerminalsRec newRelevantNonTerminals emptyNonTerminals
        else emptyNonTerminals |> Set.ofSeq

    let emptyNonTerminals = getEmptyNonTerminalsRec (new HashSet<IntersectionType>(memo.Keys)) (new HashSet<IntersectionType>(memo.Keys))

    //update memo and failCache
    for tau in emptyNonTerminals do 
        memo.Remove tau |> ignore
        failCache.Add tau |> ignore
    //remove all combinator expressions that use not inhabited types
    for entry in Seq.toList memo do
        let filteredExpressions = 
            entry.Value 
            |> Set.filter (fun (_, arguments) -> List.forall (fun argument -> not (Set.contains argument emptyNonTerminals)) arguments)
        if Set.isEmpty filteredExpressions then failwith (sprintf "Unrefuted non inhabited type %O detected" entry.Key)
        memo.Item(entry.Key) <- filteredExpressions

/// <summary>
/// Use caches to construct the corresponding tree grammar with the start symbol tau.
/// </summary>
let constructTreeGrammar (memo : Dictionary<IntersectionType, Set<CombinatorExpression>>) (failCache : HashSet<IntersectionType>) tau = 
    refuteNotInhabitedTypes memo failCache

    if memo.ContainsKey tau then
        let nonTerminals = new HashSet<IntersectionType>()

        let rec addNonTerminal (nonTerminal : IntersectionType) : unit = 
            if (not (nonTerminals.Contains(nonTerminal))) then
                match memo.TryGetValue nonTerminal with
                | true, expressions when Set.count expressions > 0 -> 
                    nonTerminals.Add(nonTerminal) |> ignore
                    expressions |> Seq.iter (function | (_, arguments) -> Seq.iter addNonTerminal arguments)
                | _ -> failwith "Error in getAllInhabitants, refutation failed?"

        addNonTerminal tau

        nonTerminals
        |> Seq.map (fun nonTerminal -> (nonTerminal, memo.Item nonTerminal))
        |> Map.ofSeq
    else Map.ofList [(tau, Set.empty)]


let enumerateConstraintSystemSubstitutions (atomicSubtypes : ID -> ID -> bool) (variableVariance : Map<ID, Variance>) (basicConstraintSystem : BasicConstraintSystem) : seq<Substitution> = 
    if (Map.isEmpty basicConstraintSystem) then Seq.singleton Map.empty
    else
        basicConstraintSystem
        |> Seq.map (fun basicConstraintSystemEntry ->
            let vid = basicConstraintSystemEntry.Key
            let variance = Map.find vid variableVariance
            match basicConstraintSystemEntry.Value with
            | (_, upperBound) when variance = Covariant -> Seq.singleton (vid, upperBound) 
            | (None, upperBound) -> Seq.singleton (vid, upperBound) 
            | (Some(lowerBound), _) when variance = Contravariant -> Seq.singleton (vid, lowerBound) 
            | (Some(lowerBound), upperbound) when isSimplifiedSubType atomicSubtypes upperbound lowerBound
                -> Seq.singleton (vid, lowerBound) 
            | (Some(lowerBound), upperbound) -> seq { yield (vid, lowerBound); yield (vid, upperbound) })
        |> Seq.toList
        |> enumerateCarthesianProduct
        |> Seq.map Map.ofList


/// <summary>
/// Given a list of closed arguments and a list of open arguments, filter the list of open arguments.
/// An open argument is filtered, if it (along with corresponding arguments) is matchable by the closed arguments.
/// Therefore all substitutions of the filtered arguments would be overspecializations.
/// </summary>
let filterMatchableArguments1 (atomicSubtypes : ID -> ID -> bool) (closedArguments : MultiArrowArguments) (openArguments : MultiArrowArguments) : option<MultiArrowArguments> =
    let containsCommonElement set1 set2 =
        Set.exists (fun element1 -> Set.contains element1 set2) set1

    //union-find ~ overkill? bottleneck isMatchable.
    let mutable classes = [] : list<Set<ID>>

    let mutable (openArgumentsPaths : list<list<IntersectionType>>) = List.map (enumeratePaths >> List.ofSeq) openArguments
    
    //form equivalence classes of cooccurring variables
    for paths in openArgumentsPaths do
        for path in paths do
            let variableIds = getVariableIds path
            if Set.count variableIds > 0 then
                let relevantClasses, irrelevantClasses = List.partition (containsCommonElement variableIds) classes
                classes <- 
                    match relevantClasses with
                    | [] -> variableIds :: irrelevantClasses
                    | _ -> (Set.unionMany (variableIds :: relevantClasses)) :: irrelevantClasses

    for variableIds in classes do
        let (relevantPaths : list<list<IntersectionType>>), (irrelevantPaths : list<list<IntersectionType>>) = 
            openArgumentsPaths
            |> List.map (List.partition (fun path -> containsCommonElement variableIds (getVariableIds path)))
            |> List.unzip
        //create a matching problem from relevant paths
        let matchingProblem = List.map2 (fun l rs -> (l, intersectSimplifiedTypes rs)) closedArguments relevantPaths
        if isMatchable atomicSubtypes matchingProblem then openArgumentsPaths <- irrelevantPaths

    let filteredOpenArguments = List.map intersectSimplifiedTypes openArgumentsPaths
    
    if List.forall (fun argument -> argument = Omega) filteredOpenArguments then None
    else Some(filteredOpenArguments)



/// <summary>
/// Given a list of closed arguments and a list of open arguments, filter the list of open arguments.
/// An open argument is filtered, if it (along with corresponding arguments) is matchable by the closed arguments.
/// Therefore all substitutions of the filtered arguments would be overspecializations.
/// </summary>
let filterMatchableArguments (atomicSubtypes : ID -> ID -> bool) (closedArguments : MultiArrowArguments) (openArguments : MultiArrowArguments) : option<MultiArrowArguments> =
    let mutable classes = new Dictionary<ID, Set<ID>>()

    let mutable (openArgumentsPaths : list<list<IntersectionType>>) = List.map (enumeratePaths >> List.ofSeq) openArguments
    
    //form equivalence classes of cooccurring variables
    for paths in openArgumentsPaths do
        for path in paths do
            let variableIds = getVariableIds path
            let newClass = variableIds |> Seq.map (fun id -> findWithDefault classes (Set.singleton id) id) |> Set.unionMany
            variableIds |> Seq.iter (fun id -> classes.[id] <- newClass)

    for variableIds in classes.Values |> Seq.distinct do
        let (relevantPaths : list<list<IntersectionType>>), (irrelevantPaths : list<list<IntersectionType>>) = 
            openArgumentsPaths
            |> List.map (List.partition (fun path -> containsAnyVariableId variableIds path))
            |> List.unzip
        //create a matching problem from relevant paths
        let matchingProblem = List.map2 (fun l rs -> (l, intersectSimplifiedTypes rs)) closedArguments relevantPaths
        if isMatchable atomicSubtypes matchingProblem then openArgumentsPaths <- irrelevantPaths

    let filteredOpenArguments = List.map (intersectSimplifiedTypes >> deOrganize) openArgumentsPaths
    
    if List.forall isOmega filteredOpenArguments then None
    else Some(filteredOpenArguments)


/// <summary>
/// Use matching (filterMatchableArguments) to remove variables that only introduce redundancies.
/// </summary>
let removeRedundantVariables (atomicSubtypes : ID -> ID -> bool) (arguments : MultiArrowArguments) : MultiArrowArguments =
    if List.forall isClosed arguments then arguments
    else
        let closedArguments, openArguments = arguments |> List.map separateClosedType |> List.unzip
        match openArguments 
                |> List.map (function | Some(t) -> t | None -> Omega) 
                |> filterMatchableArguments atomicSubtypes closedArguments with
        | Some(filteredOpenArguments) -> 
            List.map2 (fun closedArgument openArgument -> 
                [closedArgument; openArgument] |> intersectSimplifiedTypes |> deOrganize ) closedArguments filteredOpenArguments
        | None -> closedArguments

/// <summary>
/// Use satisfiability to enumerate some substitutions that could be used to inhabit arg.
/// </summary>
let guessSubstitutionsInContext (atomicSubtypes : ID -> ID -> bool) (relevantContext : list<EnvironmentEntry>) (variableVariences : Map<ID, Variance>) (arg : IntersectionType) : seq<Substitution> = 
    if isClosed arg then Seq.singleton Map.empty
    else 
        relevantContext 
        |> Seq.collect (fun entry ->
            enumerateSatisfyingSubstitutions atomicSubtypes variableVariences [(entry.IntersectionOfNthTargets, arg)])
        |> Seq.distinct