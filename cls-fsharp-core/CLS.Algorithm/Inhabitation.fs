module CLS.Algorithm.Inhabitation


open System.Collections.Generic

open CLS.Model.ID
open CLS.Model.Type
open CLS.Model.CombinatorTerm

open Util
open Type
open Subtyping
open Orthogonality
open Matching
open CombinatorTerm
open InhabitationUtil

type MultiArrowCoverEntry = 
    { MultiArrowArguments : MultiArrowArguments;
      Substitution : Map<ID, IntersectionType>;
      ClosedMultiArrowTarget : IntersectionType }

/// <summary>
/// Creates covers for the minimal set cover problem using matching based on paths in tau and a list of multiarrows.
/// </summary>
let createCovers (atomicSubtypes : ID -> ID -> bool) (multiArrows : MultiArrow list) (paths : IntersectionType list) : ((MultiArrowArguments * Set<int>) list) = 
    multiArrows
    |> List.collect (fun ((arguments, target) & multiArrow) ->
        let basicConstraintSystems = 
            paths
            |> Seq.map (fun path ->
                enumerateMaximalBasicConstraintSystems atomicSubtypes [(target, path)]
                |> Set.ofSeq)
            |> Set.unionMany
            
        let variableVariance : Map<ID, Variance> = 
            target
            |> getVariableIds
            |> Seq.fold (fun accumulatedVariance id -> 
                Map.add id ((target :: arguments) |> List.map (getVariance id) |> getVarianceSupremum) accumulatedVariance) Map.empty
        let substitutions = 
            basicConstraintSystems
            |> Seq.collect (fun basicConstraintSystem -> enumerateConstraintSystemSubstitutions atomicSubtypes variableVariance basicConstraintSystem)
            |> Set.ofSeq
        substitutions
        |> Seq.map (fun substitution -> 
            let (newArguments, newTarget) = substituteMultiarrow substitution multiArrow
            let coveredPaths = 
                paths
                |> Seq.mapi (fun i path -> if isSimplifiedSubType atomicSubtypes newTarget path then Some(i) else None)
                |> Seq.choose (fun i -> i)
                |> Set.ofSeq
            (newArguments, coveredPaths))
        |> List.ofSeq)


let getAllInhabitants (maxTreeDepth : int) (logger : ILogger) (atomicSubtypes : ID -> ID -> bool) (environment : Environment) : (IntersectionType -> TreeGrammar) = 
    //contains (presumably) inhabitable types. might contain false positives which will be refuted.
    let memo = new Dictionary<IntersectionType, Set<CombinatorExpression>>()
    //contains only not inhabitable types
    let failCache = new HashSet<IntersectionType>()
    /// <summary>
    /// Checks whether each path p is matchable by sigma.
    /// </summary>
    let isEachPathMatchable (sigma : IntersectionType) (paths : IntersectionType list) = 
        paths |> List.forall (fun p -> isMatchable atomicSubtypes [(sigma, p)])
    
    (*
    /// <summary>
    /// Checks whether there is a target of a combinator type that matches each path in the given type.
    /// </summary>
    let doesSomeTargetMatchEachPath =
        //precompute all targets in context
        let allTargets = context 
                         |> List.collect (fun (_, sigma) -> let simplifiedSigma = simplifyType sigma
                                                            [0..(getMaxNumberOfArguments simplifiedSigma)] 
                                                            |> List.map (fun numberOfArguments -> getTargets numberOfArguments simplifiedSigma))
        memoize (fun (tau : LambdaType2) -> let paths = tau |> enumeratePaths |> Seq.toList 
                                            allTargets |> List.exists (fun target -> isEachPathMatchable target paths))
    //*)

    //use partial evalutation to estimate not inhabitable closed arguments and eliminate context entries 
    let context = environment |> preprocessEnvironment atomicSubtypes
    
    /// <summary>
    /// Checks whether there is a target of a combinator type that matches each path in the given type.
    /// </summary>
    let doesSomeTargetMatchEachPath =
        //precompute all targets in context
        let allTargets = context 
                         |> List.map (fun entry -> entry.IntersectionOfNthTargets)
        memoize (fun (tau : IntersectionType) -> let paths = tau |> enumeratePaths |> Seq.toList 
                                                 allTargets |> List.exists (fun target -> isEachPathMatchable target paths))
    
    let mayBeInhabited (tau : IntersectionType) = 
        if failCache.Contains(tau) then false
        else if not (doesSomeTargetMatchEachPath tau) then
            failCache.Add(tau) |> ignore
            false
        else true

    /// <summary>
    /// Returns true if "tau" is (presumably) inhabitable, false otherwise. Updates caches.
    /// </summary>
    let rec isInhabitedRec (tau : IntersectionType) (relevantContext : list<EnvironmentEntry>) : bool = 
        if (getTreeRepsentationDepth tau > maxTreeDepth) || (failCache.Contains(tau)) then false
        //is assumed inhabitable
        else if memo.ContainsKey(tau) then true
        //inhabit omega with a special combinator Omega
        else if isOmega tau then 
            memo.Add(Omega, Set.singleton ("Omega", []))
            true
        //early abort on necessary condition
        else if not (mayBeInhabited tau) then false
        else
            logger 0 (lazy (sprintf "Goal: %O" tau))
            //recursively assume that tau is inhabited
            memo.Add(tau, Set.empty)

            let pathsInTau = tau |> (enumeratePaths >> Seq.toList)
            let inhabitants : CombinatorExpression list = 
                relevantContext 
                //here parallelization yields little
                |> List.filter (fun entry -> 
                    isEachPathMatchable entry.IntersectionOfNthTargets pathsInTau)
                |> List.collect (fun entry -> 
                    logger 0 (lazy (sprintf "use combinator %O with %O args for goal %O" entry.Id entry.NumberOfArguments tau))
                    
                    pathsInTau
                    //lists (arrow arguments, set of indices of paths in tau which are matched by the arrow target)
                    |> createCovers atomicSubtypes (List.filter (fun (_, target) -> isRelated atomicSubtypes target tau) entry.MultiArrows)
                    //enumerates minimal lists of arrow arguments whose targets match all paths in tau
                    |> enumerateMinimalSetCovers (List.length pathsInTau)
                    |> Seq.map intersectArgumentLists
                    |> Seq.map (removeRedundantVariables atomicSubtypes)
                    //recursively inhabit arguments
                    |> Seq.map (listArgumentInhabitantsRec entry.RelevantEnvironments)
                    |> List.concat
                    |> List.map (fun argumentIntabitants -> (entry.Id, argumentIntabitants)))

            if List.isEmpty inhabitants then 
                failCache.Add(tau) |> ignore
                memo.Remove(tau) |> ignore
                false
            else 
                //overapproximation. inhabitability of tau may have been used
                memo.Item(tau) <- Set.ofList inhabitants
                true

    /// <summary>
    /// Returns a list of lists containing n arguments (t_1, ..., t_n) each 
    /// so that each t_i is (presumably) inhabited by inhabitants {e_i_j}
    /// and a (virtual) combinator c with type "sigma" satisfies (c e_1_j ... e_n_j) is an inhabitant of the current goal.
    /// Each argument is associated with a corresponding relevant context
    /// </summary>
    and listArgumentInhabitantsRec (relevantContexts : list<list<Ref<EnvironmentEntry>>>) (arguments : MultiArrowArguments) : MultiArrowArguments list =          
        //the empty list of arguments is trivially inhabited
        if List.isEmpty arguments then [[]] 
        //if there is an argument that is not satisfied by all relevant entries, then there is no tuple of inhabitants for the argument list
        else if 
            List.exists2 (fun relevantEntries argument -> 
                List.forall (fun entry -> 
                    not (isPossiblySatisfiable atomicSubtypes ((!entry).IntersectionOfNthTargets, argument))) relevantEntries) relevantContexts arguments
            then []
        else         
            //pick the first closed argument
            match arguments |> Seq.mapi (fun index argument -> (index, argument)) |> Seq.tryFind (fun (_, argument) -> isClosed argument) with
            | Some((index, closedArgument)) -> 
                if isInhabitedRec closedArgument (List.map (!) relevantContexts.[index]) then
                    //process remaining arguments
                    (removeFromListAtIndex index arguments)
                    //remove corresponding relevant context
                    |> listArgumentInhabitantsRec (removeFromListAtIndex index relevantContexts)
                    |> List.map (insertInListAtIndex (index, closedArgument))
                else []
            //if all arguments are open, then speculate on substitutions for individual arguments
            | None -> 
                arguments
                |> List.mapi (fun index argument -> (index, argument))
                |> List.collect (fun (index, argument) ->
                    let remainingArguments = removeFromListAtIndex index arguments
                    let variableIds = argument |> getVariableIds
                    let variances = getAccumulatedVariances variableIds remainingArguments
                    let relevantContext = List.map (!) (relevantContexts.[index])
                    guessSubstitutionsInContext atomicSubtypes relevantContext variances argument 
                    |> List.ofSeq
                    |> List.collect (fun substitution ->
                        let closedArgument = substituteSimplified substitution argument
                        if isInhabitedRec closedArgument relevantContext then
                            remainingArguments
                            |> List.map (substituteSimplified substitution) 
                            |> listArgumentInhabitantsRec (removeFromListAtIndex index relevantContexts)
                            |> List.map (insertInListAtIndex (index, closedArgument))
                        else []))
                |> List.distinct


    fun tau -> 
        let tau = simplifyType tau
        let result = isInhabitedRec tau context
        if result then 
            logger 0 (lazy ("Constructing regular tree grammar")) 
            constructTreeGrammar memo failCache tau
        else Map.ofList [(tau, Set.empty)]
