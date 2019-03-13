module CLS.Algorithm.InhabitationNoIIUtil

//No Intersection Introduction, Each argument is linked to a context of possibly useful entries

open System.Collections.Generic

open CLS.Model.ID
open CLS.Model.Type

open Util
open Type
open Orthogonality
open Matching
open InhabitationUtil



/// <summary>
/// maxTreeDepth is Maximal tree depth of inhabited types. Ignored if 0.
/// Given a atomic subtype relation, a combinatory type environment and a type, return the context free tree grammar that represents the inhabitant solution space.
/// </summary>
let isInhabitedNoII (maxTreeDepth : int) (logger : ILogger) (atomicSubtypes : ID -> ID -> bool) (context : EnvironmentEntry list) (failCache : HashSet<IntersectionType>) : (IntersectionType -> bool) = 
    //contains inhabited types.
    let successCache = new HashSet<IntersectionType>()
    //contains already encounterd types. Abort if a type is seen a second time.
    let pathCache = new HashSet<IntersectionType>()

    /// <summary>
    /// Returns true if "tau" is (presumably) inhabited, false otherwise. Updates caches.
    /// </summary>
    let rec isInhabitedRec (tau : IntersectionType) (relevantContext : list<EnvironmentEntry>) : bool = 
        if (getTreeRepsentationDepth tau > maxTreeDepth) || (failCache.Contains(tau)) || (pathCache.Contains(tau)) then false
        //tau is already assumed to be inhabited
        else if successCache.Contains(tau) || isOmega tau then true
        else
            logger 0 (lazy(sprintf "helper goal: %O" tau))
            //recursively assume that tau is inhabited
            pathCache.Add(tau) |> ignore

            let result : bool = 
                relevantContext 
                |> List.filter (fun entry -> 
                    isMatchable atomicSubtypes [(entry.IntersectionOfNthTargets, tau)])
                //select a matching subset of multi arrows containing at all necessary and no irrelevant multi arrows
                |> List.collect (fun entry ->
                    let necessaryMultiArrows, relevantMultiArrows = categorizeMultiarrows atomicSubtypes tau entry.MultiArrows
                    relevantMultiArrows
                    //at most (number of paths in tau) multiarrows are sufficient
                    |> enumerateSublists 0 (max 0 ((getNumberOfPaths tau) - List.length necessaryMultiArrows))
                    |> Seq.choose (fun sublist -> 
                        let multiArrows = sublist @ necessaryMultiArrows
                        let intersectionOfNthTargets = multiArrows |> Seq.map getTargetOfMultiarrow |> intersectSimplifiedTypes
                        if isMatchable atomicSubtypes [(intersectionOfNthTargets, tau)] then
                            Some({ entry with MultiArrows = multiArrows; IntersectionOfNthTargets = intersectionOfNthTargets })
                        else None)
                    |> Seq.toList)
                |> Seq.exists (fun entry -> 
                    let basicConstraintSystems = 
                        enumerateMaximalBasicConstraintSystems atomicSubtypes [(entry.IntersectionOfNthTargets, tau)]
                        |> Set.ofSeq
                    let allArguments : IntersectionType list = 
                        entry.MultiArrows |> (List.map (fun (arguments, _) -> arguments)) |> List.concat
                    let variableVariance : Map<ID, Variance> = 
                        getAccumulatedVariances (getVariableIds entry.IntersectionOfNthTargets) allArguments
                    let substitutions = 
                        basicConstraintSystems
                        |> Seq.collect (fun basicConstraintSystem -> enumerateConstraintSystemSubstitutions atomicSubtypes variableVariance basicConstraintSystem)
                        |> Set.ofSeq
                    substitutions
                    |> Seq.map (fun substitution -> 
                        logger 0 (lazy(sprintf "try combinator: %O" entry.Id))
                        entry.MultiArrows 
                        |> List.map (fun (arguments, _) -> arguments |> List.map (substituteSimplified substitution))
                        //aggregate lists since individual arrows do not matter as in regular inhabitation
                        |> intersectArgumentLists
                        |> removeRedundantVariables atomicSubtypes)
                    //rename variables so that there will be no collisions with targets in context (for estimateSubstitutionsInContext)
                    |> Seq.map (fun arguments -> (List.map (renameVariables (fun id -> id+"*"))) arguments)
                    |> Seq.exists (areArgumentsInhabitedRec entry.RelevantEnvironments))

            logger 0 (lazy(sprintf "analyzed helper goal: %O" tau))
            logger 0 (lazy(sprintf "helper result: %O" result))

            if not result then failCache.Add(tau) |> ignore
            else successCache.Add(tau) |> ignore
            pathCache.Remove(tau) |> ignore
            result

    /// <summary>
    /// Returns a list of lists containing n arguments (t_1, ..., t_n) each 
    /// so that each t_i is (presumably) inhabited by inhabitants {e_i_j}
    /// and a (virtual) combinator c with type "sigma" satisfies (c e_1_j ... e_n_j) is an inhabitant of the current goal.
    /// Each argument is associated with a corresponding relevant context
    /// </summary>
    and areArgumentsInhabitedRec (relevantContexts : list<list<Ref<EnvironmentEntry>>>) (arguments : MultiArrowArguments) : bool =          
        //the empty list of arguments is trivially inhabited
        if List.isEmpty arguments then true
        //if there is an argument which cannot be satisfied by the relevant context, then abort
        else if 
            List.exists2 (fun relevantEntries argument -> 
                List.forall (fun entry -> 
                    not (isPossiblySatisfiable atomicSubtypes ((!entry).IntersectionOfNthTargets, argument))) relevantEntries) relevantContexts arguments
            then false
        //if there is an argument of which the closed part is not inhabited, then abort
        else if 
            List.exists2 (fun relevantEntries argument -> 
                let closedArgument, _ = separateClosedType argument
                not (isInhabitedRec closedArgument (List.map (!) relevantEntries))) relevantContexts arguments
            then false
        else         
            //pick the first closed argument
            match arguments |> Seq.mapi (fun index argument -> (index, argument)) |> Seq.tryFind (fun (_, argument) -> isClosed argument) with
            | Some((index, _)) -> 
                //all closed arguments were already processed. Remove corresponding relevant context
                areArgumentsInhabitedRec (removeFromListAtIndex index relevantContexts) (removeFromListAtIndex index arguments)
            //if all arguments are open, then speculate on substitutions for individual arguments
            | None -> 
                arguments
                |> List.mapi (fun index argument -> (index, argument))
                |> List.exists (fun (index, argument) ->
                    let remainingArguments = removeFromListAtIndex index arguments
                    let variableIds = argument |> getVariableIds
                    let variances = getAccumulatedVariances variableIds remainingArguments
                    let relevantContext = List.map (!) (relevantContexts.[index])
                    guessSubstitutionsInContext atomicSubtypes relevantContext variances argument 
                    |> Seq.exists (fun substitution ->
                        let closedArgument = substituteSimplified substitution argument
                        if isInhabitedRec closedArgument relevantContext then
                            remainingArguments
                            |> List.map (substituteSimplified substitution) 
                            |> areArgumentsInhabitedRec (removeFromListAtIndex index relevantContexts)
                        else false))
    
    fun tau -> 
        pathCache.Clear()
        isInhabitedRec tau context
