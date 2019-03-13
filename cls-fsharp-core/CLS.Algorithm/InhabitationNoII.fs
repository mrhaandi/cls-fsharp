module CLS.Algorithm.InhabitationNoII

//Inhabitation Module, No Intersection Introduction, Each argument is linked to a context of possibly useful entries

open System.Collections.Generic

open CLS.Model.ID
open CLS.Model.Type
open CLS.Model.CombinatorTerm

open Util
open Type
open Orthogonality
open Matching
open InhabitationUtil
open InhabitationNoIIUtil


/// <summary>
/// maxTreeDepth is Maximal tree depth of inhabited types. Ignored if 0.
/// Given a atomic subtype relation, a combinatory type environment and a type, return the context free tree grammar that represents the inhabitant solution space.
/// </summary>
let getAllInhabitants (maxTreeDepth : int) (logger : ILogger) (atomicSubtypes : ID -> ID -> bool) (environment : Environment) : (IntersectionType -> TreeGrammar) = 
    //contains (presumably) inhabited types. might contain false positives which will be refuted.
    let memo = new Dictionary<IntersectionType, Set<CombinatorExpression>>()
    //contains only not inhabitable types
    let failCache = new HashSet<IntersectionType>()
    //use partial evalutation to find not inhabited closed arguments and eliminate context entries 
    let context = environment |> preprocessEnvironment atomicSubtypes

    let isPossiblyInhabited = isInhabitedNoII maxTreeDepth logger atomicSubtypes context failCache

    /// <summary>
    /// Returns true if "tau" is (presumably) inhabited, false otherwise. Updates caches.
    /// </summary>
    let rec isInhabitedRec (tau : IntersectionType) (relevantContext : list<EnvironmentEntry>) : bool = 
        if (getTreeRepsentationDepth tau > maxTreeDepth) || (failCache.Contains(tau)) then false
        //tau is already assumed to be inhabited
        else if memo.ContainsKey(tau) then true
        //inhabit omega with a special Combinator Omega (otherwise combinatory explosion)
        else if isOmega tau then 
            memo.Add(Omega, Set.singleton ("Omega", []))
            true
        else if not (isPossiblyInhabited tau) then false
        else
            logger 0 (lazy(sprintf "goal: %O" tau))
            //recursively assume that tau is inhabited
            memo.Add(tau, Set.empty)

            let inhabitants : CombinatorExpression list = 
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
                |> List.collect (fun entry -> 
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
                        //logger 0 (lazy(sprintf "try combinator: %O" entry.Id))
                        entry.MultiArrows 
                        |> List.map (fun (arguments, _) -> arguments |> List.map (substituteSimplified substitution))
                        //aggregate lists since individual arrows do not matter as in regular inhabitation
                        |> intersectArgumentLists
                        |> removeRedundantVariables atomicSubtypes)
                    //rename variables so that there will be no collisions with targets in context (for estimateSubstitutionsInContext)
                    |> Seq.map (fun arguments -> (List.map (renameVariables (fun id -> id+"*"))) arguments)
                    |> Seq.map (listArgumentInhabitantsRec entry.RelevantEnvironments)
                    |> List.concat
                    |> List.map (fun argumentIntabitants -> (entry.Id, argumentIntabitants)))

            logger 0 (lazy(sprintf "analyzed goal: %O" tau))
            logger 0 (lazy(sprintf "result: %O" inhabitants))

            if List.isEmpty inhabitants then 
                failCache.Add(tau) |> ignore
                memo.Remove(tau) |> ignore
                false
            else
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
            //if there is an argument of which the closed part is not inhabited or which cannot be satisfied by the relevant context, then abort
            List.exists2 (fun relevantEntries argument -> 
                let closedArgument, _ = separateClosedType argument
                not (isPossiblyInhabited closedArgument) ||
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
        let result = isInhabitedRec tau context
        if result then 
            logger 0 (lazy (sprintf "Constructing regular tree grammar (memo size = %d)" memo.Count)) 
            constructTreeGrammar memo failCache tau
        else Map.ofList [(tau, Set.empty)]
