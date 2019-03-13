module CLS.Algorithm.CombinatorTerm

open CLS.Model.ID
open CLS.Model.Type
open CLS.Model.CombinatorTerm

open System.Collections.Generic

open Util

/// <summary>
/// Returns the sequence of keys in a given map.
/// </summary>
let getKeys (m : Map<'a, 'b>) = seq { for entry in m do yield entry.Key }

/// <summary>
/// Returns the set of variables in expression.
/// </summary>
let getCombinatorExpressionVariables (expression : CombinatorExpression) =
    expression |> snd |> Set.ofList

(*
let rec isClosedCombinatorTerm = function
    | CombinatorVariable _ -> false
    | CombinatorTerm(_, arguments) -> List.forall isClosedCombinatorTerm arguments
//*)

/// <summary>
/// Compute the numberOfTerms closed terms of nonTerminal in grammar of minimal tree size (number of nodes). Naiive implementation.
/// </summary>
let listMinimalCombinatorTerms (numberOfTerms : int) (grammar : TreeGrammar) (nonTerminal : IntersectionType) : list<CombinatorTerm> =

    //compute minimal sizes and closed terms derivable from each non-terminal sorted by size
    let minimalClosedTerms = new Dictionary<IntersectionType, list<int * CombinatorTerm>>()

    //build an inverse map that assigns to each type a set of types that are using it as an argument
    let useMap = 
        new Dictionary<IntersectionType, HashSet<IntersectionType>>
            (Map.ofSeq (grammar |> getKeys |> Seq.map (fun tau -> (tau, new HashSet<IntersectionType>()))))
    for entry in grammar do
        minimalClosedTerms.Add(entry.Key, [])
        for (_, arguments) in entry.Value do
            for argument in arguments do
                useMap.[argument].Add entry.Key |> ignore

    //update minimalClosedTerms at nonTerminal using newTermWithSize. returns true if newTermWithSize was useful
    let updateTermList (nonTerminal : IntersectionType) (newTermWithSize : (int * CombinatorTerm)) : bool =
        let termsWithSize = minimalClosedTerms.[nonTerminal]
        //abort if term already present
        if List.contains newTermWithSize termsWithSize then false
        //add term if there is room in the list
        else if List.length termsWithSize < numberOfTerms then
            minimalClosedTerms.[nonTerminal] <- newTermWithSize :: termsWithSize
            true
        //do not add term if list is full and the maximal size of an already found term is not larger
        else if (termsWithSize |> List.map fst |> List.max) <= (fst newTermWithSize) then false
        else
            minimalClosedTerms.[nonTerminal] <- newTermWithSize :: (termsWithSize |> List.sortByDescending fst |> List.tail)
            true
                    
    //update minimalClosedTerms at nonTerminals
    let rec updateMinimalTerms (nonTerminals : HashSet<IntersectionType>) : unit =
        //set of non-terminals that may need to be updated
        let relevantNonTerminals = new HashSet<IntersectionType>()
        for nonTerminal in nonTerminals do
            Map.find nonTerminal grammar
            |> Seq.filter (fun (_, arguments) -> 
                //all agruments have closed forms
                List.forall (fun argument -> not (List.isEmpty (minimalClosedTerms.[argument]))) arguments)
            //create combinator terms (carthesian product) from all known minimal terms
            |> Seq.collect (fun (id, arguments) -> 
                let arguments = arguments
                arguments 
                |> List.map (fun argument -> minimalClosedTerms.[argument] |> Seq.ofList) 
                |> enumerateCarthesianProduct 
                |> Seq.map (fun argumentTerms -> 
                    (1 + (argumentTerms |> List.sumBy fst), CombinatorTerm(id, argumentTerms |> List.map snd))))
            |> Seq.iter (fun newTermWithSize -> 
                    //if the new term is used, then consider non-terminals that use nonTerminal
                    if updateTermList nonTerminal newTermWithSize then relevantNonTerminals.UnionWith(useMap.[nonTerminal]))
        if relevantNonTerminals.Count > 0 then updateMinimalTerms relevantNonTerminals
    
    updateMinimalTerms (new HashSet<IntersectionType>(getKeys grammar))

    match minimalClosedTerms.TryGetValue(nonTerminal) with
    | (true, []) -> failwithf "No closed term can be deduced from %O" nonTerminal
    | (true, minimalTerms) -> minimalTerms |> List.sortBy fst |> List.map snd
    | (false, _) -> failwithf "Given non-terminal %O is not in the given grammar" nonTerminal

/// <summary>
/// Returns the set of all non-terminals that have no closed term representation in grammar.
/// </summary>
let getEmptyNonTerminals (grammar : TreeGrammar) = 
    let rec getEmptyNonTerminalsRec (emptyNonTerminals : Set<IntersectionType>) = 
        let revisedEmptyNonTerminals = 
            emptyNonTerminals 
            |> Set.filter (fun nonTerminal -> 
                Map.find nonTerminal grammar
                |> Set.forall (fun (_, arguments) -> 
                    List.exists (fun argument -> Set.contains argument emptyNonTerminals) arguments))
        if (Set.count revisedEmptyNonTerminals) = (Set.count emptyNonTerminals) then emptyNonTerminals else getEmptyNonTerminalsRec revisedEmptyNonTerminals
    getEmptyNonTerminalsRec (grammar |> getKeys |> Set.ofSeq)

/// <summary>
/// Decides whether a given closed combinator term is derivable in the given grammar.
/// </summary>
let rec isDerivable (grammar : TreeGrammar) (startSymbol : IntersectionType) : CombinatorTerm -> bool = function
    | CombinatorTerm(id1, t1s) -> 
        match Map.tryFind startSymbol grammar with
        | Some(expressions) ->
            expressions
            |> Set.exists (fun (id2, t2s) -> 
                (id1 = id2) 
                && ((List.length t1s) = (List.length t2s))
                && List.forall2 (isDerivable grammar) t2s t1s) 
        | None -> failwith (sprintf "Given grammar does not contain non-terminal %O." startSymbol)


(*
///DEPRECATED
//further ideas: 
// use priority queue (size of start non-terminal, max size of term, non-terminal) 
// based on the idea that for a term of size s starting at the start symbol only terms of sizes s' that are smaller (compute max) from other symbols are necessary

//bottom up, lazy, dynamic programming, using a dictionary as a priority queue
let enumerateClosedTerms (grammar : Map<IntersectionType, Set<CombinatorExpression>>) (nonTerminal : IntersectionType) = 
    let enumerateMapProduct size (sequences : list<Map<int, seq<_>>>) : seq<list<seq<_>>> =
        let rec enumerateMapProductRec size (sequences : list<Map<int, seq<_>>>) : seq<list<seq<_>>> = 
            match sequences with
            | [] -> if size = 0 then Seq.singleton [] else Seq.empty
            | s :: rest -> 
                seq { 
                    for entry in s do
                        if entry.Key <= size then
                            for js in enumerateMapProductRec (size - entry.Key) rest do
                                yield (entry.Value :: js)
                }
        if List.exists Map.isEmpty sequences then Seq.empty 
        else enumerateMapProductRec size sequences

    //build an inverse map that assigns to each type a set of types that are using it as an argument
    let useMap = 
        new System.Collections.Generic.Dictionary<IntersectionType, System.Collections.Generic.HashSet<IntersectionType>>
            (Map.ofSeq (grammar |> getKeys  |> Seq.map (fun tau -> (tau, new System.Collections.Generic.HashSet<IntersectionType>()))))
    for entry in grammar do
        for (_, arguments) in entry.Value do
            for argument in arguments do
                useMap.[argument].Add entry.Key |> ignore


    let result = new Dictionary<IntersectionType, Map<int, seq<CombinatorTerm>>>()
    //contains non-terminals that need to be considered
    let relevantNonTerminals = new HashSet<IntersectionType>()

    for entry in grammar do
        match entry.Value |> Seq.filter (function | (id, []) -> true | _ -> false) |> List.ofSeq with
        | [] -> result.Add(entry.Key, Map.empty)
        | expressions -> 
            result.Add(entry.Key, Map.ofList [(1, expressions |> List.map (fun (id, _) -> CombinatorTerm(id, [])) |> Seq.ofList)])
            relevantNonTerminals.UnionWith(useMap.[entry.Key])

    let enumeratePossibleSizes lowerBound nonTerminal =
        seq { 
            for (id, arguments) in grammar.[nonTerminal] do
                let sizeLists : list<seq<int>> = arguments |> List.map (fun argument -> result.[argument] |> getKeys)
                if List.forall (Seq.isEmpty >> not) sizeLists then
                    let minSize = max (lowerBound - 1) (List.sumBy (Seq.min) sizeLists)
                    let maxSize = List.sumBy (Seq.max) sizeLists
                    if minSize > maxSize then ()
                    else yield! [(1 + minSize)..(1 + maxSize)]}
        |> Seq.distinct

    //keep track of non-terminals to be considered for a given size
    let queue = new System.Collections.Generic.Dictionary<int, Set<IntersectionType>>()
    for relevantNonTerminal in relevantNonTerminals do
        for possibleSize in enumeratePossibleSizes 2 relevantNonTerminal do
            match queue.TryGetValue(possibleSize) with
            | (true, nonTerminals) -> queue.[possibleSize] <- Set.add relevantNonTerminal nonTerminals
            | (false, _) -> queue.[possibleSize] <- Set.singleton relevantNonTerminal
    seq {
        for entry in result.[nonTerminal] do
            for term in entry.Value do
                yield term
                //printfn "%O" term

        //while (queue.Count > 0) do
        for currentSize = 2 to (System.Int32.MaxValue - 1) do
            //if max queue < currentSize then abort ?
            if currentSize % 1 = 0 then printfn "%d" currentSize
            //printfn "%d" queue.Count
            System.Console.ReadKey() |> ignore
            match queue.TryGetValue(currentSize) with
            | (true, nonTerminals) ->
                //side effect and lazy evaluation together are dangerous
                //queue.Remove(currentSize) |> ignore
                let relevantNonTerminals = new HashSet<IntersectionType>()
                for currentNonTerminal in nonTerminals do
                    let currentExpressions = Map.find currentNonTerminal grammar
                    let foundClosedTerms : seq<CombinatorTerm> = 
                        seq {
                            for (id, arguments) in currentExpressions do
                                let closedArgumentSequenceStream = 
                                    arguments 
                                    |> List.map (fun argument -> result.[argument]) 
                                    |> enumerateMapProduct (currentSize - 1)
                                if not(Seq.isEmpty closedArgumentSequenceStream) then
                                    yield! closedArgumentSequenceStream
                                            |> Seq.collect (fun (closedArgumentSequences : list<seq<CombinatorTerm>>) -> enumerateCarthesianProduct closedArgumentSequences)
                                            |> Seq.map (fun (closedArguments : list<CombinatorTerm>) -> CombinatorTerm(id, closedArguments))}
                        |> Seq.distinct
                        |> Seq.cache

                    if not (Seq.isEmpty foundClosedTerms) then
                        if currentNonTerminal = nonTerminal then 
                            for term in foundClosedTerms do
                                //printfn "%O" term
                                yield term
                        result.[currentNonTerminal] <- Map.add currentSize (foundClosedTerms) result.[currentNonTerminal]
                        relevantNonTerminals.UnionWith(useMap.[currentNonTerminal])
                //update queue
                for relevantNonTerminal in relevantNonTerminals do
                    for possibleSize in enumeratePossibleSizes (currentSize + 1) relevantNonTerminal do
                        match queue.TryGetValue(possibleSize) with
                        | (true, nonTerminals) -> 
                            queue.[possibleSize] <- Set.add relevantNonTerminal nonTerminals
                        | (false, _) -> queue.[possibleSize] <- Set.singleton relevantNonTerminal
            | (false, _) -> () }


//*)