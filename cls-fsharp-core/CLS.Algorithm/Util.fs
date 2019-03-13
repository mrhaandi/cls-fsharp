module CLS.Algorithm.Util

open System.Collections.Generic

(*
/// <summary>
/// Redefinition of the pipe operator, used for debugging
/// </summary>
#if DEBUG
let (|>) value func =
  let result = func value
  result
#endif
//*)

//-
//Misc functions
//-

/// <summary>
/// Given n sequences of elements enumerate the lists of n elements (one from each sequence).
/// </summary>
let rec enumerateCarthesianProduct (sequences : list<seq<_>>) = 
    match sequences with
    | [] -> Seq.singleton []
    | s :: rest -> 
        seq { 
            for js in enumerateCarthesianProduct rest do
                for i in s do
                    yield (i :: js)
        }


let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

/// <summary>
/// Given a function f maps a tuple (a, b) to (f a, f b). 
/// </summary>
let (|>>) (a, b) f = (f a, f b)

/// <summary>
/// Given a function f : a -> b, returns the memoized version of f using an internal lookup structure.
/// </summary>
let memoize f = 
    let dict = new System.Collections.Generic.Dictionary<_, _>()
    fun n -> 
        match dict.TryGetValue(n) with
        | (true, v) -> v
        | _ -> 
            let temp = f (n)
            dict.Add(n, temp)
            temp
(*
/// <summary>
/// Given n lists of elements enumerate the lists of n elements (one from each list).
/// If for a proper(!) sublist l with 0 &lt;= m &lt; n elements predicate l = false, then no further products containing l are considered.
/// predicate [] must be defined.
/// </summary>
let enumerateCarthesianProductBottomUp (predicate : list<'a> -> bool) (sequences : list<list<'a>>) =
    let rec enumerateCarthesianProductRec = function
        | [] -> Seq.singleton []
        | s :: rest -> seq {for js in Seq.filter predicate (enumerateCarthesianProductRec rest) do
                                for i in s do yield (i :: js)}

    if not (predicate []) then Seq.empty
    else if List.isEmpty sequences || List.exists List.isEmpty sequences then 
        Seq.singleton []
    else
        enumerateCarthesianProductRec sequences
*)

/// <summary>
/// Given n lists of elements enumerate the lists of n elements (one from each list).
/// If for a proper(!) sublist l with 0 &lt;= m &lt; n elements predicate l = false, then no further products containing l are considered.
/// predicate [] must be defined.
/// Disrespects the order of lists!
/// </summary>
let enumerateListProductBottomUp (predicate : list<'a> -> bool) (lists : list<list<'a>>) = 
    let (singletons, remainingSequences) = lists |> List.partition (fun sequence -> List.length sequence = 1)
    let initialProduct = singletons |> List.map List.head
    
    let rec enumerateCarthesianProductRec = 
        function 
        | [] -> Seq.singleton initialProduct
        | s :: rest -> 
            seq { 
                for js in Seq.filter predicate (enumerateCarthesianProductRec rest) do
                    for i in s do
                        yield (i :: js)
            }
    if not (predicate initialProduct) then Seq.empty
    else if List.isEmpty lists || List.exists List.isEmpty lists then Seq.singleton []
    else enumerateCarthesianProductRec remainingSequences


//-
//List functions
//-
let rec updateListAtIndex index element list = 
    match index, list with
    | 0, x :: xs -> element :: xs
    | i, x :: xs -> x :: (updateListAtIndex (index - 1) element xs)
    | _, [] -> failwith "index out of range"

let rec insertInListAtIndex (index, element) list = 
    match index, list with
    | 0, _ -> element :: list
    | i, x :: xs -> x :: (insertInListAtIndex ((index - 1), element) xs)
    | _, [] -> failwith "index out of range"

let rec removeFromListAtIndex index list = 
    match index, list with
    | 0, x :: xs -> xs
    | i, x :: xs -> x :: (removeFromListAtIndex (index - 1) xs)
    | _, [] -> failwith "index out of range"

//-
//Table functions
//-

/// <summary>
/// If table contains key, then return table.[key]; otherwise return defaultValue
/// </summary>
let findWithDefault (table : Dictionary<'a, 'b>) (defaultValue : 'b) (key : 'a) : 'b =
    match table.TryGetValue(key) with
    | true, value -> value
    | _ -> defaultValue


//-
//Set functions
//-
/// <summary>
/// Enumerates all subsets with at most maxSize elements.
/// </summary>
let rec enumerateSubsetsUpToSize maxSize set = 
    if Set.isEmpty set || maxSize = 0 then seq { yield Set.empty }
    else 
        let element = Set.minElement set
        let rest = Set.remove element set
        seq { 
            for subset in enumerateSubsetsUpToSize maxSize rest do
                yield subset
                if (Set.count subset < maxSize) then yield Set.add element subset
        }

/// <summary>
/// Enumerates (bottom up) all subsets.
/// </summary>
let enumerateSubsets set = enumerateSubsetsUpToSize (Set.count set) set


//(*
/// <summary>
/// Let N = {0, ..., "numberOfElements"-1}, given "covers" : sequence of (representative, subset of N),
/// enumerate all lists of representatives for minimal (w.r.t. set inclusion) set covers of N.
/// </summary>
let enumerateMinimalSetCovers (numberOfElements : int) (covers : list<'a * Set<int>>) = 
    let coverTable = Array.create numberOfElements []
    covers 
    |> List.iter 
           (fun (representative, cover) -> 
           cover |> Set.iter (fun element -> coverTable.[element] <- (representative, cover) :: coverTable.[element]))
    //if an element is covered by exactly one cover, then use the cover
    let necessaryCovers = 
        coverTable
        |> Array.fold (fun necessaryCovers -> 
               function 
               | [] -> failwith "At least one element cannot be covered."
               | [ cover ] -> Set.add cover necessaryCovers
               | _ -> necessaryCovers) Set.empty
        |> Set.toList
    
    let necessaryCoveredElements = 
        necessaryCovers
        |> List.map snd
        |> Set.unionMany
    
    let necessaryUsedRepresentatives = necessaryCovers |> List.map fst
    if Set.count necessaryCoveredElements = numberOfElements then Seq.singleton necessaryUsedRepresentatives
    else 
        let sets = 
            covers
            |> Seq.map (fun (representative, cover) -> (representative, Set.difference cover necessaryCoveredElements))
            |> Seq.filter (fun (_, cover) -> not (Set.isEmpty cover))
            |> Seq.toArray
        
        let maxIndex = ((Array.length sets) - 1)
        
        let inclusions = 
            sets |> Array.mapi (fun j (_, cover) -> 
                        [ 0..maxIndex ]
                        |> List.filter (fun i -> i <> j && Set.isSuperset cover (snd sets.[i]))
                        |> Set.ofList)
        
        let rec enumerateMinimalSetCoversRec minIndex currentIndices currentRepresentatives currentCover = 
            seq { 
                if Set.count currentCover = numberOfElements then yield currentRepresentatives
                else 
                    for j in [ minIndex..maxIndex ] do
                        let (representative, cover) = sets.[j]
                        if (not (Set.isEmpty (Set.difference cover currentCover))) 
                           && (List.forall (fun i -> not (Set.contains i inclusions.[j])) currentIndices) then 
                            let newIndices = j :: currentIndices
                            let newRepresentatives = representative :: currentRepresentatives
                            let newCover = Set.union currentCover cover
                            yield! enumerateMinimalSetCoversRec (j + 1) newIndices newRepresentatives newCover
            }
        
        enumerateMinimalSetCoversRec 0 [] necessaryUsedRepresentatives necessaryCoveredElements

//*)

/// <summary>
/// Given a partial order "partialOrder" and a "sequence" (t_i | i in I), return a sequence of maximal t_i.
/// If multiple elements in a sequence are equal, then only the last occurrence of such elements remains.
/// </summary>
let enumerateMaximalElements (partialOrder : 'a -> 'a -> bool) (sequence : seq<'a>) : seq<'a> = 
    let rec filterRedundantElementsRec filteredElements remainingElements =
        match remainingElements with
        | [] -> filteredElements |> List.toSeq
        | element1 :: rest -> 
            if List.exists (fun element2 -> partialOrder element1 element2) filteredElements 
               || List.exists (fun element2 -> partialOrder element1 element2) rest then 
                filterRedundantElementsRec filteredElements rest
            else filterRedundantElementsRec (element1 :: filteredElements) rest
    filterRedundantElementsRec [] (List.ofSeq sequence)

/// <summary>
/// Given a partial order "partialOrder" and a "sequence" (t_i | i in I), return a sequence of minimal t_i.
/// If multiple elements in a sequence are equal, then only the last occurrence of such elements remains.
/// </summary>
let enumerateMinimalElements (partialOrder : 'a -> 'a -> bool) = enumerateMaximalElements (fun x y -> partialOrder y x)

/// <summary>
/// Enumerates (bottom up) minimal subsets of "set" satisfying "predicate".
/// </summary>
let enumerateMinimalSufficientSubsets (predicate : Set<_> -> bool) set =
    let necessaryItems = set |> Set.filter (fun item -> not (predicate (Set.remove item set)))
    let otherItems = Set.difference set necessaryItems

    otherItems
    |> enumerateSubsets
    |> Seq.filter (fun subset -> predicate (Set.union necessaryItems subset))
    |> enumerateMaximalElements Set.isSuperset //maximal wrt isSuperset is minimal wrt isSubset
    |> Seq.map (fun subset -> Set.union necessaryItems subset)


/// <summary>
/// Enumerates (bottom up) all sublists of size n between minSize and maxSize.
/// </summary>
let enumerateSublists minSize maxSize sequence =
    let elements = Seq.toArray sequence
    let rec enumerateSubsequencesRec maxIndex currentSeq =
        seq {let currentSize = List.length currentSeq
             if currentSize >= minSize then yield currentSeq
             if currentSize + 1 <= maxSize then
                for j in [0..maxIndex] do 
                    let newSeq = (elements.[j]) :: currentSeq 
                    yield! enumerateSubsequencesRec (j-1) newSeq}

    seq { if 0 <= maxSize then yield! enumerateSubsequencesRec ((Array.length elements)-1) [] }