module CLS.Algorithm.Subtyping

open CLS.Model.ID
open CLS.Model.Type

open Util
open Type

/// <summary>
/// Checks whether tau is a subtype of sigma.
/// <para>Precondition: tau, sigma contain no nested or empty Intersect and no t->Omega. </para>
/// </summary>
let isSimplifiedSubType (isAtomicSubtype : ID -> ID -> bool) : IntersectionType -> IntersectionType -> bool =
    let rec isSubTypeRec = function
        | _, t when isOmega t           -> true
        | s, _ when isOmega s           -> false
        //a variable is only lower equal omega or itself
        | Var(x1), t2                   -> match t2 with | Var(x2) -> x1 = x2 | _ -> false
        | t1, Intersect(ts)             -> ts |> Seq.forall (fun t2 -> isSubTypeRec (t1, t2)) 
        | Arrow(x1,y1), Arrow(x2, y2)   -> isSubTypeRec (x2, x1) && isSubTypeRec (y1, y2)
        | Constructor(id1, cvs1), 
          Constructor(id2, cvs2)        -> (List.length cvs1) = (List.length cvs2) 
                                           && isAtomicSubtype id1 id2 
                                           && (List.forall2 (fun t1 t2 -> isSubTypeRec (t1, t2)) cvs1 cvs2) 
        | Intersect(ts), Var(_) & t2    -> Set.contains t2 ts
        | Intersect(ts), t2 when Set.contains t2 ts -> true //cheap(for wide types), early abort, 2-10x speedup for wide types 2x slowdown for small types
        | Intersect(ts), t2 when isPath t2 -> Set.exists (fun t1 -> isSubTypeRec (t1, t2)) ts
        | Intersect(ts), Constructor(id2, cvs2) -> 
            let argumentLists : IntersectionType list list = 
                ts |> Seq.choose (function | Constructor(id1, cvs1) when List.length cvs1 = List.length cvs2 && isAtomicSubtype id1 id2 -> Some(cvs1) | _ -> None) |> List.ofSeq
            if List.isEmpty argumentLists then false
            else List.forall2 (fun t1 t2 -> isSubTypeRec (t1, t2)) (intersectArgumentLists argumentLists) cvs2
        | Intersect(ts), Arrow(x2, y2)  -> let targets = Seq.choose (function | Arrow(x1, y1) when isSubTypeRec (x2, x1) -> Some y1 | _ -> None) ts
                                           isSubTypeRec ((intersectSimplifiedTypes targets), y2)
        | _,_                           -> false
    fun (tau : IntersectionType) (sigma : IntersectionType) -> isSubTypeRec (tau, sigma)

/// <summary>
/// Checks whether sigma is a supertype of tau.
/// <para>Precondition: tau, sigma contain no nested or empty Intersect and no t->Omega. </para>
/// </summary>
let isSimplifiedSuperType (isAtomicSubtype : ID -> ID -> bool) (sigma : IntersectionType) (tau : IntersectionType) =
    isSimplifiedSubType isAtomicSubtype tau sigma

/// <summary>
/// Checks whether tau is a subtype of sigma.
/// </summary>
let isSubType (isAtomicSubtype : ID -> ID -> bool) (tau : IntersectionType) (sigma : IntersectionType) = 
    isSimplifiedSubType isAtomicSubtype (simplifyType tau) (simplifyType sigma)

/// <summary>
/// For a sequence (t_i | i in I) returns the maximal type t with: forall i in I t &lt;= t_i.
/// </summary>
let getInfimumOfSimplifiedTypes = intersectSimplifiedTypes


/// <summary>
/// For a sequence (t_i | i in I) returns the minimal type t with: forall i in I t_i &lt;= t.
/// </summary>
let getSupremumOfSimplifiedTypes (isAtomicSubtype : ID -> ID -> bool) (types : seq<IntersectionType>) =
    let rec getSupremumRec = function
        | s, t when isOmega s || isOmega t -> Omega
        | Var(x), Var(y) when x = y -> Var(x)
        | Arrow(x1, y1), Arrow(x2, y2) -> 
            match getSupremumRec (y1, y2) with
            | t when isOmega t -> Omega
            | t -> Arrow(getInfimumOfSimplifiedTypes [x1; x2], t)
        | Constructor(id1, cvs1), Constructor(id2, cvs2) when List.length cvs1 = List.length cvs2 && isAtomicSubtype id1 id2 -> 
            Constructor(id2, List.map2 (curry getSupremumRec) cvs1 cvs2)
        | Constructor(id1, cvs1), Constructor(id2, cvs2) when List.length cvs1 = List.length cvs2 && isAtomicSubtype id2 id1 -> 
            Constructor(id1, List.map2 (curry getSupremumRec) cvs1 cvs2)
        | Intersect(ts), t2 -> 
            seq {for t1 in ts do yield getSupremumRec (t1, t2)}
            |> intersectSimplifiedTypes
            |> deOrganize
        | t1, Intersect(ts) -> 
            seq {for t2 in ts do yield getSupremumRec (t1, t2)}
            |> intersectSimplifiedTypes
            |> deOrganize
        | _ -> Omega
    match Seq.length types with
    | 0 -> failwith "There is no minimal type."
    | 1 -> Seq.head types
    | _ -> types |> Seq.reduce (curry getSupremumRec)