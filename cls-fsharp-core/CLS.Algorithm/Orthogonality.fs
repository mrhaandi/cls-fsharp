module CLS.Algorithm.Orthogonality

open CLS.Model.ID
open CLS.Model.Type

open Type

/// <summary>
/// Given a type t, checks whether Omega leq! t.
/// </summary>
let rec doesMatchOmega = function
    | t when isOmega t -> true
    | Var(_) -> true
    | Arrow(_, t) -> doesMatchOmega t
    | Intersect(ts) -> Seq.forall doesMatchOmega ts
    | _ -> false //Constructor

/// <summary>
/// Overapproximates (false positives) whether tau leq! sigma is satisfiable. 
/// </summary>
let rec isPossiblySatisfiable (isAtomicSubtype : ID -> ID -> bool) = function
    | _, r when isOmega r -> true
    | l, r when isOmega l -> doesMatchOmega r
    | Var(_), _ -> true
    | _, Var(_) -> true
    | _, r when doesMatchOmega r -> true
    | t1, Intersect(ts) -> ts |> Seq.forall (fun t2 -> isPossiblySatisfiable isAtomicSubtype (t1, t2))
    | Intersect(ts), _ when Seq.exists (function | Var(_) -> true | _ -> false) ts -> true
    | Intersect(ts), Arrow(x2, y2) -> 
        let targets = Seq.choose (function | Arrow(x1, y1) when isPossiblySatisfiable isAtomicSubtype (x2, x1) -> Some y1 | _ -> None) ts
        isPossiblySatisfiable isAtomicSubtype ((intersectSimplifiedTypes targets), y2)
    | Intersect(ts), Constructor(id2, cvs2) -> 
        let argumentLists : IntersectionType list list = 
            ts |> Seq.choose (function | Constructor(id1, cvs1) when List.length cvs1 = List.length cvs2 && isAtomicSubtype id1 id2 -> Some(cvs1) | _ -> None) |> List.ofSeq
        if List.isEmpty argumentLists then false
        else List.forall2 (fun t1 t2 -> isPossiblySatisfiable isAtomicSubtype (t1, t2)) (intersectArgumentLists argumentLists) cvs2
    | Arrow(x1, y1), Arrow(x2, y2) -> isPossiblySatisfiable isAtomicSubtype (x2, x1) && isPossiblySatisfiable isAtomicSubtype (y1, y2)
    | Constructor(id1, cvs1), Constructor(id2, cvs2) -> 
        (List.length cvs1) = (List.length cvs2) && isAtomicSubtype id1 id2 
        && (List.forall2 (fun t1 t2 -> isPossiblySatisfiable isAtomicSubtype (t1, t2)) cvs1 cvs2) 
    | _,_ -> false

/// <summary>
/// Overapproximates (false positives) whether tau related to sigma, i.e. there is a type rho and substitution S with rho cap S(tau) leq S(sigma) and rho not leq S(sigma). 
/// Note: if tau is not related to sigma then tau leq! sigma might still be satisfiable.
/// </summary>
and isRelated (isAtomicSubtype : ID -> ID -> bool) (tau : IntersectionType) (sigma : IntersectionType) =
    match (tau, sigma) with
    | _, _ when isOmega tau || isOmega sigma -> false
    //for open types: is there asubstitution S such that rho cap S(tau) leq S(sigma) and rho not leq S(sigma)
    | Var(_), _                     -> true
    | _, Var(_)                     -> true
    | Intersect(ts), t2             -> ts |> Seq.exists (fun t1 -> isRelated isAtomicSubtype t1 t2) 
    //overapproximation (false positives). example: tau = a->a, sigma = (a->a) /\ (omega->a) are not related
    | t1, Intersect(ts)             -> ts |> Seq.exists (fun t2 -> isRelated isAtomicSubtype t1 t2)
    | Arrow(x1, y1), Arrow(x2, y2)  -> isPossiblySatisfiable isAtomicSubtype (x2, x1) && isRelated isAtomicSubtype y1 y2
    | Constructor(id1, []), Constructor(id2, []) -> isAtomicSubtype id1 id2 
    | Constructor(id1, cvs1), Constructor(id2, cvs2) -> 
        if (List.length cvs1) = (List.length cvs2) && isAtomicSubtype id1 id2 then
            //if cvs2 can be substituted by omegas, then cvs1 are relevant
            if List.forall doesMatchOmega cvs2 then true
            else List.exists2 (fun t1 t2 -> isRelated isAtomicSubtype t1 t2) cvs1 cvs2
        else false
    | _, _ -> false