module CLS.Model.Type

open CLS.Model.ID

type IntersectionType = 
    | Var of ID
    | Arrow of IntersectionType * IntersectionType
    | Constructor of ID * IntersectionType list
    | Intersect of Set<IntersectionType>
    override this.ToString() = 
        match this with
        | Arrow(Arrow(_) & x, y) -> System.String.Format("({0})->{1}", x.ToString(), y.ToString())
        | Arrow(x, y) -> System.String.Format("{0}->{1}", x.ToString(), y.ToString())
        | Intersect(ts) when Set.isEmpty ts -> "omega"
        | Intersect(ts) -> System.String.Format("[{0}]", String.concat ", " (ts |> Seq.map (fun t -> t.ToString())))
        | Constructor(id, []) -> id.ToString()
        | Constructor(id, cvs) -> 
            System.String.Format("{0}({1})", id, String.concat ", " (cvs |> Seq.map (fun t -> t.ToString())))
        | Var(x) -> x.ToString()

/// <summary>
/// Universal type.
/// </summary>
let Omega = Intersect (Set.empty)


/// <summary>
/// Partial function from variable names to types.
/// </summary>
type Substitution = Map<ID, IntersectionType>

/// <summary>
/// List of assignments of combinator names to types.
/// </summary>
type Environment = list<ID * IntersectionType>
