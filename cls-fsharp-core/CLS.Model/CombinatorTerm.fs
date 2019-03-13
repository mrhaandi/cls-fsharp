module CLS.Model.CombinatorTerm

open CLS.Model.ID
open CLS.Model.Type

/// <summary>
/// (combinator id, list of variables according to arguments of the combinator)
/// </summary>
type CombinatorExpression = (ID * IntersectionType list)

/// <summary>
/// CombinatorTerm containing no combinator variables
/// </summary>
type CombinatorTerm =
  | CombinatorTerm of ID * List<CombinatorTerm>
  override this.ToString() =
    match this with
    | CombinatorTerm(id, args) ->
        System.String.Format("{0}({1})", id, String.concat ", " (args |> Seq.map (fun t -> t.ToString())))

/// <summary>
/// Types are non-terminals; combinator IDs are terminals.
/// </summary>
type TreeGrammar = Map<IntersectionType, Set<CombinatorExpression>>