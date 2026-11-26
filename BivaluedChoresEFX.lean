module

public import BivaluedChoresEFX.Basic
public import BivaluedChoresEFX.Reductions
public import BivaluedChoresEFX.IdenticalAgents
public import BivaluedChoresEFX.TwoAgentTypes
public import BivaluedChoresEFX.RatioTwoChores
public import BivaluedChoresEFX.Sperner2D
public import BivaluedChoresEFX.ThreeAgentTypes

/-!
# BivaluedChoresEFX

A complete allocation assigns every indivisible chore to one agent. For each observer `i`,
EFX bounds the cost of her own bundle after removing any one chore by her cost for every
comparison bundle. The existence results allow `n ≥ 1` agents and `m ≥ 0` chores.

* `exists_efx_of_cost_le_sum_of_two` applies partial-round-first round-robin when costs are
  nonnegative and, for each agent, any two distinct chores together cost at least as much
  as any one. Theorem B (`exists_efx_ratio_le_two`) specializes this to each agent's own
  interval `[p i, 2 * p i]` with `p i > 0`. Its bi-valued corollary is
  `exists_efx_bivalued_ratio_le_two`.
* Theorem 1 (`exists_efx_two_agent_types_bivalued`) allows two type labels and arbitrary
  bi-valued cost profiles within each type, with `0 < p b ≤ q b`.
* Theorem C2 (`exists_efx_three_agent_types_bivalued`) allows three type labels with the
  same cost bounds when each chore has cost `p b` for zero, one, or all three types.
  Its proof uses `sperner_2d` and the single-item, chain, and star bridges.
* `exists_efx_identical_bivalued_norm` realizes the closed-form counts for identical agents.
  `efx_add_all_large_round` extends an EFX allocation by one maximal-cost chore per agent.
  `exists_efx_insert_all_small` and `exists_efx_extend_all_small` insert minimum-cost chores
  using a rotation of cheapest bundles.
-/
