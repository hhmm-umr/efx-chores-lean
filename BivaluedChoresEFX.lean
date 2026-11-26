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

Formalization in Lean 4 + Mathlib of exact EFX existence theorems for additive chores:
* **Theorem B (`BivaluedChoresEFX.exists_efx_ratio_le_two`, `exists_efx_bivalued_ratio_le_two`)**:
  Exact EFX allocations always exist for arbitrary `n ≥ 1`, `m ≥ 0`, arbitrary agent types,
  and arbitrary personalized continuous/multi-valued additive costs `c i g ∈ [p i, 2 * p i]`
  (`0 < p i`) via Partial-Round-First Round-Robin (`PRFRR`).
* **Theorem C2 (`BivaluedChoresEFX.exists_efx_three_agent_types_bivalued`)**:
  Exact EFX allocations always exist for arbitrary `n ≥ 1`, `m ≥ 0`, three agent types with
  arbitrary personalized bi-valued costs `{p b, q b}` (`0 < p b ≤ q b`, unrestricted ratios),
  and all-large (`A`), unique-light (`B_0, B_1, B_2`), and all-small (`D`) chores via 2D discrete
  Sperner's Lemma (`BivaluedChoresEFX.sperner_2d`) and Chain/Star Bridges.
* **Theorem 1 (`BivaluedChoresEFX.exists_efx_two_agent_types_bivalued`)**:
  Exact EFX allocations always exist for arbitrary `n ≥ 1`, `m ≥ 0`, and personalized bi-valued
  additive chores with two types of agents (`v b g ∈ {p b, q b}`, `0 < p b ≤ q b`).
* **Identical Bi-Valued Agents (`BivaluedChoresEFX.exists_efx_identical_bivalued_norm`)**:
  Closed-form water-filling EFX allocation for any `n ≥ 1` identical bi-valued agents.
* **General-`n` Reductions (arbitrary agent types)**:
  * Modulo-`n` All-Large Reduction (`BivaluedChoresEFX.efx_add_all_large_round`)
  * All-Small Chore Insertion Lemma via acyclic most-envy graphs
    (`BivaluedChoresEFX.exists_efx_insert_all_small`,
     `BivaluedChoresEFX.exists_efx_extend_all_small`)
-/
