module

public import BivaluedChoresEFX.Basic
public import BivaluedChoresEFX.Reductions
public import BivaluedChoresEFX.IdenticalAgents
public import BivaluedChoresEFX.TwoAgentTypes

/-!
# BivaluedChoresEFX

Formalization in Lean 4 + Mathlib of:
* **Main Theorem (`BivaluedChoresEFX.exists_efx_two_agent_types_bivalued`)**:
  EFX allocations always exist for arbitrary `n ≥ 1`, `m ≥ 0`, and personalized bi-valued
  additive chores with two types of agents (`v b g ∈ {p b, q b}`, `0 < p b ≤ q b`).
* **Identical Bi-Valued Agents (`BivaluedChoresEFX.exists_efx_identical_bivalued_norm`)**:
  Closed-form water-filling EFX allocation for any `n ≥ 1` identical bi-valued agents.
* **General-`n` Reductions (arbitrary agent types)**:
  * Modulo-`n` All-Large Reduction (`BivaluedChoresEFX.efx_add_all_large_round`)
  * All-Small Chore Insertion Lemma via acyclic most-envy graphs
    (`BivaluedChoresEFX.exists_efx_insert_all_small`,
     `BivaluedChoresEFX.exists_efx_extend_all_small`)
-/
