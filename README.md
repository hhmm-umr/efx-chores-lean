# Exact EFX Existence for Personalized Bi-Valued & Bounded-Ratio Additive Chores

A complete, constructive mathematical suite and **zero-`sorry`, zero-warning Lean 4 (`v4.36.0`) + Mathlib4 formalization** (7,184 lines across 8 Lean files, standard axioms only) establishing **exact envy-free up to any chore (EFX)** existence across four general-$n$ regimes left open by Wentao He & Biaoshuai Tao (*"EFX for Additive Chores: Nonexistence, Pareto Incompatibility, and Bi-Valued Existence"*, `arXiv:2606.08872v2`, accepted to SODA '27).

## Main Formalized Theorems

### 1. Theorem B — Arbitrary $n$, Arbitrary Agent Types, Personalized Bounded-Ratio Chores $[p_i, 2p_i]$ (`RatioTwoChores.lean`)

```lean
theorem BivaluedChoresEFX.exists_efx_ratio_le_two
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, 0 < p i)
    (hlo : ∀ i g, p i ≤ cost i g)
    (hhi : ∀ i g, cost i g ≤ 2 * p i) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc
```

- Holds for **every** $n \ge 1$, **every** $m \ge 0$, **unlimited agent types**, **all $2^n$ chore types**, and **arbitrary continuous / multi-valued** personalized additive costs $c_i(g) \in [p_i, 2 p_i]$ (in particular, all personalized bi-valued instances with $q_i / p_i \le 2$, formalized directly as `exists_efx_bivalued_ratio_le_two`).
- Proved constructively via **Partial-Round-First Round-Robin (`PRFRR`)**: execute the partial round of size $m \bmod n$ *first*, then run $\lfloor m / n \rfloor$ full rounds in the same agent order.

### 2. Theorem C2 — Arbitrary $n$, Three Agent Types, Arbitrary Personalized Ratios $r_b > 1$ (`Sperner2D.lean`, `ThreeAgentTypes.lean`)

```lean
theorem BivaluedChoresEFX.exists_efx_three_agent_types_bivalued
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (cls : Fin n → Fin 3)
    (v : Fin 3 → Fin m → ℝ)
    (h_types : ∀ i g, cost i g = v (cls i) g)
    (p q : Fin 3 → ℝ)
    (hp : ∀ b, 0 < p b) (hpq : ∀ b, p b ≤ q b)
    (hbiv : ∀ b g, v b g = p b ∨ v b g = q b)
    (h_no_two_light : ∀ g,
      (v 0 g = p 0 ∧ v 1 g = p 1 → v 2 g = p 2) ∧
      (v 0 g = p 0 ∧ v 2 g = p 2 → v 1 g = p 1) ∧
      (v 1 g = p 1 ∧ v 2 g = p 2 → v 0 g = p 0)) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc
```

- Holds for **every** $n = t_0 + t_1 + t_2 \ge 1$, **every** $m \ge 0$, **three agent types** with **completely unrestricted personalized ratios** $r_b = q_b / p_b > 1$, and all-large ($A$), unique-light ($B_0, B_1, B_2$), and all-small ($D$) chores.
- Proved via **Unified Total-Chore Simplex $\Sigma$**, **Conservative Envy $\widehat{E}_b$** (giving automatic Sperner boundary conditions without boundary walks), a self-contained **`ZMod 2` 2D Discrete Sperner's Lemma (`sperner_2d`)**, exact rainbow-triangle extraction, **Subcase 4a (`threeTypeSpec_of_subcase4a`)**, and **Subcase 4b Chain/Star Bridges (`threeTypeSpec_chain_bridge`, `threeTypeSpec_star_bridge`)**.

### 3. Theorem 1 — Arbitrary $n$, Two Agent Types, Full Personalized Bi-Valued Chores (`TwoAgentTypes.lean`)

```lean
theorem BivaluedChoresEFX.exists_efx_two_agent_types_bivalued
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (cls : Fin n → Bool)
    (v : Bool → Fin m → ℝ)
    (h_types : ∀ i g, cost i g = v (cls i) g)
    (p q : Bool → ℝ)
    (hp : ∀ b, 0 < p b) (hpq : ∀ b, p b ≤ q b)
    (hbiv : ∀ b g, v b g = p b ∨ v b g = q b) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc
```

- Resolves the full unrestricted 2-agent-type bi-valued regime (all 4 chore types $A, B, C, D$, arbitrary $n \ge 1$, arbitrary personalized ratios $r_1, r_2 > 1$) via closed-form water-filling (`IdenticalAgents.lean`), a 3-phase Discrete Bolzano Walk, and a Single-Item Jump Bridge — delineating the exact bi-valued vs. tri-valued phase transition against He & Tao (2026).

### 4. General-$n$ Reductions & Identical-Agent Water-Filling (`Reductions.lean`, `IdenticalAgents.lean`)

1. **Modulo-$n$ All-Large Chore Reduction** (`BivaluedChoresEFX.efx_add_all_large_round`): Adding $n$ all-large chores preserves EFX for arbitrary $n$ and arbitrary additive costs.
2. **All-Small Chore Insertion Lemma** (`BivaluedChoresEFX.exists_efx_insert_all_small`, `BivaluedChoresEFX.exists_efx_extend_all_small`): Arbitrary numbers of all-small chores can be inserted while preserving EFX via acyclic most-envy DAG sinks of minimum-social-cost EFX allocations.
3. **Closed-Form Identical Bi-Valued EFX** (`BivaluedChoresEFX.exists_efx_identical_bivalued_norm`): Explicit water-filling EFX allocation `IdenticalEFX` for arbitrary $n \ge 1$ identical bi-valued agents.

## Repository Structure

| File | Lines | Contents |
|---|---:|---|
| [BivaluedChoresEFX.lean](BivaluedChoresEFX.lean) | 34 | Root module re-exporting all 7 modules |
| [BivaluedChoresEFX/Basic.lean](BivaluedChoresEFX/Basic.lean) | 222 | `bundle`, `bundleCost`, `IsEFX`, scaling/reindexing invariance, `exists_assignment_with_counts` |
| [BivaluedChoresEFX/Reductions.lean](BivaluedChoresEFX/Reductions.lean) | 483 | `efx_add_all_large_round`, acyclic most-envy DAG sink, `exists_efx_insert_all_small`, `exists_efx_extend_all_small` |
| [BivaluedChoresEFX/IdenticalAgents.lean](BivaluedChoresEFX/IdenticalAgents.lean) | 1750 | `IdenticalEFX`, internal EFX, Fundamental Bound, Lemmas A/B/C, `phase1_bundle_lower_bound` |
| [BivaluedChoresEFX/TwoAgentTypes.lean](BivaluedChoresEFX/TwoAgentTypes.lean) | 949 | `discrete_bolzano`, `TwoTypeSpec`, Phase 1/2/3 + Bridge, `exists_efx_identical_bivalued_norm`, `exists_efx_two_agent_types_bivalued` |
| [BivaluedChoresEFX/RatioTwoChores.lean](BivaluedChoresEFX/RatioTwoChores.lean) | 524 | Partial-Round-First Round-Robin (`PRFRR`), `exists_efx_ratio_le_two`, `exists_efx_bivalued_ratio_le_two` |
| [BivaluedChoresEFX/Sperner2D.lean](BivaluedChoresEFX/Sperner2D.lean) | 269 | Self-contained `ZMod 2` proof of 2D Discrete Sperner's Lemma (`sperner_2d`) |
| [BivaluedChoresEFX/ThreeAgentTypes.lean](BivaluedChoresEFX/ThreeAgentTypes.lean) | 2953 | `pileTau_mono_p`, `tildeTau` bounds, `ThreeTypeSpec`, 1-Item / Chain / Star Bridges, `exists_threeTypeSpec`, `exists_efx_three_agent_types_bivalued` |
| [PROOF.md](PROOF.md) | — | Self-contained human-readable mathematical proof companion |
| **Total Lean Code** | **7184** | **0 errors, 0 warnings, 0 `sorry`** |

## Building and Verification

Requires Lean `v4.36.0` (pinned in [lean-toolchain](lean-toolchain)) and Mathlib `v4.36.0` (pinned in [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json)).

```bash
lake exe cache get   # optional: fetch prebuilt Mathlib oleans
lake build
```

### Verification Summary

- **Fresh clean build**: all 8 Lean targets (`Basic`, `Sperner2D`, `RatioTwoChores`, `Reductions`, `IdenticalAgents`, `TwoAgentTypes`, `ThreeAgentTypes`, `BivaluedChoresEFX`) compile cleanly with **0 errors**, **0 warnings**, and **0 `sorry`** (`Build completed successfully (6386 jobs)`).
- **Complete Axiom Audit** (`#print axioms`):

```lean
'BivaluedChoresEFX.exists_efx_ratio_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_bivalued_ratio_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_three_agent_types_bivalued' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_threeTypeSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.sperner_2d' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_two_agent_types_bivalued' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_identical_bivalued_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.efx_add_all_large_round' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_insert_all_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_extend_all_small' depends on axioms: [propext, Classical.choice, Quot.sound]
```
