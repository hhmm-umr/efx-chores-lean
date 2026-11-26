# EFX Existence for Personalized Bi-Valued Additive Chores with Two Agent Types

A complete, constructive mathematical proof and **zero-`sorry`, zero-warning Lean 4 + Mathlib4 formalization** proving that **envy-free up to any chore (EFX)** allocations **always exist** for arbitrary numbers of agents $n \ge 1$ and chores $m \ge 0$ in personalized bi-valued additive chores instances with **two types of agents**.

## Main Theorem

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

In plain mathematics:

> **Theorem.** For every $n \ge 1$, every $m \ge 0$, every partition of the $n$ agents into two types $T_1, T_2$, and every additive disutility profile in which each type $b \in \{1, 2\}$ assigns every chore a cost in $\{p_b, q_b\}$ for arbitrary reals $0 < p_b \le q_b$ (allowing personalized ratios $q_1/p_1 \ne q_2/p_2$ and arbitrary disagreements between types on which chores are large or small), there **always** exists a complete EFX allocation.

### Research Context

In *EFX for Additive Chores: Nonexistence, Pareto Incompatibility, and Bi-Valued Existence* (Wentao He & Biaoshuai Tao, `arXiv:2606.08872v2`, 2026), two-agent-type instances were shown to be strong enough to yield tri-valued EFX nonexistence and bi-valued EFX+PO incompatibility for all $n \ge 4$, while general bi-valued EFX existence was established only up to $n \le 4$. This work resolves the general-$n$ bi-valued two-agent-type regime positively and constructively for all $n \ge 1$ and all personalized bi-valued ratios.

## Additional General-$n$ Theorems Included

Beyond the main theorem, this repository also formalizes general-$n$ results that hold for **arbitrary** agent types and arbitrary additive valuations:

1. **Modulo-$n$ All-Large Chore Reduction** (`BivaluedChoresEFX.efx_add_all_large_round`): Adding $n$ all-large chores (one per agent) preserves EFX for arbitrary $n$ and arbitrary additive disutilities.
2. **All-Small Chore Insertion Lemma** (`BivaluedChoresEFX.exists_efx_insert_all_small`, `BivaluedChoresEFX.exists_efx_extend_all_small`): For arbitrary $n \ge 1$ and arbitrary nonnegative additive disutilities, any number of all-small chores can be inserted into an EFX-solvable instance while preserving EFX. The proof selects a global minimum-social-cost EFX allocation, proves its most-envy digraph is acyclic, and gives the new all-small chore to a sink (an envy-free agent).
3. **Closed-Form Identical Bi-Valued EFX** (`BivaluedChoresEFX.exists_efx_identical_bivalued_norm`): Explicit water-filling EFX allocation `IdenticalEFX` for arbitrary $n \ge 1$ identical bi-valued agents.

## Proof Architecture

See [PROOF.md](PROOF.md) for the full self-contained mathematical writeup. In brief:

1. **Normalization & All-Small Elimination**: Rescale each type by $1/p_b > 0$ so costs lie in $\{1, r_b\}$ ($r_b > 1$), handle degenerate single-type cases via `IdenticalEFX`, and strip all-small chores $D$ via `exists_efx_extend_all_small`.
2. **Closed-Form Water-Filling Pile (`IdenticalEFX`)**: For a pile of $t$ identical agents with $p$ large chores and $s$ small chores ($K = \lceil r \rceil$), define explicit bundle counts (`pileLarge`, `pileSmall`), envy threshold (`pileTau`), minimum bundle size (`pileMinSize`), and large-bundle witness (`maxLargeIdx`, `maxLargeSize`).
3. **Three-Phase Discrete Bolzano Walk**:
   - **Phase 1 & Phase 3 (No-Jump)**: Moving $B$-chores (resp. $C$-chores via exact symmetry `TwoTypeSpec.swap`) never experiences an envy jump, proved unconditionally by `phase1_bundle_lower_bound`.
   - **Phase 2 (Single-Item Jump-Bridge)**: At any Phase-2 envy jump $E_2(a_1) \land E_1(a_1 + 1)$, three universal single-pile lemmas—**Lemma A** (`pileTau_step_lt`, `pileTau_step_le_tight`), **Lemma B** (`pileMinSize_sub_one_ge`), and **Lemma C** (`pileTau_sub_one_le_of_maxLargeSize`)—pin $M_1(a_1) = M_2(a_2 - 1) = M^* \ge 1$ with $n_B, n_C \ge 1$ and prove that at least one of the two single-item cross-pile bridge states $B_{\text{moveB}}$ or $B_{\text{moveC}}$ is EFX.

## Repository Structure

| File | Lines | Contents |
|---|---:|---|
| [BivaluedChoresEFX.lean](BivaluedChoresEFX.lean) | 22 | Root module importing all components |
| [BivaluedChoresEFX/Basic.lean](BivaluedChoresEFX/Basic.lean) | 222 | `bundle`, `bundleCost`, `IsEFX`, scaling/reindexing invariance, `exists_assignment_with_counts` |
| [BivaluedChoresEFX/Reductions.lean](BivaluedChoresEFX/Reductions.lean) | 483 | `efx_add_all_large_round`, acyclic most-envy DAG sink, `exists_efx_insert_all_small`, `exists_efx_extend_all_small` |
| [BivaluedChoresEFX/IdenticalAgents.lean](BivaluedChoresEFX/IdenticalAgents.lean) | 1750 | `IdenticalEFX`, internal EFX, Fundamental Bound, Lemmas A/B/C, `phase1_bundle_lower_bound` |
| [BivaluedChoresEFX/TwoAgentTypes.lean](BivaluedChoresEFX/TwoAgentTypes.lean) | 949 | `discrete_bolzano`, `TwoTypeSpec`, Phase 1/2/3 + Bridge, `exists_efx_identical_bivalued_norm`, `exists_efx_two_agent_types_bivalued` |
| [PROOF.md](PROOF.md) | 85 | Self-contained human-readable mathematical proof |

## Building and Verification

Requires Lean `v4.36.0` (pinned in [lean-toolchain](lean-toolchain)) and Mathlib `v4.36.0` (pinned in [lakefile.toml](lakefile.toml) and [lake-manifest.json](lake-manifest.json)).

```bash
lake exe cache get   # optional: fetch prebuilt Mathlib oleans
lake build
```

### Verification Summary

- **Compiler status**: `lake build` succeeds with **0 errors**, **0 warnings**, and **0 `sorry`** (using Lean 4.36's `module` system across all modules).
- **Axiom audit** (`#print axioms`):

```lean
'BivaluedChoresEFX.exists_efx_two_agent_types_bivalued' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_identical_bivalued_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_twoTypeSpec' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.efx_add_all_large_round' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_insert_all_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'BivaluedChoresEFX.exists_efx_extend_all_small' depends on axioms: [propext, Classical.choice, Quot.sound]
```
