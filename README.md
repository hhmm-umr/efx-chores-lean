# Exact EFX for personalized bi-valued and bounded-cost additive chores

This Lean 4 formalization gives three existence results for any number of agents $n\ge 1$ and any number of indivisible chores $m\ge 0$. A complete allocation assigns every chore to exactly one agent. It is **envy-free up to any chore (EFX)** if, for every pair $i,j$ and every chore $g$ assigned to $i$,

$$c_i(X_i\setminus\{g\})\le c_i(X_j).$$

Both bundles are evaluated by agent $i$, and bundle costs are additive. An agent **type** specifies a full cost profile across chores. A type can contain any number of agents.

| Result | Agent types | Restriction on costs |
|---|---|---|
| PRFRR, including Theorem B | Arbitrary | For each agent, costs are nonnegative and the largest cost is at most the sum of the two smallest when $m\ge 2$. This includes all costs in a personal interval $[p_i,2p_i]$ with $p_i>0$. |
| Theorem 1 | At most two | Each type $b$ has its own values $0<p_b\le q_b$. All four light/heavy patterns are allowed. |
| Theorem C2 | Three type labels | Each type has its own values $0<p_b\le q_b$. Each chore is light for zero, one, or all three types. |

The supporting results include closed-form bundle sizes for identical agents and two ways to extend an existing EFX allocation. The proof guide works through the round-robin comparison and the exchange at a two-type crossing. [Proof guide](PROOF.md)

## Main formalized theorems

### Theorem B and its extension to sums of two chore costs

```lean
theorem exists_efx_ratio_le_two
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i)
    (hlo : ∀ i g, p i ≤ cost i g)
    (hhi : ∀ i g, cost i g ≤ 2 * p i) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc
```

In partial-round-first round-robin (PRFRR), the first $m\bmod n$ agents each pick a cheapest remaining chore. All agents then pick in the same order for $\lfloor m/n\rfloor$ full rounds. The stronger theorem uses the following hypothesis for each agent $i$ and all chores $g,a,b$.

$$a\ne b \quad\Longrightarrow\quad c_i(g)\le c_i(a)+c_i(b).$$

Here $a,b$ are distinct chores, and their costs may tie. For $m\ge 2$ it suffices to compare the maximum with the sum of the two smallest entries in that agent's row, counting multiplicities. For $m\le 1$ the pair condition is vacuous. The row $(1,2,2,3)$ satisfies the condition and has maximum-to-minimum ratio $3$. The general theorem is `exists_efx_of_cost_le_sum_of_two`. The interval theorem above and `exists_efx_bivalued_ratio_le_two` follow directly. [Round-robin proofs](BivaluedChoresEFX/RatioTwoChores.lean)

He and Tao already give an arbitrary-$n$ algorithm for the common two-value set $\{1,r\}$ with $r\le 2$ in Section 5 of their paper. Their partial first round takes its agents in reverse order. Theorem B uses a forward partial round and allows every real cost in each agent's personal interval. [He and Tao, Section 5](https://arxiv.org/html/2606.08872v2#S5)

### Theorem C2 for three type labels

```lean
theorem exists_efx_three_agent_types_bivalued
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

A chore is light for type $b$ exactly when its cost equals $p_b$. The permitted sets of light types are $\varnothing$, $\{0\}$, $\{1\}$, $\{2\}$, and $\{0,1,2\}$. The theorem includes empty types, constant profiles ($q_b=p_b$), and unbounded personalized ratios $q_b/p_b$. Its proof uses the two-dimensional discrete Sperner lemma, then resolves the rainbow triangle by a single-item, chain, or star bridge. [Three-type proof](BivaluedChoresEFX/ThreeAgentTypes.lean) · [Sperner lemma](BivaluedChoresEFX/Sperner2D.lean)

### Theorem 1 for two agent types

```lean
theorem exists_efx_two_agent_types_bivalued
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

There is no restriction on which types find a given chore light. The proof balances bundles within each type, follows a discrete path between the two piles, and exchanges a chore across piles when the envy inequalities change at consecutive states. He and Tao's three-value counterexamples also use only two agent types, for every $n\ge4$. Their four-agent bi-valued existence theorem uses a common pair of costs across the agents. [Two-type proof](BivaluedChoresEFX/TwoAgentTypes.lean) · [He and Tao, Sections 3–5](https://arxiv.org/html/2606.08872v2#S3)

## Reductions and identical agents

For nonnegative additive costs, `efx_add_all_large_round` assigns one new chore to each agent when all new chores attain each observer's maximum cost. This reduces the number of such chores to consider modulo $n$. For a chore of minimum cost to every agent, `exists_efx_insert_all_small` finds an EFX allocation with an envy-free recipient by rotating old bundles on one cycle of cheapest-bundle choices. `exists_efx_extend_all_small` repeats the insertion. [Reductions](BivaluedChoresEFX/Reductions.lean)

For identical agents with normalized costs $\{1,r\}$ and $r>1$, `pileLarge` and `pileSmall` give the counts in each bundle. `exists_efx_identical_bivalued_norm` realizes those counts as a complete allocation. [Water-filling formulas](BivaluedChoresEFX/IdenticalAgents.lean) · [Realization theorem](BivaluedChoresEFX/TwoAgentTypes.lean)

## Repository structure

| File | Contents |
|---|---|
| [BivaluedChoresEFX.lean](BivaluedChoresEFX.lean) | Root module re-exporting the seven modules below |
| [Basic.lean](BivaluedChoresEFX/Basic.lean) | Bundles, additive costs, `IsEFX`, scaling, reindexing, and realization of prescribed counts |
| [Reductions.lean](BivaluedChoresEFX/Reductions.lean) | All-large rounds, rotation of cheapest bundles, and all-small insertion |
| [IdenticalAgents.lean](BivaluedChoresEFX/IdenticalAgents.lean) | Water-filling formulas, internal EFX, and bounds on thresholds and bundle sizes |
| [TwoAgentTypes.lean](BivaluedChoresEFX/TwoAgentTypes.lean) | Discrete crossing, `TwoTypeSpec`, the single-item bridge, and the two-type theorem |
| [RatioTwoChores.lean](BivaluedChoresEFX/RatioTwoChores.lean) | PRFRR, the bound by two distinct chores, and the ratio-two corollaries |
| [Sperner2D.lean](BivaluedChoresEFX/Sperner2D.lean) | Parity proof of the two-dimensional discrete Sperner lemma |
| [ThreeAgentTypes.lean](BivaluedChoresEFX/ThreeAgentTypes.lean) | Pile bounds, `ThreeTypeSpec`, rainbow triangle cases, bridges, and C2 |

## Building and verification

The project pins Lean and Mathlib to `v4.36.0`. Run the build from the repository root. The `--wfail` option treats build warnings as failures. [Lean toolchain](lean-toolchain) · [Lake configuration](lakefile.toml) · [Dependency manifest](lake-manifest.json)

```bash
lake exe cache get   # optional, fetch prebuilt Mathlib files
lake --wfail build
```

The eight project modules pass this build. Each declaration below depends only on `propext`, `Classical.choice`, and `Quot.sound`. Reproduce the axiom check through the root module after building.

```bash
lake env lean --stdin <<'LEAN'
import BivaluedChoresEFX
open BivaluedChoresEFX
#print axioms exists_efx_of_cost_le_sum_of_two
#print axioms exists_efx_ratio_le_two
#print axioms exists_efx_bivalued_ratio_le_two
#print axioms exists_efx_two_agent_types_bivalued
#print axioms exists_twoTypeSpec
#print axioms exists_efx_identical_bivalued_norm
#print axioms exists_efx_three_agent_types_bivalued
#print axioms exists_threeTypeSpec
#print axioms sperner_2d
#print axioms efx_add_all_large_round
#print axioms exists_efx_with_envy_free_agent
#print axioms exists_efx_insert_all_small
#print axioms exists_efx_extend_all_small
LEAN
```
