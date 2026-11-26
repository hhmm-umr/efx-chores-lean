# Mathematical Proof Companion: Exact EFX Existence for Personalized Bi-Valued & Bounded-Ratio Additive Chores

This document presents the self-contained mathematical proofs of all major theorems formalized in Lean 4 (`v4.36.0` + Mathlib4) in this repository.

---

## 1. Problem Setup and Research Context

We consider allocating $m \ge 0$ indivisible chores $M$ among $n \ge 1$ agents $N$ with additive disutilities $c_i : M \to \mathbb{R}_{>0}$. A complete allocation $X = (X_1, \dots, X_n)$ partitioning $M$ is **envy-free up to any chore (EFX)** if for all $i, j \in N$ and every $g \in X_i$,
$$c_i(X_i \setminus \{g\}) \le c_i(X_j).$$

In *EFX for Additive Chores: Nonexistence, Pareto Incompatibility, and Bi-Valued Existence* (Wentao He & Biaoshuai Tao, `arXiv:2606.08872v2`, SODA '27), two-agent-type instances were used to prove that for all $n \ge 4$, tri-valued EFX allocations need not exist and bi-valued EFX+PO allocations need not exist, while exact bi-valued EFX existence was proved up to $n \le 4$. This repository proves and machine-verifies four general-$n$ positive theorems:

1. **General-$n$ Reductions** (`Reductions.lean`): Modulo-$n$ all-large elimination and iterated all-small insertion for arbitrary additive valuations.
2. **Theorem 1** (`IdenticalAgents.lean`, `TwoAgentTypes.lean`): Complete exact EFX for **all $n \ge 1$**, **2 agent types**, arbitrary personalized bi-valued costs $\{p_b, q_b\}$, all 4 chore types.
3. **Theorem B** (`RatioTwoChores.lean`): Complete exact EFX for **all $n \ge 1$**, **arbitrary agent types**, **all $2^n$ chore types**, and **arbitrary continuous / multi-valued** personalized costs $c_i(g) \in [p_i, 2 p_i]$.
4. **Theorem C2** (`Sperner2D.lean`, `ThreeAgentTypes.lean`): Complete exact EFX for **all $n \ge 1$**, **3 agent types**, arbitrary personalized bi-valued costs $\{p_b, q_b\}$ (unrestricted ratios $r_b > 1$), on all-large ($A$), unique-light ($B_0, B_1, B_2$), and all-small ($D$) chores via 2D discrete Sperner's Lemma and Chain/Star Bridges.

---

## 2. General-$n$ Reductions (`Reductions.lean`)

- **Modulo-$n$ All-Large Reduction (`efx_add_all_large_round`)**: For arbitrary $n \ge 1$ and arbitrary additive costs, giving one all-large chore (maximal cost for every agent) to each agent preserves EFX.
- **All-Small Insertion Lemma (`exists_efx_insert_all_small`, `exists_efx_extend_all_small`)**: Take an EFX allocation $X$ on the current chores minimizing total social cost $\sum_i c_i(X_i)$. Its **most-envy digraph** $E(i, j) \iff c_i(X_j) = \min_k c_i(X_k) < c_i(X_i)$ is acyclic (rotating along a cycle preserves EFX while strictly reducing total social cost). Hence it admits a sink $s$ (an envy-free agent). Assigning any all-small chore $g$ to $s$ preserves EFX because for all $g' \in X_s \cup \{g\}$, $c_s((X_s \cup \{g\}) \setminus \{g'\}) = c_s(X_s) + c_s(g) - c_s(g') \le c_s(X_s) \le c_s(X_k)$. $\square$

---

## 3. Theorem B: Arbitrary $n$, Arbitrary Agent Types, Costs in $[p_i, 2p_i]$ (`RatioTwoChores.lean`)

**Theorem (`exists_efx_ratio_le_two`).** For every $n \ge 1$, $m \ge 0$, and additive disutilities satisfying $0 < p_i \le c_i(g) \le 2 p_i$ for all $i, g$, **Partial-Round-First Round-Robin (`PRFRR`)** outputs an exact EFX allocation.

*Proof.* Write $m = q n + u$ with $0 \le u < n$. Fix an arbitrary agent order $0, 1, \dots, n - 1$:
- **Round 0 (partial round first)**: agents $0, 1, \dots, u - 1$ each pick their minimum-cost remaining chore.
- **Rounds $1, \dots, q$ (full rounds)**: in each round, agents $0, 1, \dots, n - 1$ sequentially pick their minimum-cost remaining chore.

Let $g_{i, r}$ be the chore picked by agent $i$ in round $r$. For any two agents $i \ne j$ and any $h \in X_i$:
1. **If $i < j$**: In every full round $r \in \{1, \dots, q\}$, agent $i$ picks *before* agent $j$, so $c_i(g_{i, r}) \le c_i(g_{j, r})$.
   - If $i \ge u$ (both $i, j$ have $q$ items): $c_i(X_i \setminus \{h\}) \le c_i(X_i) = \sum_{r=1}^q c_i(g_{i,r}) \le \sum_{r=1}^q c_i(g_{j,r}) = c_i(X_j)$.
   - If $i < u \le j$ ($i$ has $q + 1$ items, $j$ has $q$ items): $i$'s round-0 pick $g_{i, 0}$ precedes every chore in $X_i \setminus \{g_{i, 0}\}$, so $c_i(g_{i, 0}) \le c_i(h)$; hence $c_i(X_i \setminus \{h\}) \le c_i(X_i \setminus \{g_{i, 0}\}) = \sum_{r=1}^q c_i(g_{i,r}) \le \sum_{r=1}^q c_i(g_{j,r}) = c_i(X_j)$.
   - If $i < j < u$ (both have $q + 1$ items): $c_i(g_{i, 0}) \le c_i(g_{j, 0})$ as well, so $c_i(X_i \setminus \{h\}) \le c_i(X_i) \le c_i(X_j)$.
2. **If $j < i$**: In round $r \in \{1, \dots, q - 1\}$, agent $i$ picks before agent $j$'s round-$(r + 1)$ pick, so $c_i(g_{i, r}) \le c_i(g_{j, r + 1})$ (and if $j < u$, $c_i(g_{i, 0})$ when $i < u$ precedes $g_{j, 1}$ as well). Summing the shifted rounds cancels all but one item on each side, leaving at most:
   - When $j < u \le i$ ($i$ has $q$ items, $j$ has $q + 1$ items): $c_i(X_i \setminus \{h\}) \le \sum_{r=1}^{q-1} c_i(g_{j, r+1}) \le c_i(X_j)$ (since $c_i(g_{i, q}) - c_i(h) \le 2 p_i - p_i = p_i \le c_i(g_{j, 0})$ and $c_i(g_{j, 1}) \ge p_i$!).
   - When both have $q$ items (or both have $q + 1$ items): removing $h \in X_i$ drops at least $p_i$, while the single unmatched final-round item of $i$ has cost at most $2 p_i$, so $c_i(g_{i, q}) - c_i(h) \le 2 p_i - p_i = p_i \le c_i(g_{j, \text{first}})$. Thus $c_i(X_i \setminus \{h\}) \le c_i(X_j)$ unconditionally. $\square$

*(Corollary `exists_efx_bivalued_ratio_le_two`: every personalized bi-valued chores instance with $1 \le q_i / p_i \le 2$ admits an exact EFX allocation for all $n, m$.)*

---

## 4. Closed-Form `IdenticalEFX` Water-Filling Pile (`IdenticalAgents.lean`)

For $t \ge 1$ identical agents with normalized costs $\{1, r\}$ ($r > 1$, $K = \lceil r \rceil \ge 2$), given $p = \ell t + u$ ($0 \le u < t$) own-large items and $s$ own-small items ($\mathrm{cap} = (t - u) K$), `IdenticalEFX` assigns $\ell + 1$ large items to indices $i < u$ and $\ell$ large items to $i \ge u$, and fills small items in closed form (Regime U: $s \le \mathrm{cap}$; Regime O: $s > \mathrm{cap}$).

Denote by $\tau(t, p, s; r)$ (`pileTau`) its closed-form maximum EFX threshold, by $M(t, p, s; K)$ (`pileMinSize`) its minimum bundle cardinality, and by $L_{\max}(t, p, s; K)$ (`maxLargeSize`) the cardinality of the explicit large-bundle witness `maxLargeIdx`. We prove:
1. **Internal EFX (`identicalPile_internal_efx`)**: $\tau_{\mathrm{own}}(i) \le c_{\mathrm{own}}(j)$ for all $i, j$.
2. **Fundamental Bound (`pileTau_le_r_mul_minSize`)**: $\tau(t, p, s; r) \le r \cdot M(t, p, s; K)$.
3. **Lemma A (`pileTau_step_lt`, `pileTau_step_le_tight`)**: $\tau(t, p + 1, s; r) < r (M(t, p, s; K) + 1)$, with tight bound $\le r M(t, p, s; K)$ whenever $s = 0$, $t = 1$, or $p \equiv 0 \pmod t$.
4. **Monotonicity**: $\tau$ is non-decreasing in $s$ (`pileTau_mono_s`) and in $p$ (`pileTau_mono_p`).
5. **Lemma B (`pileMinSize_sub_one_ge`)**: $s \ge 1 \land r M^* < \tau(t, p, s; r) \implies M(t, p, s - 1; K) \ge M^* + 1$.
6. **Lemma C (`pileTau_sub_one_le_of_maxLargeSize`)**: $s \ge 1 \land M^* \ge 1 \land L_{\max}(t, p, s; K) \le M^* + 1 \implies \tau(t, p, s - 1; r) \le r M^* + 1$.
7. **Phase 1/3 No-Jump Bound (`phase1_bundle_lower_bound`)**: $q r_2 < \tau(t, p + 1, c; r_2) \implies \forall i,\ q \le L_i + S_i r_1$ in `IdenticalEFX(t, p, c, K_2)`.

---

## 5. Theorem 1: Two Agent Types, Full Personalized Bi-Valued Chores (`TwoAgentTypes.lean`)

After normalizing to $\{1, r_b\}$ and stripping all-small chores $D$ via `exists_efx_extend_all_small`, partition $A \cup B \cup C$ between Pile 1 ($T_1$) and Pile 2 ($T_2$):
- **Case 1 ($\neg E_2(J_1)$)** and **Case 2 ($\neg E_1(J_2)$)**: Walk $B$ (resp. $C$ via `TwoTypeSpec.swap`) using `discrete_bolzano`; any jump contradicts `phase1_bundle_lower_bound`.
- **Case 3 ($E_2(J_1) \land E_1(J_2)$)**: Walk $A$ from $0$ to $n_A$. At any jump $E_2(a_1) \land E_1(a_1 + 1)$, Lemma A pins $M_1(a_1, n_B) = M_2(a_2 - 1, n_C) = M^* \ge 1$ with $n_B, n_C \ge 1$. By Lemma B and Lemma C, at least one of the two single-item cross-pile bridge states `B_moveB` or `B_moveC` is exact EFX. $\square$

---

## 6. Theorem C2: Three Agent Types via 2D Discrete Sperner + Chain/Star Bridge (`Sperner2D.lean`, `ThreeAgentTypes.lean`)

**Theorem (`exists_efx_three_agent_types_bivalued`).** For arbitrary $n = t_0 + t_1 + t_2 \ge 1$, $m \ge 0$, personalized bi-valued costs $\{p_b, q_b\}$ ($0 < p_b \le q_b$, arbitrary ratios $r_b > 1$), and chores in $A \cup B_0 \cup B_1 \cup B_2 \cup D$ (no chore small for exactly two types), a complete exact EFX allocation always exists.

### Proof Overview

1. **Normalization, Degeneracy, All-Small Elimination**: Normalize to $\{1, r_b\}$. If any $t_b = 0$, invoke Theorem 1 (`exists_efx_two_agent_types_bivalued`). Strip $D$ via `exists_efx_extend_all_small`, leaving $N = n_A + n_{B_0} + n_{B_1} + n_{B_2}$ chores.
2. **Unified Total-Chore Simplex $\Sigma$ & Conservative Threshold $\tilde{\tau}_b$**:
   For each grid point $(m_0, m_1, m_2) \in \mathbb{N}^3$ with $m_0 + m_1 + m_2 = N$, give Pile $b$ $\min(m_b, n_{B_b})$ own-small chores and $\max(m_b - n_{B_b}, 0)$ large chores from the shared pool $A \cup \bigcup_c \text{leftover}(B_c)$, with:
   $$M_b(m_b) := M(t_b, m_b - n_{B_b}, \min(m_b, n_{B_b}); K_b), \qquad
     \tilde{\tau}_b(m_b) := \begin{cases} \tau_b(m_b) / r_b & \text{if } n_{B_b} \le m_b \text{ (Case A)}, \\ \tau_b(m_b) & \text{if } m_b < n_{B_b} \text{ (Case B)}. \end{cases}$$
   Universal bounds proved in `ThreeAgentTypes.lean`: $\tilde{\tau}_b(0) = 0$; $\tilde{\tau}_b(m) \le M_b(m)$; $\tilde{\tau}_b(m) \le M_b(m + 1)$ (using `pileTau_mono_p`); $\tilde{\tau}_b(m + 1) < M_b(m) + 1$; and in Case B ($m < n_{B_b}$), $\tilde{\tau}_b(m + 1) \le M_b(m)$.
3. **Conservative Envy & 2D Discrete Sperner's Lemma (`sperner_2d`)**:
   Define $E_b(m) \iff \min_{j \ne b} M_j(m_j) < \tilde{\tau}_b(m_b)$. If some vertex has $\neg E_0 \land \neg E_1 \land \neg E_2$, `threeTypeSpec_of_grid` constructs an exact EFX `ThreeTypeSpec`. Otherwise, color each vertex by the envious type maximizing $\tilde{\tau}_b(m_b)$. Since $\tilde{\tau}_b(0) = 0$, the Sperner boundary conditions (`col 0 b ≠ 0`, `col a 0 ≠ 1`, `a + b = N → col a b ≠ 2`) hold automatically. Our `ZMod 2` proof of 2D Discrete Sperner's Lemma (`sperner_2d`) yields a rainbow up-triangle or rainbow down-triangle.
4. **Rainbow Triangle Resolution**:
   - **Up-triangle** $(a+1, b, c), (a, b+1, c), (a, b, c+1)$: All 5 non-identity color permutations are impossible by the universal bounds. On the identity permutation $(0, 1, 2)$, at least two of $(M_0(a), M_1(b), M_2(c))$ tie at the minimum $M^*$:
     - **Subcase 4a ($M_0 = M_1 < M_2$, up to rotation)**: Tie-breaking yields $\tilde{\tau}_2(c) < M^* + 1$. Holding Pile 2 fixed at $c$ and applying the 1-item cross-pile bridge between Piles 0 and 1 (`threeTypeSpec_of_subcase4a`) yields exact EFX.
     - **Subcase 4b ($M_0 = M_1 = M_2 = M^*$)**: All three types are in Case A with $M^* \ge 1$ and $n_{B_b} \ge 1$. Classify each type $b$ as **EASY** ($\tau_b(a_b+1, n_{B_b}-1) \le r_b M^* + 1$) or **HARD** (by Lemma C, $L_{\max, b} \ge M^* + 2$; by `pileTau_succ_zero_le_mul_minSize`, $n_{B_b} \ge 2$; by Lemma B, $M_b(a_b+1, n_{B_b}-2) \ge M^* + 1$). If at least one type is EASY, the **2-Step Chain Bridge** (`threeTypeSpec_chain_bridge`) resolves the triangle; if all three are HARD, the **2-Spoke Star Bridge** (`threeTypeSpec_star_bridge`) resolves it.
   - **Down-triangle** $(a, b+1, c+1), (a+1, b, c+1), (a+1, b+1, c)$: Identity $(0, 1, 2)$ is impossible; all 3 transpositions and both 3-cycles pin the global minimum $W = \min_{c, \delta \in \{0,1\}} M_c(m_c + \delta)$ on at least two types in Case A with the third type at $m_c + 1$ having $M > W$ and $\tilde{\tau} < W + 1$, reducing in one step to `threeTypeSpec_of_subcase4a`. $\square$

*(Remark on Higher Dimensions: The global-minimum extraction $W^* = \min_c \min(M_c(a_c), M_c(a_c + 1))$ together with a Generalized Caterpillar-Star Bridge directly extends Theorem C2 to arbitrary $k$ agent types on $A \cup B_0 \cup \dots \cup B_{k-1} \cup D$ via $(k-1)$-D Freudenthal Sperner's Lemma; the unrestricted full $2^n$ chore-type conjecture for $n \ge 5$ remains open, with >13M GPU-evolved instances and ~69k exact MILP/Z3 tests finding zero counterexamples.)*
