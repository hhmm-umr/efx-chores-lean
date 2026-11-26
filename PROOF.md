# Mathematical Proof Companion: EFX Existence for Personalized Bi-Valued Chores with Two Agent Types

This document presents the self-contained mathematical proof formalized in Lean 4 in this repository.

## 1. Problem Setup and Main Result

We consider a fair division instance of $m \ge 0$ indivisible chores $M$ among $n \ge 1$ agents $N$ with additive disutilities $c_i : M \to \mathbb{R}_{>0}$. A complete allocation $X = (X_1, \dots, X_n)$ partitioning $M$ is **envy-free up to any chore (EFX)** if for all $i, j \in N$ and every $g \in X_i$,
$$c_i(X_i \setminus \{g\}) \le c_i(X_j).$$

**Main Theorem (`exists_efx_two_agent_types_bivalued`).**
Suppose the agents partition into two types $T_1, T_2$ (with $|T_1| = t_1$, $|T_2| = t_2$, $t_1 + t_2 = n \ge 1$) such that every agent in $T_b$ ($b \in \{1, 2\}$) has identical personalized bi-valued disutilities $v_b(g) \in \{p_b, q_b\}$ for arbitrary reals $0 < p_b \le q_b$. Then a complete EFX allocation always exists.

### Context (Relation to He & Tao, `arXiv:2606.08872v2`)
Wentao He and Biaoshuai Tao (2026) used instances with **two types of agents** to prove that for all $n \ge 4$, tri-valued EFX allocations need not exist (Theorem 1) and bi-valued EFX+PO allocations need not exist (Theorem 2), while proving bi-valued EFX existence only up to $n \le 4$ via extensive case analysis (Theorem 3). Our theorem establishes that **for all $n \ge 1$**, bi-valued (and even personalized bi-valued) instances with two types of agents always admit an EFX allocation.

---

## 2. Reductions

### 2.1 Normalization and Degenerate Cases
Dividing each agent type $b \in \{1, 2\}$ by $p_b > 0$ preserves EFX (`isEFX_scale`) and maps disutilities into $\{1, r_b\}$ where $r_b = q_b / p_b > 1$ if $p_b < q_b$, or $r_b = 2$ (with all chores taking value $1$) if $p_b = q_b$.
If $t_1 = 0$ or $t_2 = 0$, all agents are identical and the closed-form water-filling allocation `IdenticalEFX` below immediately yields an EFX allocation (`exists_efx_identical_bivalued_norm`). Thus assume $t_1, t_2 \ge 1$.

### 2.2 All-Small Chore Insertion (`Reductions.lean`)
Partition the chores into four types according to $(v_1(g), v_2(g))$:
- $A$: $(r_1, r_2)$ (all-large), $|A| = n_A$;
- $B$: $(1, r_2)$ (small for $T_1$, large for $T_2$), $|B| = n_B$;
- $C$: $(r_1, 1)$ (large for $T_1$, small for $T_2$), $|C| = n_C$;
- $D$: $(1, 1)$ (all-small), $|D| = n_D$.

**Lemma (All-Small Insertion, `exists_efx_extend_all_small`).** For arbitrary $n \ge 1$ and arbitrary nonnegative additive disutilities, if an EFX allocation exists on $M \setminus D$ where every $g \in D$ satisfies $c_i(g) \le c_i(g')$ for all $i, g'$, then an EFX allocation exists on $M$.

*Proof.* Take an EFX allocation $X$ on the current chores minimizing total social cost $\sum_i c_i(X_i)$. Its **most-envy directed graph** $E(i, j) \iff c_i(X_j) = \min_k c_i(X_k) < c_i(X_i)$ has no directed cycle: rotating bundles along a simple cycle preserves EFX (every agent on the cycle receives a minimum-cost bundle) while strictly reducing total social cost. Hence the finite DAG admits a sink $s$ (an envy-free agent with $c_s(X_s) \le c_s(X_k)$ for all $k$). Assigning $g \in D$ to $s$ preserves EFX because for any $g' \in X_s \cup \{g\}$, $c_s((X_s \cup \{g\}) \setminus \{g'\}) = c_s(X_s) + c_s(g) - c_s(g') \le c_s(X_s) \le c_s(X_k)$. $\square$

*(Also formalized in `Reductions.lean` for general $n$: the Modulo-$n$ All-Large Reduction `efx_add_all_large_round`.)*

---

## 3. Closed-Form `IdenticalEFX` Pile and Its Structural Lemmas (`IdenticalAgents.lean`)

For $t \ge 1$ identical agents with costs $\{1, r\}$ ($r > 1$, $K = \lceil r \rceil \ge 2$, so $K - 1 < r \le K$), given $p$ own-large items and $s$ own-small items, write $p = \ell t + u$ ($0 \le u < t$) and $\mathrm{cap} = (t - u) K$:
- **Large items**: indices $i < u$ receive $\ell + 1$ large items; indices $i \ge u$ receive $\ell$ large items.
- **Small items (closed-form water-filling)**:
  - **Regime U ($s \le \mathrm{cap}$)**: high-large bundles ($i < u$) get $0$ small items; low-large bundles ($i \ge u$) split $s$ evenly into $\lfloor s / (t - u) \rfloor$ and $\lceil s / (t - u) \rceil$.
  - **Regime O ($s > \mathrm{cap}$)**: write $s - \mathrm{cap} = w t + v$ ($0 \le v < t$).
    - If $v \le u$: $v$ high-large bundles get $w + 1$, $u - v$ high-large bundles get $w$, and all $t - u$ low-large bundles get $K + w$.
    - If $v > u$: all $u$ high-large bundles get $w + 1$, $v - u$ low-large bundles get $K + w + 1$, and $t - v$ low-large bundles get $K + w$.

Denote by $\tau(t, p, s; r)$ the closed-form maximum EFX threshold `pileTau`, by $M(t, p, s; K)$ the minimum bundle cardinality `pileMinSize`, and by $L_{\max}(t, p, s; K)$ the cardinality of the explicit witness large bundle `maxLargeIdx` (which has $\ge 1$ large item whenever $p \ge 1$). We prove:

1. **Internal EFX (`identicalPile_internal_efx`)**: Every pair $(i, j)$ in the pile satisfies $\tau_{\mathrm{own}}(i) \le c_{\mathrm{own}}(j)$.
2. **Fundamental Bound (`pileTau_le_r_mul_minSize`)**: $\tau(t, p, s; r) \le r \cdot M(t, p, s; K)$.
3. **Lemma A — Universal $+1$ Step Bound (`pileTau_step_lt`, `pileTau_step_le_tight`)**:
   $$\tau(t, p + 1, s; r) < r \cdot \big(M(t, p, s; K) + 1\big),$$
   and if $s = 0$, $t = 1$, or $p \equiv 0 \pmod t$, then $\tau(t, p + 1, s; r) \le r \cdot M(t, p, s; K)$.
4. **Monotonicity (`pileTau_mono_s`)**: $\tau(t, p, s; r)$ is non-decreasing in $s$.
5. **Lemma B — Zero-Drop Lemma (`pileMinSize_sub_one_ge`)**:
   If $s \ge 1$ and $r \cdot M^* < \tau(t, p, s; r)$, then $M(t, p, s - 1; K) \ge M^* + 1$.
6. **Lemma C — Single-Pile Impossibility (`pileTau_sub_one_le_of_maxLargeSize`)**:
   If $s \ge 1$, $M^* \ge 1$, and $L_{\max}(t, p, s; K) \le M^* + 1$, then $\tau(t, p, s - 1; r) \le r \cdot M^* + 1$.
7. **Phase 1/3 No-Jump Bound (`phase1_bundle_lower_bound`)**:
   For any $q \in \mathbb{N}$ and any $r_1, r_2 > 1$, if $q \cdot r_2 < \tau(t, p + 1, c; r_2)$, then every bundle $i$ of `IdenticalEFX(t, p, c, K_2)` satisfies $q \le L_i + S_i \cdot r_1$.

---

## 4. Discrete Bolzano Walk and Phase-2 Single-Item Bridge (`TwoAgentTypes.lean`)

Partition $A \cup B \cup C$ between Pile 1 (for $T_1$) and Pile 2 (for $T_2$), running `IdenticalEFX` internally on each pile. Because both piles are internally EFX, the combined allocation is EFX iff neither group strongly envies the other ($\neg E_1 \land \neg E_2$).

Consider the two junction states $J_1 = (0, n_B, 0 \mid n_A, 0, n_C)$ and $J_2 = (n_A, n_B, 0 \mid 0, 0, n_C)$:

- **Case 1 ($\neg E_2(J_1)$) — Phase 1 ($B$ moves $0 \to n_B$)**:
  Walk $S_{b_1} = (0, b_1, 0 \mid n_A, n_B - b_1, n_C)$ from $b_1 = 0$ ($\neg E_1$) to $b_1 = n_B$ ($\neg E_2$). By the **Discrete Bolzano Crossing Lemma** (`discrete_bolzano`), either some $b_1$ is EFX or some step has $E_2(b_1) \land E_1(b_1 + 1)$. Since $M_1(0, b_1) = \lfloor b_1 / t_1 \rfloor = q$ and $\tau_1(0, b_1 + 1) = q$, the latter gives $q r_2 < \tau_2(n_A + n_B - b_1, n_C)$ and $L_j + S_j r_1 < q$ for some bundle $j$ of Pile 2 at $p = n_A + n_B - b_1 - 1$, contradicting the Phase 1/3 No-Jump Bound.
- **Case 2 ($\neg E_1(J_2)$) — Phase 3 ($C$ moves $0 \to n_C$)**:
  Exact mirror of Case 1 under the symmetry $T_1 \leftrightarrow T_2, B \leftrightarrow C, r_1 \leftrightarrow r_2$ (`TwoTypeSpec.swap`).
- **Case 3 ($E_2(J_1) \land E_1(J_2)$) — Phase 2 ($A$ moves $0 \to n_A$) + Bridge**:
  Along $S_{a_1} = (a_1, n_B, 0 \mid n_A - a_1, 0, n_C)$, neither pile has cross items, so $E_1(a_1)$ and $E_2(a_1)$ are mutually exclusive (by the Fundamental Bound). Hence $\neg E_1(0)$ and $\neg E_2(n_A)$. By `discrete_bolzano`, either some $a_1 \le n_A$ is EFX, or some jump $a_1 < n_A$ satisfies $E_2(a_1) \land E_1(a_1 + 1)$ (set $a_2 = n_A - a_1 \ge 1$).
  - By **Lemma A** on both piles, the two integer bounds squeeze to an exact pinning identity:
    $$M_1(a_1, n_B) = M_2(a_2 - 1, n_C) =: M^*,$$
    with $r_1 M^* < \tau_1(a_1 + 1, n_B) < r_1 (M^* + 1)$ and $r_2 M^* < \tau_2(a_2, n_C) < r_2 (M^* + 1)$.
  - By **Tight Lemma A**, $n_B \ge 1$, $n_C \ge 1$, $a_1 \not\equiv 0 \pmod{t_1}$, and $M^* \ge 1$.
  - By **Lemma B**, $M_1(a_1 + 1, n_B - 1) \ge M^* + 1$ and $M_2(a_2, n_C - 1) \ge M^* + 1$.
  - Consider the two single-item bridge states:
    1. **`B_moveB`** $= (a_1 + 1, n_B - 1, 0 \mid a_2 - 1, 1, n_C)$, placing the single cross item $B$ on Pile 2's witness bundle `maxLargeIdx₂`. By Lemma B, $\neg E_2$ holds automatically. On Pile 2, every non-witness bundle has $c_1 \ge r_1 (M^* + 1) > \tau_1(a_1 + 1, n_B - 1)$, while the witness bundle has $c_1 = r_1 (L_{\max}^{(2)} - 1) + 1$. If $\tau_1(a_1 + 1, n_B - 1) \le r_1 (L_{\max}^{(2)} - 1) + 1$, then `B_moveB` is EFX.
    2. Otherwise, since $L_{\max}^{(2)} \ge M_2(a_2, n_C) \ge M^* + 1$, we have $\tau_1(a_1 + 1, n_B - 1) > r_1 M^* + 1$. By the contrapositive of **Lemma C** applied to Pile 1 $(a_1 + 1, n_B)$, we obtain $L_{\max}^{(1)} \ge M^* + 2$. Then **`B_moveC`** $= (a_1, n_B, 1 \mid a_2, 0, n_C - 1)$ (placing the single cross item $C$ on Pile 1's witness bundle `maxLargeIdx₁`) satisfies $\neg E_1$ by Lemma B and $\neg E_2$ because the witness bundle has $c_2 = r_2 (L_{\max}^{(1)} - 1) + 1 \ge r_2 (M^* + 1) + 1 > \tau_2(a_2, n_C - 1)$. Hence `B_moveC` is EFX. $\square$
