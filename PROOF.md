# Proof guide to exact EFX for additive chores

## 1. The model and the scope of the results

Let $M$ be a set of $m\ge 0$ indivisible chores and let $n\ge 1$ be the number of agents. Agent $i$ evaluates a bundle $S$ by $c_i(S)=\sum_{g\in S}c_i(g)$. A complete allocation partitions $M$ into bundles $X_i$. It is **EFX** if

$$\forall i,j,\quad \forall g\in X_i,\qquad c_i(X_i\setminus\{g\})\le c_i(X_j).$$

The chore is removed from the observer's own bundle. With nonnegative costs, the hardest removal is a cheapest chore in that bundle. An empty bundle imposes no condition. [Lean definitions](BivaluedChoresEFX/Basic.lean)

The round-robin theorem assumes nonnegative costs and a bound on each observer's cost for any one chore. The two-type and three-type theorems assume personalized bi-valued costs. Agents of type $b$ share one cost profile with values in $\{p_b,q_b\}$, where $0<p_b\le q_b$. Section 5 allows every light/heavy pattern for two types. Section 6 allows chores light for zero, one, or all three types. A chore is light for $b$ if its cost equals $p_b$.

He and Tao prove existence for four agents with a common pair of costs and give an arbitrary-$n$ algorithm in the common $\{1,r\}$ case for $r\le 2$. They also exhibit two-type instances with three cost values and no EFX allocation for every $n\ge4$, and bi-valued instances where EFX is incompatible with Pareto optimality. The guarantees here concern complete EFX allocations. [He and Tao, Sections 3–5](https://arxiv.org/html/2606.08872v2#S3)

## 2. Extending an EFX allocation

Assume throughout this section that every single-chore cost is nonnegative.

**One round of all-large chores.** Suppose the old allocation is EFX and, for each observer $i$, each of the $n$ new chores has the same cost $R_i$, at least every old single-chore cost. Give one new chore to each agent. Removing an old chore adds the same $R_i$ to both sides of its old EFX inequality. Removing the new chore leaves $c_i(X_i)$ to compare with $c_i(X_j)+R_i$. If $X_i$ is nonempty, old EFX gives $c_i(X_i)\le c_i(X_j)+c_i(h)$ for any $h\in X_i$, and $c_i(h)\le R_i$. The empty case follows from nonnegativity. This is `efx_add_all_large_round`.

**A recipient for a minimum-cost chore.** Start with any EFX allocation $X$. For every agent $i$ choose the owner $f(i)$ of a bundle minimizing $c_i(X_j)$ over all $j$. Follow $f$ from any vertex. Finiteness gives a directed cycle, possibly a fixed point. Rotate the bundles around that cycle, so each member $i$ gets $X_{f(i)}$. Every cycle member now holds a cheapest bundle and satisfies EFX by nonnegativity. Each other agent retains her old bundle and sees the same collection of comparison bundles. Hence the new allocation $Y$ is EFX and any cycle member $s$ is envy-free. This is `exists_efx_with_envy_free_agent`.

For example, suppose two agents start with one chore each, and each values her own at $2$ and the other's at $1$. The allocation is EFX. Giving either agent a new chore of cost $1$ to both would leave her envying the other after removing that new chore. Swapping their original chores first gives both agents a cheapest bundle.

Give $s$ a new chore $g$ of minimum cost to every agent. For any $h\in Y_s\cup\{g\}$,

$$c_s((Y_s\cup\{g\})\setminus\{h\})
  =c_s(Y_s)+c_s(g)-c_s(h)\le c_s(Y_s)\le c_s(Y_j).$$

For every other observer, the only comparison bundle that changes grows in cost or stays tied. This proves `exists_efx_insert_all_small`. Iterating proves `exists_efx_extend_all_small` when every added chore is a minimum for every agent among all the chores. [Lean proofs](BivaluedChoresEFX/Reductions.lean)

## 3. Partial-round-first round-robin and Theorem B

**Round-robin theorem.** Suppose costs are nonnegative and, for every agent $i$ and every pair of distinct chores $a,b$,

$$c_i(g)\le c_i(a)+c_i(b)\qquad\text{for every chore }g.$$

For at least two chores, the smallest possible right-hand side is the sum of the two smallest entries of agent $i$'s cost row, counting multiplicity. The largest possible left-hand side is the maximum of the row. With fewer than two chores there is no pair to check. The formal statement is `exists_efx_of_cost_le_sum_of_two`.

Write $m=qn+u$, where $0\le u<n$. In round 0, agents $0,\ldots,u-1$ each pick a cheapest remaining chore. In each of rounds $1,\ldots,q$, agents $0,\ldots,n-1$ do the same, in that order. This uses every chore exactly once.

Fix an observer $i$ with a nonempty bundle, another agent $j$, and any $h\in X_i$. Write $x_{k,r}=c_i(g_{k,r})$ for the cost **to $i$** of the chore picked by $k$ in round $r$. The first round for $i$ is $t=0$ if $i<u$, and $t=1$ otherwise. Greedy choice gives $x_{i,t}\le c_i(h)$, since $h$ was available at that turn. For $j=i$, nonnegativity gives EFX directly.

- **If $i<j$**, pair $i$'s picks in rounds $t+1,\ldots,q$ with $j$'s picks in the same rounds. These rounds are full, and $i$ picks first. Thus $c_i(X_i)-c_i(h)\le\sum_{r=t+1}^q x_{i,r}\le\sum_{r=t+1}^q x_{j,r}\le c_i(X_j)$.
- **If $j<i$**, agent $j$ also picks in round $t$. For $t\le r<q$, the chore $j$ takes in round $r+1$ was available to $i$ in round $r$, so $x_{i,r}\le x_{j,r+1}$. The two chores picked by $i$ and $j$ in round $t$ are distinct. The hypothesis therefore gives $x_{i,q}\le x_{i,t}+x_{j,t}$, hence $x_{i,q}-c_i(h)\le x_{j,t}$. Combining the paired and unpaired terms gives

$$
\begin{aligned}
c_i(X_i\setminus\{h\})
 &=\sum_{r=t}^{q-1} x_{i,r}+x_{i,q}-c_i(h)\\
 &\le \sum_{r=t}^{q-1} x_{j,r+1}+x_{j,t}
 \le c_i(X_j).
\end{aligned}
$$

The sums over paired rounds are empty when $t=q$. To see why the unpaired term matters, take two identical agents and chores of costs $(1,1,1,1,2)$. They receive $(1,1,1)$ and $(1,2)$. For the second agent, removing the $1$ leaves $2$. The shifted sum is $1$ and the first agent's unpaired round-$1$ pick supplies the other $1$.

**Theorem B.** If $0<p_i\le c_i(g)\le 2p_i$, then $c_i(a)+c_i(b)\ge 2p_i\ge c_i(g)$. Applying the theorem proves `exists_efx_ratio_le_two`, including the personalized bi-valued corollary `exists_efx_bivalued_ratio_le_two`. The row $(1,2,2,3)$ illustrates the extra scope of the pair bound. [Lean proof](BivaluedChoresEFX/RatioTwoChores.lean)

## 4. Water-filling for identical agents

Normalize one type to costs $\{1,r\}$ with $r>1$, and put $K=\lceil r\rceil$. Let $t\ge1$ be the number of agents of that type, $p=\ell t+u$ the count of their large chores, and $s$ the count of their small chores. Here $p$ is an item count. Give $\ell+1$ large chores to the first $u$ agents and $\ell$ to each remaining agent. Distribute up to $(t-u)K$ small chores as evenly as possible among those last $t-u$ agents. If small chores remain, distribute them evenly among all $t$ agents, giving any extras in index order. The Lean functions are `pileLarge` and `pileSmall`.

For a nonempty bundle with $L$ large and $S$ small items, its EFX threshold `ownTau` is $Lr+S$ minus $1$ if $S>0$, and minus $r$ otherwise. Put the threshold at zero for an empty bundle. For fixed $t,r,K$, write $\tau(p,s)$ for `pileTau`, an upper bound on all these thresholds, and $M(p,s)$ for `pileMinSize`, a lower bound on all bundle sizes. Write $L_{\max}(p,s)$ for the size of the designated witness bundle `maxLargeIdx` used to receive a cross-type chore. The proof uses the following bounds.

| Lemma | Bound |
|---|---|
| Internal EFX | Each individual threshold is at most the cost of every bundle in its pile. |
| Fundamental bound | $\tau(p,s)\le rM(p,s)$. |
| Lemma A | $\tau(p+1,s)<r(M(p,s)+1)$. If $s=0$, $t=1$, or $t$ divides $p$, the right-hand bound tightens to $\tau(p+1,s)\le rM(p,s)$. |
| Monotonicity | $\tau$ is nondecreasing in the number of small chores and in the number of large chores. |
| Lemma B | If $s\ge1$ and $\tau(p,s)>rM^*$, then $M(p,s-1)\ge M^*+1$. |
| Lemma C | If $s\ge1$, $M^*\ge1$ and $L_{\max}(p,s)\le M^*+1$, then $\tau(p,s-1)\le rM^*+1$. |
| Phase 1 and 3 no-jump bound | If $qr_2<\tau_2(p+1,c)$, every bundle with counts $(L,S)$ in pile 2 at $(p,c)$ satisfies $q\le L+Sr_1$. |

The single-pile inequalities are proved by splitting at the water-filling capacity and at the remainder of $p$ modulo $t$. Monotonicity in $p$ is proved at the start of the three-type module. [Water-filling lemmas](BivaluedChoresEFX/IdenticalAgents.lean) · [Large-item monotonicity](BivaluedChoresEFX/ThreeAgentTypes.lean)

## 5. Theorem 1 for two agent types

Divide each type's costs by its positive $p_b$. A constant type then has only cost $1$, so an unused upper value $r_b=2$ lets the same lemmas apply. An empty type reduces the problem to identical agents. Set aside all-small chores $D$ for insertion by Section 2. Of the remaining chores, $A$ is large for both types, $B$ is small only for type 1, and $C$ is small only for type 2. Write $n_A,n_B,n_C$ for their counts and use subscripts on $\tau$ and $M$ for the corresponding pile parameters.

### The walk and its endpoints

In the middle phase, let $a$ of the $A$ chores be in pile 1 and $b=n_A-a$ in pile 2. All $B$ chores are in pile 1 and all $C$ chores in pile 2. From the other type's viewpoint every item in a comparison bundle is large. The cross-pile tests are therefore

$$
\begin{aligned}
E_1(a)&\iff r_1M_2(b,n_C)<\tau_1(a,n_B),\\
E_2(a)&\iff r_2M_1(a,n_B)<\tau_2(b,n_C).
\end{aligned}
$$

If both tests are false, every cross-pile comparison satisfies EFX. The fundamental bound prevents both tests from being true at once, since each would force its own pile to have strictly larger $M$ than the other pile.

The endpoints $J_1$ and $J_2$ correspond to $a=0$ and $a=n_A$. If $E_2(0)$ is false, the first phase moves $B$ chores into pile 1 up to $J_1$. If $E_1(n_A)$ is false, the symmetric last phase moves $C$ chores. In either case `discrete_bolzano` and `phase1_bundle_lower_bound` give a state passing both tests for that phase. In the remaining case $E_2(0)$ and $E_1(n_A)$ hold. The middle walk then either passes both tests at one state or jumps from $E_2(a)$ to $E_1(a+1)$.

### A single-item bridge at a jump

At a jump $b\ge1$. Lemma A and integrality force
$M_1(a,n_B)=M_2(b-1,n_C)=M^*$. The tight cases and the pile formulas give $M^*\ge1$ and $n_B,n_C\ge1$. The two thresholds $\tau_1(a+1,n_B)$ and $\tau_2(b,n_C)$ are strictly below $r_1(M^*+1)$ and $r_2(M^*+1)$ respectively. The fundamental bound and Lemma B give minimum sizes of at least $M^*+1$ in each of these two piles, even after dropping one own-small chore.

First try moving one $B$ to pile 2 in exchange for one $A$. Pile 1 balances $(a+1,n_B-1)$ large and small items. Pile 2 keeps the balanced pattern for $(b,n_C)$, filling one large slot of its designated witness bundle with the incoming $B$. Its own type values $A$ and $B$ equally, so internal EFX still holds. Let $L_2$ be that witness bundle's size.

- From type 2, every item in pile 1 costs $r_2$ and each bundle there has at least $M^*+1$ items. This covers every type-2 threshold.
- From type 1, ordinary pile-2 bundles likewise cost at least $r_1(M^*+1)$. The witness costs $r_1(L_2-1)+1$ because exactly one item is a $B$. If $\tau_1(a+1,n_B-1)\le r_1(L_2-1)+1$, it too passes. This allocation is the `B_moveB` case of `exists_twoTypeSpec_phase2_jump`.

If the witness test fails, $L_2\ge M^*+1$ implies $\tau_1(a+1,n_B-1)>r_1 M^*+1$. Lemma C forces the type-1 witness at $(a+1,n_B)$ to have size $L_1\ge M^*+2$. Use the symmetric construction, placing one $C$ in that witness's large slot and leaving $(b,n_C-1)$ in pile 2. From type 2 the witness costs $r_2(L_1-1)+1>r_2(M^*+1)$. The ordinary comparisons follow from the same size and threshold bounds. This is `B_moveC`. Finally, `realize_twoTypeSpec` assigns actual chores to the counted slots and the all-small insertion lemma restores $D$. [Two-type proof and both bridge constructions](BivaluedChoresEFX/TwoAgentTypes.lean)

## 6. Theorem C2 for three agent types

Each type has $0<p_b\le q_b$ with no upper ratio bound. The sets of types for which a chore is light have size $0$, $1$, or $3$. Normalize as in Section 5. If any type is empty, apply Theorem 1. Otherwise set aside the all-small chores $D$. Write $B_b$ for the chores light only for type $b$ and $A$ for the chores light for no type. There are $N=n_A+\sum_b n_{B_b}$ remaining chores. When $N=0$, the empty specification suffices.

**The grid and its thresholds.** A vertex $(m_0,m_1,m_2)$ with nonnegative integer coordinates summing to $N$ prescribes a size for each pile. Pile $b$ takes $s_b=\min(m_b,n_{B_b})$ own-small chores and $\ell_b=\max(m_b-n_{B_b},0)$ own-large chores. The latter come from $A$ and the unused single-light chores of other types. Put $M_b(m_b)=M_b(\ell_b,s_b)$ using the pile-size function of Section 4. The conservative threshold is

$$
\widetilde{\tau}_b(m_b)=
\begin{cases}
\tau_b(\ell_b,s_b)/r_b & m_b\ge n_{B_b}\quad\text{(case A)},\\
\tau_b(\ell_b,s_b)     & m_b<n_{B_b}\quad\text{(case B)}.
\end{cases}
$$

In case A all of type $b$'s light chores are in its own pile, so every other bundle costs $r_b$ times its size to that type. In case B the item count alone is a valid lower bound on each other bundle's cost. The grid lemmas give $\widetilde{\tau}_b(0)=0$, $\widetilde{\tau}_b(m)\le\min(M_b(m),M_b(m+1))$, and $\widetilde{\tau}_b(m+1)<M_b(m)+1$. In case B the last bound tightens to $\widetilde{\tau}_b(m+1)\le M_b(m)$.

**Finding a rainbow triangle.** Flag type $b$ at a vertex if $\min_{j\ne b}M_j(m_j)<\widetilde{\tau}_b(m_b)$. An unflagged vertex gives EFX by `threeTypeSpec_of_grid`. Otherwise color each vertex by a flagged type of largest threshold, breaking ties in index order. A type with $m_b=0$ cannot be flagged, which gives the three Sperner boundary conditions. In the parity proof, interior edges with endpoint colors 0 and 1 count twice. On the side opposite color 2 the endpoint colors differ and the number of such edges is odd. Hence at least one small triangle has all three colors. [Discrete Sperner lemma](BivaluedChoresEFX/Sperner2D.lean)

**Resolving the triangle.** The vertex order determines what the identity coloring $(0,1,2)$ means.

- For an up-triangle the order is $(a+1,b,c),(a,b+1,c),(a,b,c+1)$. The bounds exclude the five nonidentity colorings. In the identity case at least two of $M_0(a),M_1(b),M_2(c)$ tie at their minimum $M^*$. If exactly two tie (subcase 4a), the coloring rule bounds the third pile's threshold by $<M^*+1$. Hold that pile fixed and use the single-item bridge on the other two.
- If all three tie (subcase 4b), each pile is in case A, $M^*\ge1$ and each $n_{B_b}\ge1$. At the base coordinates $(m_0,m_1,m_2)=(a,b,c)$, write $u_b=m_b-n_{B_b}$ for the large-slot count of type $b$. Call a type EASY when $\tau_b(u_b+1,n_{B_b}-1)\le r_bM^*+1$. For a HARD type, Lemma C supplies a witness of size at least $M^*+2$. The single-pile bounds give $n_{B_b}\ge2$ and $M_b(u_b+1,n_{B_b}-2)\ge M^*+1$. An EASY type allows a two-step chain bridge after relabeling the types. Three HARD types allow a two-spoke star bridge.
- For a down-triangle the order is $(a,b+1,c+1),(a+1,b,c+1),(a+1,b+1,c)$. The identity coloring contradicts the minimum-size bounds. In each of the three transpositions and two three-cycles the proof chooses a pair tied at the global minimum of the six adjacent size values. The remaining pile has larger size and threshold below that minimum plus one at its upper coordinate. These are the hypotheses of subcase 4a.

The resulting `ThreeTypeSpec` records counts and all nine directions of EFX comparisons. `realize_threeTypeSpec` turns it into a complete allocation and the insertion lemma restores the all-small chores. [Three-type proof](BivaluedChoresEFX/ThreeAgentTypes.lean)

### Higher-dimensional research question

For $k>3$ types with unrestricted personalized ratios, does EFX always exist when the light types of each chore form the empty set, a singleton, or the full set? Extending this proof would require a $(k-1)$-dimensional coloring argument and a construction that resolves every resulting rainbow simplex. The formalized bridge constructions above establish the three-type case. Allowing arbitrary sets of light types at unrestricted ratios gives a further question.
