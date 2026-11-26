module

public import BivaluedChoresEFX.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# EFX for additive chores under a bound on each agent's costs

In partial-round-first round-robin (PRFRR), write `m = n * q + u`. Agents `0, …, u - 1`
each pick a cheapest remaining chore, then all agents pick in the same order for `q` rounds.

`exists_efx_of_cost_le_sum_of_two` proves EFX for nonnegative costs when each single chore
costs at most the sum of any two distinct chores, as evaluated by the same agent. With at
least two chores, this means the largest cost is at most the sum of the two smallest.
Theorem B (`exists_efx_ratio_le_two`) applies this to costs in `[p i, 2 * p i]` with
`p i > 0`. The bi-valued specialization is `exists_efx_bivalued_ratio_le_two`.

An agent's first pick is a cheapest chore in her bundle. If she precedes the comparison
agent, pair her later picks with his picks in the same rounds. If she follows him, pair
each of her picks except the last with his next-round pick. Her last pick costs at most
the sum of her first pick and his pick in that same first round, which are distinct.
-/

@[expose] public section

namespace BivaluedChoresEFX

open scoped BigOperators

/-! ### Greedy Picking Sequence Bijection -/

/-- Given any picking schedule `picker : Fin m → Fin n`, there exists a bijection
`pick : Fin m ≃ Fin m` (mapping turn `k` to the chore picked at turn `k`) such that at every
turn `k₁`, the chosen chore `pick k₁` minimizes `cost (picker k₁)` among all chores picked at
turns `k₂ ≥ k₁`. -/
lemma exists_greedy_picking_order {n m : ℕ}
    (cost : Fin n → Fin m → ℝ) (picker : Fin m → Fin n) :
    ∃ pick : Fin m ≃ Fin m,
      ∀ k₁ k₂ : Fin m, k₁ ≤ k₂ → cost (picker k₁) (pick k₁) ≤ cost (picker k₁) (pick k₂) := by
  classical
  induction m with
  | zero =>
    exact ⟨Equiv.refl (Fin 0), fun k₁ => Fin.elim0 k₁⟩
  | succ m ih =>
    let i₀ : Fin n := picker 0
    have hne : (Finset.univ : Finset (Fin (m + 1))).Nonempty := ⟨0, Finset.mem_univ 0⟩
    obtain ⟨g₀, _, hg₀_min⟩ := Finset.exists_min_image Finset.univ (cost i₀) hne
    have hcard : Fintype.card {g : Fin (m + 1) // g ≠ g₀} = m := by
      have h1 : Fintype.card {g : Fin (m + 1) // g ≠ g₀} =
          (Finset.univ.erase g₀).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp [Finset.mem_erase]
      rw [h1, Finset.card_erase_of_mem (Finset.mem_univ g₀), Finset.card_fin]
      omega
    let eRem : Fin m ≃ {g : Fin (m + 1) // g ≠ g₀} := (Fintype.equivFinOfCardEq hcard).symm
    let cost' : Fin n → Fin m → ℝ := fun i x => cost i (eRem x).1
    let picker' : Fin m → Fin n := fun k => picker k.succ
    obtain ⟨pick', hpick'⟩ := ih cost' picker'
    let f : Fin (m + 1) → Fin (m + 1) := Fin.cases g₀ (fun k => (eRem (pick' k)).1)
    have hf_inj : Function.Injective f := by
      intro a b hab
      revert hab
      refine Fin.cases ?_ (fun a' => ?_) a
      · refine Fin.cases (fun _ => rfl) (fun b' h => ?_) b
        simp only [f, Fin.cases_zero, Fin.cases_succ] at h
        exact absurd h.symm (eRem (pick' b')).2
      · refine Fin.cases (fun h => ?_) (fun b' h => ?_) b
        · simp only [f, Fin.cases_zero, Fin.cases_succ] at h
          exact absurd h (eRem (pick' a')).2
        · simp only [f, Fin.cases_succ] at h
          have hsub : eRem (pick' a') = eRem (pick' b') := Subtype.ext h
          have heq : a' = b' := pick'.injective (eRem.injective hsub)
          rw [heq]
    let pick : Fin (m + 1) ≃ Fin (m + 1) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
    refine ⟨pick, ?_⟩
    intro k₁ k₂ hle
    revert hle
    refine Fin.cases ?_ (fun k₁' => ?_) k₁
    · intro _
      change cost i₀ (f 0) ≤ cost i₀ (f k₂)
      simp only [f, Fin.cases_zero]
      exact hg₀_min (f k₂) (Finset.mem_univ _)
    · refine Fin.cases (fun hle0 => ?_) (fun k₂' hle' => ?_) k₂
      · exfalso
        have : k₁'.succ.1 ≤ (0 : Fin (m + 1)).1 := hle0
        simp at this
      · change cost (picker k₁'.succ) (f k₁'.succ) ≤ cost (picker k₁'.succ) (f k₂'.succ)
        simp only [f, Fin.cases_succ]
        have hle'' : k₁' ≤ k₂' := by
          change k₁'.1 ≤ k₂'.1
          have : k₁'.1 + 1 ≤ k₂'.1 + 1 := hle'
          omega
        exact hpick' k₁' k₂' hle''

/-! ### Partial-Round-First Round-Robin (`PRFRR`) Schedule -/

/-- Turn index of agent `j` in round `t` under `PRFRR` (`m = n * q + u`, `u = m % n`).
Round `0` is the partial round for `j < u`; rounds `1 .. q` are full rounds for all `j`. -/
private def prfrrTurn (n u t : ℕ) (j : Fin n) : ℕ :=
  if t = 0 then j.1 else u + (t - 1) * n + j.1

/-- First round in which agent `j` picks under `PRFRR`: `0` if `j < u`, else `1`. -/
private def prfrrFirstRound {n : ℕ} (u : ℕ) (j : Fin n) : ℕ :=
  if j.1 < u then 0 else 1

/-- The `PRFRR` picking schedule mapping turn `k : Fin m` to the agent who picks at turn `k`. -/
private def prfrrPicker {n m : ℕ} (hn : 0 < n) (k : Fin m) : Fin n :=
  let u := m % n
  if hk : k.1 < u then ⟨k.1, lt_of_lt_of_le hk (le_of_lt (Nat.mod_lt m hn))⟩
  else ⟨(k.1 - u) % n, Nat.mod_lt _ hn⟩

private lemma prfrrTurn_lt {n m : ℕ} (_hn : 0 < n) (j : Fin n) {t : ℕ}
    (ht_lo : prfrrFirstRound (m % n) j ≤ t) (ht_hi : t ≤ m / n) :
    prfrrTurn n (m % n) t j < m := by
  have hdm : n * (m / n) + m % n = m := Nat.div_add_mod m n
  have hmod_le : m % n ≤ m := by omega
  unfold prfrrTurn
  by_cases ht0 : t = 0
  · subst ht0
    rw [ite_eq_left rfl]
    unfold prfrrFirstRound at ht_lo
    by_cases hju : j.1 < m % n
    · omega
    · rw [ite_eq_right hju] at ht_lo; omega
  · rw [ite_eq_right ht0]
    have h1 : (t - 1) * n + n ≤ (m / n) * n := by
      have : t ≤ m / n := ht_hi
      have hsub : (t - 1) + 1 = t := by omega
      rw [← Nat.add_one_mul, hsub]
      exact Nat.mul_le_mul_right n this
    have hjlt : j.1 < n := j.2
    rw [Nat.mul_comm] at hdm
    omega

private lemma prfrrPicker_turn {n m : ℕ} (hn : 0 < n) (j : Fin n) {t : ℕ}
    (ht_lo : prfrrFirstRound (m % n) j ≤ t) (ht_hi : t ≤ m / n) :
    prfrrPicker hn ⟨prfrrTurn n (m % n) t j, prfrrTurn_lt hn j ht_lo ht_hi⟩ = j := by
  unfold prfrrPicker prfrrTurn
  by_cases ht0 : t = 0
  · subst ht0
    unfold prfrrFirstRound at ht_lo
    have hju : j.1 < m % n := by
      by_contra h; rw [ite_eq_right h] at ht_lo; omega
    simp [hju]
  · simp only [ht0, ↓reduceIte]
    have hnot : ¬ (m % n + (t - 1) * n + j.1 < m % n) := by omega
    rw [dite_eq_right hnot]
    apply Fin.ext
    dsimp only
    have hsub : m % n + (t - 1) * n + j.1 - m % n = j.1 + n * (t - 1) := by
      rw [Nat.mul_comm]; omega
    rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.2]

/-- Recover a valid round from a turn belonging to agent `j`. -/
private lemma exists_prfrrRound {n m : ℕ} (hn : 0 < n) (k : Fin m) (j : Fin n)
    (hk : prfrrPicker hn k = j) :
    ∃ t, prfrrFirstRound (m % n) j ≤ t ∧ t ≤ m / n ∧ prfrrTurn n (m % n) t j = k.val := by
  unfold prfrrPicker at hk
  by_cases hpartial : k.val < m % n
  · rw [dite_eq_left hpartial] at hk
    have hj : k.val = j.val := congrArg Fin.val hk
    have hfirst : j.val < m % n := hj ▸ hpartial
    exact ⟨0, by simp [prfrrFirstRound, hfirst], Nat.zero_le _, by simp [prfrrTurn, hj]⟩
  · rw [dite_eq_right hpartial] at hk
    have hj : (k.val - m % n) % n = j.val := congrArg Fin.val hk
    let d := (k.val - m % n) / n
    have hkdiv : n * d + (k.val - m % n) % n = k.val - m % n := Nat.div_add_mod _ _
    have hmdiv := Nat.div_add_mod m n
    have hlt : n * d < n * (m / n) := by have := k.isLt; omega
    refine ⟨d + 1, ?_, Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left hlt), ?_⟩
    · unfold prfrrFirstRound
      split_ifs
      · exact Nat.zero_le _
      · exact Nat.succ_le_succ (Nat.zero_le _)
    · simp only [prfrrTurn, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [Nat.mul_comm] at hkdiv
      omega

private lemma prfrrTurn_strictMono {n u : ℕ} (hn : 0 < n) (j : Fin n) :
    ∀ t₁ t₂, prfrrFirstRound u j ≤ t₁ → t₁ < t₂ → prfrrTurn n u t₁ j < prfrrTurn n u t₂ j := by
  intro t₁ t₂ ht₁ hlt
  unfold prfrrTurn
  by_cases h1 : t₁ = 0
  · subst h1
    have h2 : t₂ ≠ 0 := by omega
    rw [ite_eq_left rfl, ite_eq_right h2]
    unfold prfrrFirstRound at ht₁
    have hju : j.1 < u := by by_contra h; rw [ite_eq_right h] at ht₁; omega
    omega
  · have h2 : t₂ ≠ 0 := by omega
    rw [ite_eq_right h1, ite_eq_right h2]
    have : t₁ - 1 < t₂ - 1 := by omega
    have hmul : (t₁ - 1) * n < (t₂ - 1) * n := Nat.mul_lt_mul_of_pos_right this hn
    omega

private lemma prfrrTurn_lt_of_lt_agent {n u t : ℕ} {i j : Fin n} (ht : 1 ≤ t) (hij : i.1 < j.1) :
    prfrrTurn n u t i < prfrrTurn n u t j := by
  unfold prfrrTurn
  have ht0 : t ≠ 0 := by omega
  rw [ite_eq_right ht0, ite_eq_right ht0]
  omega

private lemma prfrrTurn_lt_succ_of_gt_agent {n u t : ℕ} {i j : Fin n}
    (ht_lo : prfrrFirstRound u i ≤ t) :
    prfrrTurn n u t i < prfrrTurn n u (t + 1) j := by
  unfold prfrrTurn
  have hts : t + 1 ≠ 0 := Nat.succ_ne_zero t
  rw [ite_eq_right hts]
  by_cases ht0 : t = 0
  · subst ht0
    rw [ite_eq_left rfl]
    unfold prfrrFirstRound at ht_lo
    have hiu : i.1 < u := by by_contra h; rw [ite_eq_right h] at ht_lo; omega
    omega
  · rw [ite_eq_right ht0]
    have hsub : t + 1 - 1 = (t - 1) + 1 := by omega
    rw [hsub, Nat.add_one_mul]
    have hi : i.1 < n := i.2
    omega

private lemma bundleCost_eq_sum_rounds {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ) (pick : Fin m ≃ Fin m)
    (i j : Fin n) :
    bundleCost cost (bundle (fun g => prfrrPicker hn (pick.symm g)) j) i =
      ∑ t ∈ Finset.Ico (prfrrFirstRound (m % n) j) (m / n + 1),
        if h : prfrrFirstRound (m % n) j ≤ t ∧ t ≤ m / n then
          cost i (pick ⟨prfrrTurn n (m % n) t j, prfrrTurn_lt hn j h.1 h.2⟩)
        else 0 := by
  by_cases hm0 : m = 0
  · subst hm0
    have hfirst : prfrrFirstRound (0 % n) j = 1 := by simp [prfrrFirstRound]
    have hempty : Finset.Ico (prfrrFirstRound (0 % n) j) (0 / n + 1) = ∅ := by
      rw [hfirst]; simp
    rw [hempty, Finset.sum_empty]
    unfold bundleCost bundle
    simp
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
  unfold bundleCost bundle
  symm
  refine Finset.sum_nbij
    (fun t => if h : prfrrFirstRound (m % n) j ≤ t ∧ t ≤ m / n then
      pick ⟨prfrrTurn n (m % n) t j, prfrrTurn_lt hn j h.1 h.2⟩
      else pick ⟨0, hm_pos⟩)
    ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_Ico] at ht
    have hcond : prfrrFirstRound (m % n) j ≤ t ∧ t ≤ m / n := ⟨ht.1, by omega⟩
    rw [dite_eq_left hcond]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    exact prfrrPicker_turn hn j hcond.1 hcond.2
  · intro t₁ ht₁ t₂ ht₂ heq
    rw [Finset.mem_coe, Finset.mem_Ico] at ht₁ ht₂
    dsimp only at heq
    have hc1 : prfrrFirstRound (m % n) j ≤ t₁ ∧ t₁ ≤ m / n := ⟨ht₁.1, by omega⟩
    have hc2 : prfrrFirstRound (m % n) j ≤ t₂ ∧ t₂ ≤ m / n := ⟨ht₂.1, by omega⟩
    rw [dite_eq_left hc1, dite_eq_left hc2] at heq
    have hfin := pick.injective heq
    have hval : prfrrTurn n (m % n) t₁ j = prfrrTurn n (m % n) t₂ j := congrArg Fin.val hfin
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (prfrrTurn_strictMono hn j t₁ t₂ hc1.1 hlt)) hval
    · exact (ne_of_gt (prfrrTurn_strictMono hn j t₂ t₁ hc2.1 hgt)) hval
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨t, hfirst, hlast, ht⟩ := exists_prfrrRound hn (pick.symm g) j hg
    refine ⟨t, Finset.mem_Ico.mpr ⟨hfirst, by omega⟩, ?_⟩
    dsimp only
    rw [dite_eq_left ⟨hfirst, hlast⟩]
    have hturn : (⟨prfrrTurn n (m % n) t j, prfrrTurn_lt hn j hfirst hlast⟩ : Fin m) =
        pick.symm g := Fin.ext ht
    rw [hturn, pick.apply_symm_apply]
  · intro t ht
    rw [Finset.mem_Ico] at ht
    simp [show prfrrFirstRound (m % n) j ≤ t ∧ t ≤ m / n from ⟨ht.1, by omega⟩]

/-! ### EFX under a bound by the sum of two distinct chore costs -/

/-- PRFRR gives a complete EFX allocation if each agent's costs are nonnegative and each
single chore costs at most the sum of any two distinct chores for that agent. -/
theorem exists_efx_of_cost_le_sum_of_two
    {n m : ℕ} (hn : 0 < n) (cost : Fin n → Fin m → ℝ)
    (hcost_nn : ∀ i g, 0 ≤ cost i g)
    (hpair : ∀ i g a b, a ≠ b → cost i g ≤ cost i a + cost i b) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc := by
  classical
  obtain ⟨pick, hgreedy⟩ := exists_greedy_picking_order cost (prfrrPicker hn)
  let alloc : Fin m → Fin n := fun g => prfrrPicker hn (pick.symm g)
  refine ⟨alloc, fun i j g hg => ?_⟩
  rw [bundleCost_sdiff_singleton cost hg]
  set q := m / n
  set u := m % n
  set t0i := prfrrFirstRound u i
  set t0j := prfrrFirstRound u j
  -- Helper term for agent k's picked cost in round t
  let term (k : Fin n) (t : ℕ) : ℝ :=
    if h : prfrrFirstRound u k ≤ t ∧ t ≤ q then
      cost i (pick ⟨prfrrTurn n u t k, prfrrTurn_lt hn k h.1 h.2⟩)
    else 0
  have hterm_nn : ∀ k t, 0 ≤ term k t := by
    intro k t; simp only [term]; split_ifs
    · exact hcost_nn _ _
    · exact le_refl 0
  have hcost_i : bundleCost cost (bundle alloc i) i = ∑ t ∈ Finset.Ico t0i (q + 1), term i t :=
    bundleCost_eq_sum_rounds hn cost pick i i
  have hcost_j : bundleCost cost (bundle alloc j) i = ∑ t ∈ Finset.Ico t0j (q + 1), term j t :=
    bundleCost_eq_sum_rounds hn cost pick i j
  rw [hcost_i, hcost_j]
  have howner : prfrrPicker hn (pick.symm g) = i := by simpa [alloc] using mem_bundle.mp hg
  obtain ⟨r, hr0, hrq, hrturn⟩ := exists_prfrrRound hn (pick.symm g) i howner
  have hfirst : t0i ≤ q := le_trans hr0 hrq
  have hcond0 : prfrrFirstRound u i ≤ t0i ∧ t0i ≤ q := ⟨le_rfl, hfirst⟩
  have hfirst_le_g : term i t0i ≤ cost i g := by
    simp only [term, hcond0]
    have hturn : (⟨prfrrTurn n u t0i i, prfrrTurn_lt hn i hcond0.1 hcond0.2⟩ : Fin m) ≤
        pick.symm g := by
      change prfrrTurn n u t0i i ≤ (pick.symm g).val
      rw [← hrturn]
      rcases eq_or_lt_of_le hr0 with heq | hlt
      · rw [← heq]
      · exact (prfrrTurn_strictMono hn i t0i r le_rfl hlt).le
    have h := hgreedy _ _ hturn
    rwa [prfrrPicker_turn hn i hcond0.1 hcond0.2, pick.apply_symm_apply] at h
  -- Split ∑_{t0i}^{q} term i t = term i t0i + ∑_{t0i+1}^{q} term i t
  have hsplit_i : ∑ t ∈ Finset.Ico t0i (q + 1), term i t =
      term i t0i + ∑ t ∈ Finset.Ico (t0i + 1) (q + 1), term i t := by
    rw [← Finset.sum_eq_sum_Ico_succ_bot (by omega : t0i < q + 1)]
  have htau_bound : (∑ t ∈ Finset.Ico t0i (q + 1), term i t) - cost i g ≤
      ∑ t ∈ Finset.Ico (t0i + 1) (q + 1), term i t := by
    linarith
  refine le_trans htau_bound ?_
  rcases lt_trichotomy i.1 j.1 with hij | hij | hji
  · -- Case 1: i < j. Every t ∈ [t0i + 1, q] satisfies t ≥ 1 ≥ t0j and turn(t, i) < turn(t, j)!
    have hsub : Finset.Ico (t0i + 1) (q + 1) ⊆ Finset.Ico t0j (q + 1) := by
      intro t ht; rw [Finset.mem_Ico] at ht ⊢
      have ht0j_le1 : t0j ≤ 1 := by unfold t0j prfrrFirstRound; split_ifs <;> omega
      omega
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hterm_nn j t))
    refine Finset.sum_le_sum fun t ht => ?_
    rw [Finset.mem_Ico] at ht
    have hci : prfrrFirstRound u i ≤ t ∧ t ≤ q := ⟨by omega, by omega⟩
    have hcj : prfrrFirstRound u j ≤ t ∧ t ≤ q := by
      have ht0j_le1 : t0j ≤ 1 := by unfold t0j prfrrFirstRound; split_ifs <;> omega
      exact ⟨by omega, by omega⟩
    simp only [term, hci, hcj, and_self, ↓reduceDIte]
    have hlt_turn : (⟨prfrrTurn n u t i, prfrrTurn_lt hn i hci.1 hci.2⟩ : Fin m) ≤
        ⟨prfrrTurn n u t j, prfrrTurn_lt hn j hcj.1 hcj.2⟩ :=
      le_of_lt (prfrrTurn_lt_of_lt_agent (by omega : 1 ≤ t) hij)
    have hgr := hgreedy _ _ hlt_turn
    rw [prfrrPicker_turn hn i hci.1 hci.2] at hgr
    exact hgr
  · -- Removing a nonnegative chore decreases the cost of the same bundle.
    have heq : i = j := Fin.ext hij
    subst heq
    have hsub : Finset.Ico (t0i + 1) (q + 1) ⊆ Finset.Ico t0i (q + 1) :=
      Finset.Ico_subset_Ico_left (Nat.le_succ _)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hterm_nn i t)
  · -- Case 3: j < i. Here t0j ≤ t0i, and turn(t, i) < turn(t + 1, j) for t ∈ [t0i, q - 1]!
    have ht0j_le : t0j ≤ t0i := by
      unfold t0j t0i prfrrFirstRound
      split_ifs <;> omega
    have hsub : Finset.Ico t0i (q + 1) ⊆ Finset.Ico t0j (q + 1) :=
      Finset.Ico_subset_Ico_left ht0j_le
    have hj_ge_sub : ∑ t ∈ Finset.Ico t0i (q + 1), term j t ≤
        ∑ t ∈ Finset.Ico t0j (q + 1), term j t :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => hterm_nn j t)
    have hsplit_j : ∑ t ∈ Finset.Ico t0i (q + 1), term j t =
        term j t0i + ∑ t ∈ Finset.Ico (t0i + 1) (q + 1), term j t := by
      rw [← Finset.sum_eq_sum_Ico_succ_bot (by omega : t0i < q + 1)]
    have hshift_j : ∑ t ∈ Finset.Ico (t0i + 1) (q + 1), term j t =
        ∑ t ∈ Finset.Ico t0i q, term j (t + 1) := by
      refine Finset.sum_nbij (fun t => t - 1) ?_ ?_ ?_ ?_
      · intro t ht; rw [Finset.mem_Ico] at ht ⊢; omega
      · intro t₁ ht₁ t₂ ht₂ h; rw [Finset.mem_coe, Finset.mem_Ico] at ht₁ ht₂; dsimp only at h; omega
      · intro s hs; rw [Finset.mem_coe, Finset.mem_Ico] at hs
        exact ⟨s + 1, by rw [Finset.mem_coe, Finset.mem_Ico]; omega, by dsimp only; omega⟩
      · intro t ht; rw [Finset.mem_Ico] at ht; congr 1; omega
    have hstep_le : ∑ t ∈ Finset.Ico t0i q, term i t ≤
        ∑ t ∈ Finset.Ico t0i q, term j (t + 1) := by
      refine Finset.sum_le_sum fun t ht => ?_
      rw [Finset.mem_Ico] at ht
      have hci : prfrrFirstRound u i ≤ t ∧ t ≤ q := ⟨ht.1, le_of_lt ht.2⟩
      have hcj : prfrrFirstRound u j ≤ t + 1 ∧ t + 1 ≤ q := ⟨by omega, by omega⟩
      simp only [term, hci, hcj, and_self, ↓reduceDIte]
      have hlt_turn : (⟨prfrrTurn n u t i, prfrrTurn_lt hn i hci.1 hci.2⟩ : Fin m) ≤
          ⟨prfrrTurn n u (t + 1) j, prfrrTurn_lt hn j hcj.1 hcj.2⟩ :=
        le_of_lt (prfrrTurn_lt_succ_of_gt_agent hci.1)
      have hgr := hgreedy _ _ hlt_turn
      rw [prfrrPicker_turn hn i hci.1 hci.2] at hgr
      exact hgr
    have hsplit_i_top : ∑ t ∈ Finset.Ico t0i (q + 1), term i t =
        (∑ t ∈ Finset.Ico t0i q, term i t) + term i q := by
      rw [Finset.sum_Ico_succ_top hfirst]
    -- The two chores picked in round t0i have different owners.
    have hcondj0 : prfrrFirstRound u j ≤ t0i ∧ t0i ≤ q := ⟨ht0j_le, hfirst⟩
    have hcondiq : prfrrFirstRound u i ≤ q ∧ q ≤ q := ⟨hfirst, le_rfl⟩
    have hlast : term i q ≤ term i t0i + term j t0i := by
      simp only [term, hcondiq, hcond0, hcondj0]
      apply hpair
      intro heq
      have hij := congrArg (prfrrPicker hn) (pick.injective heq)
      rw [prfrrPicker_turn hn i hcond0.1 hcond0.2,
        prfrrPicker_turn hn j hcondj0.1 hcondj0.2] at hij
      exact (ne_of_gt hji) (congrArg Fin.val hij)
    linarith

/-- Theorem B. If the costs of each agent lie in a positive interval `[p i, 2 * p i]`,
there exists a complete EFX allocation. -/
theorem exists_efx_ratio_le_two
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i)
    (hlo : ∀ i g, p i ≤ cost i g)
    (hhi : ∀ i g, cost i g ≤ 2 * p i) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc := by
  apply exists_efx_of_cost_le_sum_of_two hn cost (fun i g => (hp i).le.trans (hlo i g))
  intro i g a b _
  linarith [hhi i g, hlo i a, hlo i b]

/-- **Corollary (Personalized Bi-Valued Chores with Ratio ≤ 2 — Arbitrary `n`, Arbitrary Types)**:
For every `n ≥ 1`, every `m ≥ 0`, and every personalized bi-valued additive chores instance
with `cost i g ∈ {p i, q i}` and `0 < p i ≤ q i ≤ 2 * p i`, a complete EFX allocation exists. -/
theorem exists_efx_bivalued_ratio_le_two
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (p q : Fin n → ℝ)
    (hp : ∀ i, 0 < p i)
    (hpq : ∀ i, p i ≤ q i)
    (hq2 : ∀ i, q i ≤ 2 * p i)
    (hbiv : ∀ i g, cost i g = p i ∨ cost i g = q i) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc :=
  exists_efx_ratio_le_two hn cost p hp
    (fun i g => by rcases hbiv i g with h | h <;> linarith [hpq i])
    (fun i g => by rcases hbiv i g with h | h <;> linarith [hpq i, hq2 i])

end BivaluedChoresEFX
