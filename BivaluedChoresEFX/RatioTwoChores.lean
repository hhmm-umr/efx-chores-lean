module

public import BivaluedChoresEFX.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Exact EFX Existence for General-n Ratio-≤ 2 Additive Chores (`PRFRR`)

This module proves **Theorem B (`exists_efx_ratio_le_two`)**:
for **every** `n ≥ 1`, **every** `m ≥ 0`, and **every** additive chores instance
`cost : Fin n → Fin m → ℝ` (arbitrary number of agent types, arbitrary chore types, not even
restricted to bi-valued disutilities!) such that each agent `i`'s costs lie in `[p i, 2 * p i]`
for some `p i > 0`, **Partial-Round-First Round-Robin (`PRFRR`)** produces a complete exact EFX
allocation.

As an immediate corollary (`exists_efx_bivalued_ratio_le_two`), **every** personalized bi-valued
additive chores instance with `0 < p i ≤ q i ≤ 2 * p i` admits a complete EFX allocation for all
`n ≥ 1` and all `m ≥ 0`.

## Proof Idea
Write `m = n * q + u` with `q = m / n` and `u = m % n < n`.
* **Round `0` (partial round FIRST):** agents `0, 1, ..., u - 1` pick one minimum-cost remaining
  chore each in order.
* **Rounds `1, ..., q` (full rounds):** agents `0, 1, ..., n - 1` pick one minimum-cost remaining
  chore each in order.

For any agent `i` with `≥ 2` chores, `i`'s earliest pick `g_{i, t₀(i)}` has minimum cost in `X_i`,
so `τ_i(X_i) = ∑_{t = t₀(i)+1}^q c_i(g_{i, t})`.
* For `j > i`: turn `(t, j)` follows `(t, i)` for every `t ∈ {t₀(i)+1, ..., q}`, giving
  `c_i(X_j) ≥ τ_i(X_i)` directly (without even using the ratio-2 bound).
* For `j < i`: turn `(t + 1, j)` follows `(t, i)` for every `t ∈ {t₀(i), ..., q - 1}`, and
  `j` also has pick `g_{j, t₀(i)}`, giving
  `c_i(X_j) ≥ τ_i(X_i) + c_i(g_{i, t₀(i)}) + c_i(g_{j, t₀(i)}) - c_i(g_{i, q}) ≥ τ_i(X_i)`
  since `c_i(g_{i, t₀(i)}) ≥ p i`, `c_i(g_{j, t₀(i)}) ≥ p i`, and `c_i(g_{i, q}) ≤ 2 * p i`.
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
    set k := pick.symm g
    have hk_eq : prfrrPicker hn k = j := hg
    unfold prfrrPicker at hk_eq
    by_cases hku : k.1 < m % n
    · rw [dite_eq_left hku] at hk_eq
      have hjval : k.1 = j.1 := congrArg Fin.val hk_eq
      have hju : j.1 < m % n := by omega
      refine ⟨0, ?_, ?_⟩
      · simp [prfrrFirstRound, hju]
      · have hcond : prfrrFirstRound (m % n) j ≤ 0 ∧ 0 ≤ m / n := by
          simp [prfrrFirstRound, hju]
        dsimp only
        rw [dite_eq_left hcond]
        have hkeq : (⟨prfrrTurn n (m % n) 0 j, prfrrTurn_lt hn j hcond.1 hcond.2⟩ : Fin m) = k := by
          ext; simp [prfrrTurn, hjval]
        rw [hkeq]; exact Equiv.apply_symm_apply pick g
    · rw [dite_eq_right hku] at hk_eq
      have hjval : (k.1 - m % n) % n = j.1 := congrArg Fin.val hk_eq
      set d := (k.1 - m % n) / n
      have hdm : n * d + (k.1 - m % n) % n = k.1 - m % n := Nat.div_add_mod (k.1 - m % n) n
      have hdm_m : n * (m / n) + m % n = m := Nat.div_add_mod m n
      have hd_lt : d < m / n := by
        have hklt : k.1 < m := k.2
        have h1 : n * d < n * (m / n) := by omega
        exact Nat.lt_of_mul_lt_mul_left h1
      have hcond : prfrrFirstRound (m % n) j ≤ d + 1 ∧ d + 1 ≤ m / n :=
        ⟨by unfold prfrrFirstRound; split_ifs; exact Nat.zero_le _; exact Nat.succ_le_succ (Nat.zero_le d),
         Nat.succ_le_of_lt hd_lt⟩
      refine ⟨d + 1, ?_, ?_⟩
      · rw [Finset.mem_coe, Finset.mem_Ico]; exact ⟨hcond.1, by omega⟩
      · dsimp only
        rw [dite_eq_left hcond]
        have hkeq : (⟨prfrrTurn n (m % n) (d + 1) j, prfrrTurn_lt hn j hcond.1 hcond.2⟩ : Fin m) = k := by
          ext; simp only [prfrrTurn, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          rw [Nat.mul_comm] at hdm; omega
        rw [hkeq]; exact Equiv.apply_symm_apply pick g
  · intro t ht
    rw [Finset.mem_Ico] at ht
    have hcond : prfrrFirstRound (m % n) j ≤ t ∧ t ≤ m / n := ⟨ht.1, by omega⟩
    rw [dite_eq_left hcond, dite_eq_left hcond]

/-! ### Main Ratio-≤ 2 Additive Chores EFX Theorem -/

/-- **Main Theorem (Exact EFX for General-`n` Ratio-≤ 2 Additive Chores)**:
For every `n ≥ 1`, every `m ≥ 0`, and every additive chores instance `cost : Fin n → Fin m → ℝ`
where each agent `i`'s disutilities lie in `[p i, 2 * p i]` for some `p i > 0`,
Partial-Round-First Round-Robin (`PRFRR`) produces a complete exact EFX allocation. -/
theorem exists_efx_ratio_le_two
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i)
    (hlo : ∀ i g, p i ≤ cost i g)
    (hhi : ∀ i g, cost i g ≤ 2 * p i) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc := by
  classical
  obtain ⟨pick, hgreedy⟩ := exists_greedy_picking_order cost (prfrrPicker hn)
  let alloc : Fin m → Fin n := fun g => prfrrPicker hn (pick.symm g)
  refine ⟨alloc, fun i j g hg => ?_⟩
  rw [bundleCost_sdiff_singleton cost hg]
  have hcost_nn : ∀ a b, 0 ≤ cost a b := fun a b => le_trans (le_of_lt (hp a)) (hlo a b)
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
  -- Check if i has ≤ 1 chore (t0i ≥ q)
  by_cases hsmall : q ≤ t0i
  · -- Agent i receives at most 1 chore; since g ∈ bundle alloc i, i receives exactly 1 chore (at t0i = q)
    have ht0i_le : t0i ≤ q := by
      -- Since g ∈ bundle alloc i, bundle i is nonempty, hence Ico t0i (q+1) is nonempty
      by_contra hgt
      have hempty : Finset.Ico t0i (q + 1) = ∅ := Finset.Ico_eq_empty (by omega)
      have hzero : bundleCost cost (bundle alloc i) i = 0 := by
        rw [hcost_i, hempty, Finset.sum_empty]
      have hpos : 0 < bundleCost cost (bundle alloc i) i := by
        have hle : cost i g ≤ bundleCost cost (bundle alloc i) i := by
          unfold bundleCost
          exact Finset.single_le_sum (fun x _ => hcost_nn i x) hg
        linarith [hp i, hlo i g]
      linarith
    have hteq : t0i = q := le_antisymm ht0i_le hsmall
    have hIco : Finset.Ico t0i (q + 1) = {q} := by rw [hteq]; simp
    -- Also show cost i g = term i q (the unique chore in bundle alloc i)
    have hg_eq : term i q ≤ cost i g := by
      have hcond : prfrrFirstRound u i ≤ q ∧ q ≤ q := ⟨ht0i_le, le_refl q⟩
      simp only [term, hcond, and_self, ↓reduceDIte]
      have hk_pick : prfrrPicker hn (pick.symm g) = i := by
        simpa [alloc] using mem_bundle.mp hg
      -- Turn q for agent i is ≤ pick.symm g (in fact equal!)
      have hle_turn : (⟨prfrrTurn n u q i, prfrrTurn_lt hn i hcond.1 hcond.2⟩ : Fin m) ≤ pick.symm g := by
        -- Show pick.symm g has value = prfrrTurn n u q i
        set k := pick.symm g
        have hk_eq : prfrrPicker hn k = i := hk_pick
        unfold prfrrPicker at hk_eq
        by_cases hku : k.1 < u
        · rw [dite_eq_left hku] at hk_eq
          have hival : k.1 = i.1 := congrArg Fin.val hk_eq
          have hiu : i.1 < u := by omega
          have ht0i0 : t0i = 0 := by simp [t0i, prfrrFirstRound, hiu]
          have hq0 : q = 0 := by omega
          change prfrrTurn n u q i ≤ k.1
          simp [prfrrTurn, hq0, hival]
        · rw [dite_eq_right hku] at hk_eq
          have hival : (k.1 - u) % n = i.1 := congrArg Fin.val hk_eq
          have hdm : n * ((k.1 - u) / n) + (k.1 - u) % n = k.1 - u := Nat.div_add_mod _ n
          have hdm_m : n * q + u = m := Nat.div_add_mod m n
          have hd_lt : (k.1 - u) / n < q := by
            have h1 : n * ((k.1 - u) / n) < n * q := by have := k.2; omega
            exact Nat.lt_of_mul_lt_mul_left h1
          have hq1 : q = 1 := by
            have hteq' : (if i.1 < u then 0 else 1) = q := hteq
            have hqpos : 1 ≤ q := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) hd_lt)
            split_ifs at hteq' <;> omega
          have hd0 : (k.1 - u) / n = 0 := by
            rw [hq1] at hd_lt; exact Nat.lt_one_iff.mp hd_lt
          change prfrrTurn n u q i ≤ k.1
          simp only [prfrrTurn, hq1, Nat.succ_ne_zero, ↓reduceIte, Nat.sub_self, zero_mul, add_zero]
          rw [hd0, mul_zero, zero_add] at hdm
          omega
      have hgr := hgreedy ⟨prfrrTurn n u q i, prfrrTurn_lt hn i hcond.1 hcond.2⟩ (pick.symm g) hle_turn
      rw [prfrrPicker_turn hn i hcond.1 hcond.2, Equiv.apply_symm_apply] at hgr
      exact hgr
    rw [hIco, Finset.sum_singleton]
    have hj_nn : 0 ≤ ∑ t ∈ Finset.Ico t0j (q + 1), term j t :=
      Finset.sum_nonneg (fun t _ => hterm_nn j t)
    linarith
  · -- Main case: t0i < q (agent i receives ≥ 2 chores, rounds t0i .. q)
    push Not at hsmall
    -- Step 1: Agent i's first pick (round t0i) has cost ≤ cost i g
    have hcond0 : prfrrFirstRound u i ≤ t0i ∧ t0i ≤ q := ⟨le_refl _, le_of_lt hsmall⟩
    have hfirst_le_g : term i t0i ≤ cost i g := by
      simp only [term, hcond0, and_self, ↓reduceDIte]
      set k := pick.symm g
      have hk_eq : prfrrPicker hn k = i := by
        simpa [alloc] using mem_bundle.mp hg
      have hle_k : (⟨prfrrTurn n u t0i i, prfrrTurn_lt hn i hcond0.1 hcond0.2⟩ : Fin m) ≤ k := by
        change prfrrTurn n u t0i i ≤ k.1
        unfold prfrrPicker at hk_eq
        by_cases hku : k.1 < u
        · rw [dite_eq_left hku] at hk_eq
          have hival : k.1 = i.1 := congrArg Fin.val hk_eq
          have hiu : i.1 < u := by omega
          have ht0i0 : t0i = 0 := by simp [t0i, prfrrFirstRound, hiu]
          rw [ht0i0]; simp [prfrrTurn, hival]
        · rw [dite_eq_right hku] at hk_eq
          have hival : (k.1 - u) % n = i.1 := congrArg Fin.val hk_eq
          have hdm : n * ((k.1 - u) / n) + (k.1 - u) % n = k.1 - u := Nat.div_add_mod _ n
          by_cases hiu : i.1 < u
          · have ht0i0 : t0i = 0 := by simp [t0i, prfrrFirstRound, hiu]
            rw [ht0i0]; simp only [prfrrTurn, ↓reduceIte]; omega
          · have ht0i1 : t0i = 1 := by simp [t0i, prfrrFirstRound, hiu]
            rw [ht0i1]; simp only [prfrrTurn, Nat.succ_ne_zero, ↓reduceIte, Nat.sub_self, zero_mul, add_zero]
            omega
      have hgr := hgreedy ⟨prfrrTurn n u t0i i, prfrrTurn_lt hn i hcond0.1 hcond0.2⟩ k hle_k
      rw [prfrrPicker_turn hn i hcond0.1 hcond0.2, Equiv.apply_symm_apply] at hgr
      exact hgr
    -- Split ∑_{t0i}^{q} term i t = term i t0i + ∑_{t0i+1}^{q} term i t
    have hsplit_i : ∑ t ∈ Finset.Ico t0i (q + 1), term i t =
        term i t0i + ∑ t ∈ Finset.Ico (t0i + 1) (q + 1), term i t := by
      rw [← Finset.sum_eq_sum_Ico_succ_bot (by omega : t0i < q + 1)]
    have htau_bound : (∑ t ∈ Finset.Ico t0i (q + 1), term i t) - cost i g ≤
        ∑ t ∈ Finset.Ico (t0i + 1) (q + 1), term i t := by
      linarith
    refine le_trans htau_bound ?_
    -- Split by trichotomy between i and j!
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
    · -- Case 2: i = j (trivial!)
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
        rw [Finset.sum_Ico_succ_top (le_of_lt hsmall)]
      -- Apply the ratio-≤ 2 bounds: term i t0i ≥ p i, term j t0i ≥ p i, term i q ≤ 2 * p i!
      have hlo_i0 : p i ≤ term i t0i := by
        simp only [term, hcond0, and_self, ↓reduceDIte]; exact hlo i _
      have hcondj0 : prfrrFirstRound u j ≤ t0i ∧ t0i ≤ q := ⟨ht0j_le, le_of_lt hsmall⟩
      have hlo_j0 : p i ≤ term j t0i := by
        simp only [term, hcondj0, and_self, ↓reduceDIte]; exact hlo i _
      have hcondiq : prfrrFirstRound u i ≤ q ∧ q ≤ q := ⟨le_of_lt hsmall, le_refl q⟩
      have hhi_iq : term i q ≤ 2 * p i := by
        simp only [term, hcondiq, and_self, ↓reduceDIte]; exact hhi i _
      linarith

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
