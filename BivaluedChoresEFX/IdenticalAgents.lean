module

public import BivaluedChoresEFX.Basic

/-!
# Closed-Form Identical-Agent EFX Allocation and Structural Bounds

This module defines the closed-form water-filling allocation `identicalPile` for `t ≥ 1`
identical agents with bi-valued chore costs `{1, r}` (`1 < r`, `K = ⌈r⌉`), and proves:

1. **Sum identities**: total large items = `p`, total small items = `s`.
2. **Internal EFX (`identicalPile_internal_efx`)**: every pair of agents in the pile is EFX.
3. **Closed-form bounds**: `ownTau_le_pileTau`, `pileMinSize_le_size`, `maxLargeIdx_large_pos`.
4. **Fundamental bound (`pileTau_le_r_mul_minSize`)**: `pileTau t p s K r ≤ r * pileMinSize t p s K`.
5. **Universal `+1` Step Bound (`pileTau_step_lt`, `pileTau_step_le_tight`)** (Lemma A).
6. **Monotonicity of `pileTau` in `s` (`pileTau_mono_s`)**.
7. **Zero-Drop Lemma (`pileMinSize_sub_one_ge`)** (Lemma B).
8. **Single-Pile Impossibility Lemma (`pileTau_sub_one_le_of_maxLargeSize`)** (Lemma C).
9. **Phase-1 / Phase-3 No-Jump Bound (`phase1_bundle_lower_bound`)**.
-/

@[expose] public section

namespace BivaluedChoresEFX

open scoped BigOperators

/-! ### Arithmetic Helper Lemmas -/

/-- Existence of the ceiling integer `K = ⌈r⌉` for any real `r > 1`. -/
lemma exists_ceil_gt_one {r : ℝ} (hr : 1 < r) :
    ∃ K : ℕ, 2 ≤ K ∧ (K : ℝ) - 1 < r ∧ r ≤ (K : ℝ) := by
  refine ⟨Nat.ceil r, ?_, ?_, Nat.le_ceil r⟩
  · have h1 : 1 < Nat.ceil r := Nat.lt_ceil.mpr (by exact_mod_cast hr)
    omega
  · have hpos : (0 : ℝ) ≤ r := by linarith
    have hlt := Nat.ceil_lt_add_one hpos
    linarith

/-- Ceiling division `(s + d - 1) / d` for `d > 0`. -/
def ceilDiv (s d : ℕ) : ℕ := (s + d - 1) / d

lemma ceilDiv_eq_div_add_ite {s d : ℕ} (hd : 0 < d) (hs : 0 < s) :
    ceilDiv s d = s / d + if 0 < s % d then 1 else 0 := by
  unfold ceilDiv
  have hdm : d * (s / d) + s % d = s := Nat.div_add_mod s d
  have hmlt : s % d < d := Nat.mod_lt s hd
  split_ifs with hm
  · have hmul : d * (s / d + 1) = d * (s / d) + d := Nat.mul_succ d (s / d)
    have h1 : s + d - 1 = d * (s / d + 1) + (s % d - 1) := by omega
    rw [h1, Nat.mul_add_div hd, Nat.div_eq_of_lt (show s % d - 1 < d by omega), add_zero]
  · have hm0 : s % d = 0 := by omega
    have hq_pos : 1 ≤ s / d := by
      by_contra hq0
      have hq : s / d = 0 := Nat.eq_zero_of_not_pos (fun h => hq0 h)
      rw [hq, hm0] at hdm; simp at hdm; omega
    have h1 : s + d - 1 = d * (s / d) + (d - 1) := by omega
    rw [h1, Nat.mul_add_div hd, Nat.div_eq_of_lt (show d - 1 < d by omega), add_zero]

lemma ceilDiv_pos {s d : ℕ} (hd : 0 < d) (hs : 0 < s) : 1 ≤ ceilDiv s d := by
  rw [ceilDiv_eq_div_add_ite hd hs]
  have hdm : d * (s / d) + s % d = s := Nat.div_add_mod s d
  split_ifs with hm
  · exact Nat.le_add_left 1 (s / d)
  · have hm0 : s % d = 0 := by omega
    rw [add_zero]
    by_contra h0
    have hq : s / d = 0 := Nat.eq_zero_of_not_pos (fun h => h0 h)
    rw [hq, hm0] at hdm; simp at hdm; omega

lemma ceilDiv_le_of_le_mul {s d K : ℕ} (hd : 0 < d) (h : s ≤ d * K) :
    ceilDiv s d ≤ K := by
  unfold ceilDiv
  have hmul : d * (K + 1) = d * K + d := Nat.mul_succ d K
  have h1 : s + d - 1 < d * (K + 1) := by omega
  have h2 : (s + d - 1) / d < K + 1 := (Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.mul_comm]; exact h1)
  omega

lemma ceilDiv_sub_one_mul_lt {s d : ℕ} (hd : 0 < d) (hs : 0 < s) :
    (ceilDiv s d - 1) * d < s := by
  rw [ceilDiv_eq_div_add_ite hd hs]
  have hdm : d * (s / d) + s % d = s := Nat.div_add_mod s d
  have hmlt : s % d < d := Nat.mod_lt s hd
  split_ifs with hm
  · simp only [Nat.add_sub_cancel]
    nlinarith
  · have hm0 : s % d = 0 := by omega
    have hq_pos : 1 ≤ s / d := by
      by_contra h0
      have hq : s / d = 0 := Nat.eq_zero_of_not_pos (fun h => h0 h)
      rw [hq, hm0] at hdm; simp at hdm; omega
    rw [add_zero]
    have hsub : (s / d - 1) * d + d = (s / d) * d := by
      have := Nat.add_one_mul (s / d - 1) d
      have h1 : s / d - 1 + 1 = s / d := by omega
      rw [h1] at this; exact this.symm
    nlinarith

lemma ceilDiv_mono {s₁ s₂ d : ℕ} (h : s₁ ≤ s₂) : ceilDiv s₁ d ≤ ceilDiv s₂ d := by
  unfold ceilDiv
  exact Nat.div_le_div_right (by omega)

lemma ceilDiv_succ_sub_one {b t : ℕ} (ht : 0 < t) :
    ceilDiv (b + 1) t - 1 = b / t := by
  unfold ceilDiv
  have h1 : b + 1 + t - 1 = t * 1 + b := by omega
  rw [h1, Nat.mul_add_div ht, Nat.add_sub_cancel_left]

lemma div_mod_succ_of_lt {p t : ℕ} (ht : 0 < t) (h : p % t + 1 < t) :
    (p + 1) / t = p / t ∧ (p + 1) % t = p % t + 1 := by
  have hdm : t * (p / t) + p % t = p := Nat.div_add_mod p t
  have h1 : p + 1 = t * (p / t) + (p % t + 1) := by omega
  constructor
  · rw [h1, Nat.mul_add_div ht, Nat.div_eq_of_lt h, add_zero]
  · rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

lemma div_mod_succ_of_eq {p t : ℕ} (ht : 0 < t) (h : p % t + 1 = t) :
    (p + 1) / t = p / t + 1 ∧ (p + 1) % t = 0 := by
  have hdm : t * (p / t) + p % t = p := Nat.div_add_mod p t
  have hmul : t * (p / t + 1) = t * (p / t) + t := Nat.mul_succ t (p / t)
  have h1 : p + 1 = t * (p / t + 1) := by omega
  constructor
  · rw [h1, Nat.mul_div_cancel_left _ ht]
  · rw [h1, Nat.mul_mod_right]

lemma add_mul_div_mod {K rem t : ℕ} (ht : 0 < t) :
    (t * K + rem) / t = K + rem / t ∧ (t * K + rem) % t = rem % t :=
  ⟨Nat.mul_add_div ht K rem, Nat.mul_add_mod t K rem⟩

/-! ### Definition of `IdenticalEFX` Pile -/

/-- Auxiliary large-item count given `ell = p / t, u = p % t`. -/
def pileLargeAux (t ell u : ℕ) (i : Fin t) : ℕ :=
  if i.1 < u then ell + 1 else ell

/-- Number of own-large items assigned to agent `i : Fin t` in `IdenticalEFX(t, p, s, K)`. -/
def pileLarge (t p : ℕ) (i : Fin t) : ℕ :=
  pileLargeAux t (p / t) (p % t) i

/-- Auxiliary small-item count given `u = p % t`. -/
def pileSmallAux (t u s K : ℕ) (i : Fin t) : ℕ :=
  if s ≤ (t - u) * K then
    if i.1 < u then 0
    else s / (t - u) + if i.1 - u < s % (t - u) then 1 else 0
  else
    if (s - (t - u) * K) % t ≤ u then
      if i.1 < u then (s - (t - u) * K) / t + if i.1 < (s - (t - u) * K) % t then 1 else 0
      else K + (s - (t - u) * K) / t
    else
      if i.1 < u then (s - (t - u) * K) / t + 1
      else K + (s - (t - u) * K) / t + if i.1 - u < (s - (t - u) * K) % t - u then 1 else 0

/-- Number of own-small items assigned to agent `i : Fin t` in `IdenticalEFX(t, p, s, K)`. -/
def pileSmall (t p s K : ℕ) (i : Fin t) : ℕ :=
  pileSmallAux t (p % t) s K i

/-- Own cost of a bundle `(L, S)` to an agent with large cost `r` and small cost `1`. -/
def ownCost (r : ℝ) (L S : ℕ) : ℝ :=
  (L : ℝ) * r + (S : ℝ)

/-- EFX envy threshold of a bundle `(L, S)`: maximum cost after removing one chore (or `0` if empty). -/
def ownTau (r : ℝ) (L S : ℕ) : ℝ :=
  if L + S = 0 then 0
  else ownCost r L S - if 0 < S then 1 else r

/-- Auxiliary closed-form threshold given `ell = p / t` and `u = p % t`. -/
def pileTauAux (t ell u s K : ℕ) (r : ℝ) : ℝ :=
  if s ≤ (t - u) * K then
    if s = 0 then
      if 0 < u then (ell : ℝ) * r
      else if 0 < ell then ((ell - 1 : ℕ) : ℝ) * r
      else 0
    else
      (ell : ℝ) * r + ((ceilDiv s (t - u) - 1 : ℕ) : ℝ)
  else
    if (s - (t - u) * K) % t ≤ u then
      if 0 < (s - (t - u) * K) % t then
        ((ell + 1 : ℕ) : ℝ) * r + (((s - (t - u) * K) / t : ℕ) : ℝ)
      else
        (ell : ℝ) * r + (K : ℝ) + (((s - (t - u) * K) / t : ℕ) : ℝ) - 1
    else
      (ell : ℝ) * r + (K : ℝ) + (((s - (t - u) * K) / t : ℕ) : ℝ)

/-- Closed-form upper bound (in fact exact maximum) on `ownTau` across all bundles of `identicalPile`. -/
def pileTau (t p s K : ℕ) (r : ℝ) : ℝ :=
  pileTauAux t (p / t) (p % t) s K r

/-- Auxiliary closed-form minimum bundle size given `ell = p / t` and `u = p % t`. -/
def pileMinSizeAux (t ell u s K : ℕ) : ℕ :=
  if s ≤ (t - u) * K then
    if u = 0 then ell + s / t
    else if s < t - u then ell
    else ell + 1
  else
    if u = 0 then ell + K + (s - (t - u) * K) / t
    else if (s - (t - u) * K) % t < u then ell + (s - (t - u) * K) / t + 1
    else ell + (s - (t - u) * K) / t + 2

/-- Closed-form minimum bundle size `min_i (L_i + S_i)` in `identicalPile`. -/
def pileMinSize (t p s K : ℕ) : ℕ :=
  pileMinSizeAux t (p / t) (p % t) s K

/-- Witness bundle index with `pileLarge > 0` (when `p ≥ 1`) used for single-cross-item placement. -/
def maxLargeIdx (t p s K : ℕ) (ht : 0 < t) : Fin t :=
  if 0 < p % t ∧ 0 < p / t ∧ 0 < s ∧ s ≤ (t - p % t) * K then
    ⟨p % t, Nat.mod_lt p ht⟩
  else
    ⟨0, ht⟩

/-- Size of the witness large bundle `maxLargeIdx`. -/
def maxLargeSize (t p s K : ℕ) (ht : 0 < t) : ℕ :=
  pileLarge t p (maxLargeIdx t p s K ht) + pileSmall t p s K (maxLargeIdx t p s K ht)

/-! ### Sum Identities -/

private lemma sum_ite_lt {t k : ℕ} (hk : k ≤ t) :
    ∑ i : Fin t, (if i.1 < k then (1 : ℕ) else 0) = k := by
  rw [Finset.sum_boole, Nat.cast_id]
  have hcard : (Finset.univ : Finset (Fin k)).card =
      (Finset.univ.filter (fun i : Fin t => i.1 < k)).card := by
    refine Finset.card_nbij (fun y => (⟨y.1, by omega⟩ : Fin t)) ?_ ?_ ?_
    · intro y _; simp [y.2]
    · intro y₁ _ y₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin t → ℕ) h)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact ⟨⟨x.1, hx⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
  simpa using hcard.symm

private lemma sum_ite_ge {t u : ℕ} (hu : u ≤ t) :
    ∑ i : Fin t, (if i.1 < u then (0 : ℕ) else 1) = t - u := by
  have h1 : ∀ i : Fin t, (if i.1 < u then (1 : ℕ) else 0) + (if i.1 < u then 0 else 1) = 1 := by
    intro i; split_ifs <;> omega
  have hsum : ∑ i : Fin t, ((if i.1 < u then (1 : ℕ) else 0) + (if i.1 < u then 0 else 1)) = t := by
    simp [h1]
  rw [Finset.sum_add_distrib, sum_ite_lt hu] at hsum
  omega

private lemma sum_ite_ge_lt {t u k : ℕ} (huk : u + k ≤ t) :
    ∑ i : Fin t, (if i.1 < u then (0 : ℕ) else if i.1 - u < k then 1 else 0) = k := by
  have heq : ∀ i : Fin t,
      (if i.1 < u then (0 : ℕ) else if i.1 - u < k then 1 else 0) =
      (if ¬ i.1 < u ∧ i.1 - u < k then 1 else 0) := by
    intro i; split_ifs <;> simp_all
  simp_rw [heq, Finset.sum_boole, Nat.cast_id]
  have hcard : (Finset.univ : Finset (Fin k)).card =
      (Finset.univ.filter (fun i : Fin t => ¬ i.1 < u ∧ i.1 - u < k)).card := by
    refine Finset.card_nbij (fun y => (⟨u + y.1, by omega⟩ : Fin t)) ?_ ?_ ?_
    · intro y _; simp [y.2]
    · intro y₁ _ y₂ _ h
      have hv : u + y₁.1 = u + y₂.1 := congrArg (Fin.val : Fin t → ℕ) h
      exact Fin.ext (by omega)
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
      refine ⟨⟨x.1 - u, hx.2⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      ext; simp; omega
  simpa using hcard.symm

lemma sum_pileLarge {t p : ℕ} (ht : 0 < t) :
    ∑ i : Fin t, pileLarge t p i = p := by
  have heq : ∀ i : Fin t, pileLarge t p i = p / t + if i.1 < p % t then 1 else 0 := by
    intro i; unfold pileLarge pileLargeAux; split_ifs <;> omega
  simp_rw [heq, Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      sum_ite_lt (le_of_lt (Nat.mod_lt p ht))]
  exact Nat.div_add_mod p t

private lemma sum_pileSmallAux {t u s K : ℕ} (ht : 0 < t) (hu_lt : u < t) :
    ∑ i : Fin t, pileSmallAux t u s K i = s := by
  have htu_pos : 0 < t - u := by omega
  by_cases hle : s ≤ (t - u) * K
  · have heq : ∀ i : Fin t, pileSmallAux t u s K i =
        (s / (t - u)) * (if i.1 < u then 0 else 1) +
        (if i.1 < u then 0 else if i.1 - u < s % (t - u) then 1 else 0) := by
      intro i; unfold pileSmallAux; rw [ite_eq_left hle]; split_ifs <;> ring
    simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [sum_ite_ge (le_of_lt hu_lt), sum_ite_ge_lt (by have := Nat.mod_lt s htu_pos; omega)]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod s (t - u)
  · have hs_gt : (t - u) * K < s := by omega
    have hdm : t * ((s - (t - u) * K) / t) + (s - (t - u) * K) % t = s - (t - u) * K :=
      Nat.div_add_mod _ t
    have hv_lt : (s - (t - u) * K) % t < t := Nat.mod_lt _ ht
    have hrem_add : (t - u) * K + (s - (t - u) * K) = s := by omega
    generalize hw : (s - (t - u) * K) / t = w at hdm
    generalize hv : (s - (t - u) * K) % t = v at hdm hv_lt
    by_cases hvu : v ≤ u
    · have heq : ∀ i : Fin t, pileSmallAux t u s K i =
          w + (K * (if i.1 < u then 0 else 1) + if i.1 < v then 1 else 0) := by
        intro i; unfold pileSmallAux
        rw [ite_eq_right hle, hw, hv, ite_eq_left hvu]
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu, ite_eq_left hiu]; split_ifs <;> omega
        · have hiv : ¬ i.1 < v := by omega
          rw [ite_eq_right hiu, ite_eq_right hiu, ite_eq_right hiv]; omega
      simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          sum_ite_ge (le_of_lt hu_lt), sum_ite_lt (le_of_lt hv_lt)]
      have hcomm : K * (t - u) = (t - u) * K := Nat.mul_comm K (t - u)
      omega
    · have heq : ∀ i : Fin t, pileSmallAux t u s K i =
          w + ((if i.1 < u then 1 else 0) +
          (K * (if i.1 < u then 0 else 1) +
           (if i.1 < u then 0 else if i.1 - u < v - u then 1 else 0))) := by
        intro i; unfold pileSmallAux
        rw [ite_eq_right hle, hw, hv, ite_eq_right hvu]
        split_ifs <;> omega
      simp_rw [heq, Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          sum_ite_lt (le_of_lt hu_lt), sum_ite_ge (le_of_lt hu_lt),
          sum_ite_ge_lt (by omega : u + (v - u) ≤ t)]
      have hcomm : K * (t - u) = (t - u) * K := Nat.mul_comm K (t - u)
      omega

lemma sum_pileSmall {t p s K : ℕ} (ht : 0 < t) :
    ∑ i : Fin t, pileSmall t p s K i = s :=
  sum_pileSmallAux ht (Nat.mod_lt p ht)

/-! ### Internal EFX of `IdenticalEFX` -/

private lemma identicalPileAux_internal_efx {t ell u s K : ℕ} {r : ℝ}
    (hu_lt : u < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (i j : Fin t) :
    ownTau r (pileLargeAux t ell u i) (pileSmallAux t u s K i) ≤
      ownCost r (pileLargeAux t ell u j) (pileSmallAux t u s K j) := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have htu_pos : 0 < t - u := by omega
  by_cases hle : s ≤ (t - u) * K
  · -- Regime U
    have hq_le : s / (t - u) ≤ K := by
      have h1 : s / (t - u) ≤ ((t - u) * K) / (t - u) := Nat.div_le_div_right hle
      rwa [Nat.mul_div_cancel_left K htu_pos] at h1
    have hq_strict : 0 < s % (t - u) → s / (t - u) + 1 ≤ K := by
      intro hmod
      have hdm : (t - u) * (s / (t - u)) + s % (t - u) = s := Nat.div_add_mod s (t - u)
      have hlt : (t - u) * (s / (t - u)) < (t - u) * K := by omega
      exact Nat.lt_of_mul_lt_mul_left hlt
    have hSi_le_K : pileSmallAux t u s K i ≤ K := by
      unfold pileSmallAux; rw [ite_eq_left hle]
      split_ifs with h1 h2
      · omega
      · exact hq_strict (by omega)
      · exact hq_le
    by_cases hiu : i.1 < u
    · have hLi : pileLargeAux t ell u i = ell + 1 := ite_eq_left hiu
      have hSi : pileSmallAux t u s K i = 0 := by unfold pileSmallAux; rw [ite_eq_left hle, ite_eq_left hiu]
      rw [hLi, hSi]
      have htau : ownTau r (ell + 1) 0 = (ell : ℝ) * r := by
        unfold ownTau ownCost
        rw [ite_eq_right (by omega : ell + 1 + 0 ≠ 0), ite_eq_right (lt_irrefl 0)]
        push_cast; ring
      rw [htau]
      have hLj : ell ≤ pileLargeAux t ell u j := by unfold pileLargeAux; split_ifs <;> omega
      unfold ownCost
      have hLjR : (ell : ℝ) ≤ (pileLargeAux t ell u j : ℝ) := by exact_mod_cast hLj
      have hSjR : (0 : ℝ) ≤ (pileSmallAux t u s K j : ℝ) := Nat.cast_nonneg _
      nlinarith
    · have hLi : pileLargeAux t ell u i = ell := ite_eq_right hiu
      have hSi_eq : pileSmallAux t u s K i = s / (t - u) + if i.1 - u < s % (t - u) then 1 else 0 := by
        unfold pileSmallAux; rw [ite_eq_left hle, ite_eq_right hiu]
      by_cases hSi0 : pileSmallAux t u s K i = 0
      · rw [hLi, hSi0]
        have htau_le : ownTau r ell 0 ≤ (ell : ℝ) * r := by
          unfold ownTau ownCost
          simp only [lt_self_iff_false, ↓reduceIte, Nat.cast_zero, add_zero]
          split_ifs
          · positivity
          · linarith
        have hLj : ell ≤ pileLargeAux t ell u j := by unfold pileLargeAux; split_ifs <;> omega
        unfold ownCost
        have hLjR : (ell : ℝ) ≤ (pileLargeAux t ell u j : ℝ) := by exact_mod_cast hLj
        have hSjR : (0 : ℝ) ≤ (pileSmallAux t u s K j : ℝ) := Nat.cast_nonneg _
        nlinarith
      · have hSi_pos : 0 < pileSmallAux t u s K i := by omega
        have htau : ownTau r (pileLargeAux t ell u i) (pileSmallAux t u s K i) =
            (ell : ℝ) * r + (pileSmallAux t u s K i : ℝ) - 1 := by
          rw [hLi]; unfold ownTau ownCost
          rw [ite_eq_right (by omega : ell + pileSmallAux t u s K i ≠ 0), ite_eq_left hSi_pos]
        rw [htau]
        by_cases hju : j.1 < u
        · have hLj : pileLargeAux t ell u j = ell + 1 := ite_eq_left hju
          have hSj : pileSmallAux t u s K j = 0 := by unfold pileSmallAux; rw [ite_eq_left hle, ite_eq_left hju]
          rw [hLj, hSj]; unfold ownCost
          have hSiK : (pileSmallAux t u s K i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hSi_le_K
          push_cast; linarith
        · have hLj : pileLargeAux t ell u j = ell := ite_eq_right hju
          have hSj_ge : s / (t - u) ≤ pileSmallAux t u s K j := by
            unfold pileSmallAux; rw [ite_eq_left hle, ite_eq_right hju]; exact Nat.le_add_right _ _
          have hSi_le : pileSmallAux t u s K i ≤ s / (t - u) + 1 := by
            rw [hSi_eq]; split_ifs <;> omega
          rw [hLj]; unfold ownCost
          have hcmp : (pileSmallAux t u s K i : ℝ) ≤ (pileSmallAux t u s K j : ℝ) + 1 := by
            have : pileSmallAux t u s K i ≤ pileSmallAux t u s K j + 1 := by omega
            exact_mod_cast this
          linarith
  · -- Regime O: generalize w, v!
    unfold pileSmallAux
    rw [ite_eq_right hle, ite_eq_right hle]
    generalize (s - (t - u) * K) / t = w
    generalize (s - (t - u) * K) % t = v
    by_cases hvu : v ≤ u
    · rw [ite_eq_left hvu, ite_eq_left hvu]
      have hcost_j : ((ell : ℝ) + 1) * r + (w : ℝ) ≤
          ownCost r (pileLargeAux t ell u j) (if j.1 < u then w + if j.1 < v then 1 else 0 else K + w) := by
        unfold pileLargeAux ownCost
        by_cases hju : j.1 < u
        · rw [ite_eq_left hju, ite_eq_left hju]; split_ifs <;> push_cast <;> linarith
        · rw [ite_eq_right hju, ite_eq_right hju]; push_cast; linarith
      have htau_i : ownTau r (pileLargeAux t ell u i)
            (if i.1 < u then w + if i.1 < v then 1 else 0 else K + w) ≤
          ((ell : ℝ) + 1) * r + (w : ℝ) := by
        unfold pileLargeAux ownTau ownCost
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu, ite_eq_left hiu]
          by_cases hiv : i.1 < v
          · rw [ite_eq_left hiv, ite_eq_right (by omega : ell + 1 + (w + 1) ≠ 0),
                ite_eq_left (by omega : 0 < w + 1)]
            push_cast; linarith
          · rw [ite_eq_right hiv, add_zero, ite_eq_right (by omega : ell + 1 + w ≠ 0)]
            split_ifs <;> push_cast <;> linarith
        · rw [ite_eq_right hiu, ite_eq_right hiu,
              ite_eq_right (by omega : ell + (K + w) ≠ 0), ite_eq_left (by omega : 0 < K + w)]
          push_cast; linarith
      exact le_trans htau_i hcost_j
    · rw [ite_eq_right hvu, ite_eq_right hvu]
      have hcost_j : (ell : ℝ) * r + (K : ℝ) + (w : ℝ) ≤
          ownCost r (pileLargeAux t ell u j)
            (if j.1 < u then w + 1 else K + w + if j.1 - u < v - u then 1 else 0) := by
        unfold pileLargeAux ownCost
        by_cases hju : j.1 < u
        · rw [ite_eq_left hju, ite_eq_left hju]; push_cast; linarith
        · rw [ite_eq_right hju, ite_eq_right hju]; split_ifs <;> push_cast <;> linarith
      have htau_i : ownTau r (pileLargeAux t ell u i)
            (if i.1 < u then w + 1 else K + w + if i.1 - u < v - u then 1 else 0) ≤
          (ell : ℝ) * r + (K : ℝ) + (w : ℝ) := by
        unfold pileLargeAux ownTau ownCost
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu, ite_eq_left hiu,
              ite_eq_right (by omega : ell + 1 + (w + 1) ≠ 0), ite_eq_left (by omega : 0 < w + 1)]
          push_cast; linarith
        · rw [ite_eq_right hiu, ite_eq_right hiu]
          by_cases hiv : i.1 - u < v - u
          · rw [ite_eq_left hiv, ite_eq_right (by omega : ell + (K + w + 1) ≠ 0),
                ite_eq_left (by omega : 0 < K + w + 1)]
            push_cast; linarith
          · rw [ite_eq_right hiv, add_zero, ite_eq_right (by omega : ell + (K + w) ≠ 0),
                ite_eq_left (by omega : 0 < K + w)]
            push_cast; linarith
      exact le_trans htau_i hcost_j

lemma identicalPile_internal_efx {t p s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (i j : Fin t) :
    ownTau r (pileLarge t p i) (pileSmall t p s K i) ≤
      ownCost r (pileLarge t p j) (pileSmall t p s K j) :=
  identicalPileAux_internal_efx (Nat.mod_lt p ht) hr hK_lo hK_hi i j

/-! ### Relating Individual Bundles to `pileTau`, `pileMinSize`, `maxLargeSize` -/

private lemma ownTau_le_pileTauAux {t ell u s K : ℕ} {r : ℝ}
    (hu_lt : u < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (i : Fin t) :
    ownTau r (pileLargeAux t ell u i) (pileSmallAux t u s K i) ≤ pileTauAux t ell u s K r := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have htu_pos : 0 < t - u := by omega
  unfold pileTauAux pileSmallAux pileLargeAux
  by_cases hle : s ≤ (t - u) * K
  · rw [ite_eq_left hle, ite_eq_left hle]
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0, hs0]
      simp only [Nat.zero_div, Nat.zero_mod, Nat.not_lt_zero, ↓reduceIte, add_zero]
      have hzero : (if i.1 < u then (0 : ℕ) else 0) = 0 := by split_ifs <;> rfl
      rw [hzero]
      by_cases hu0 : 0 < u
      · rw [ite_eq_left hu0]
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu]; unfold ownTau ownCost
          rw [ite_eq_right (by omega : ell + 1 + 0 ≠ 0), ite_eq_right (lt_irrefl 0)]
          push_cast; linarith
        · rw [ite_eq_right hiu]; unfold ownTau ownCost
          simp only [lt_self_iff_false, ↓reduceIte, Nat.cast_zero, add_zero]
          split_ifs
          · positivity
          · linarith
      · rw [ite_eq_right hu0, ite_eq_right (by omega : ¬ i.1 < u)]
        by_cases hell0 : 0 < ell
        · rw [ite_eq_left hell0]; unfold ownTau ownCost
          rw [ite_eq_right (by omega : ell + 0 ≠ 0), ite_eq_right (lt_irrefl 0),
              Nat.cast_sub (by omega : 1 ≤ ell)]
          push_cast; linarith
        · rw [ite_eq_right hell0, show ell = 0 by omega]; simp [ownTau]
    · rw [ite_eq_right hs0]
      have hs_pos : 0 < s := by omega
      have hceil_pos : 1 ≤ ceilDiv s (t - u) := ceilDiv_pos htu_pos hs_pos
      by_cases hiu : i.1 < u
      · rw [ite_eq_left hiu, ite_eq_left hiu]; unfold ownTau ownCost
        rw [ite_eq_right (by omega : ell + 1 + 0 ≠ 0), ite_eq_right (lt_irrefl 0)]
        have hnn : (0 : ℝ) ≤ ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        push_cast; linarith
      · rw [ite_eq_right hiu, ite_eq_right hiu]
        set S := s / (t - u) + if i.1 - u < s % (t - u) then 1 else 0
        have hS_le : S ≤ ceilDiv s (t - u) := by
          rw [ceilDiv_eq_div_add_ite htu_pos hs_pos]
          dsimp only [S]; split_ifs <;> omega
        unfold ownTau ownCost
        by_cases hS0 : S = 0
        · rw [hS0]
          simp only [lt_self_iff_false, ↓reduceIte, Nat.cast_zero, add_zero]
          have hnn : (0 : ℝ) ≤ ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
          split_ifs
          · have : (0 : ℝ) ≤ (ell : ℝ) * r := by positivity
            linarith
          · linarith
        · have hS_pos : 0 < S := Nat.pos_of_ne_zero hS0
          have hne : ell + S ≠ 0 := Nat.ne_of_gt (Nat.add_pos_right ell hS_pos)
          rw [ite_eq_right hne, ite_eq_left hS_pos]
          have hsub : S - 1 ≤ ceilDiv s (t - u) - 1 := by omega
          have hsubR : ((S - 1 : ℕ) : ℝ) ≤ ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) := by exact_mod_cast hsub
          rw [Nat.cast_sub (Nat.succ_le_of_lt hS_pos), Nat.cast_one] at hsubR
          linarith
  · rw [ite_eq_right hle, ite_eq_right hle]
    have hrem_pos : 0 < s - (t - u) * K := by omega
    have hdm : t * ((s - (t - u) * K) / t) + (s - (t - u) * K) % t = s - (t - u) * K :=
      Nat.div_add_mod _ t
    generalize (s - (t - u) * K) / t = w at hdm
    generalize (s - (t - u) * K) % t = v at hdm
    by_cases hvu : v ≤ u
    · rw [ite_eq_left hvu, ite_eq_left hvu]
      by_cases hv0 : 0 < v
      · rw [ite_eq_left hv0]
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu, ite_eq_left hiu]; unfold ownTau ownCost
          by_cases hiv : i.1 < v
          · rw [ite_eq_left hiv, ite_eq_right (by omega : ell + 1 + (w + 1) ≠ 0),
                ite_eq_left (by omega : 0 < w + 1)]
            push_cast; linarith
          · rw [ite_eq_right hiv, add_zero, ite_eq_right (by omega : ell + 1 + w ≠ 0)]
            split_ifs <;> push_cast <;> linarith
        · rw [ite_eq_right hiu, ite_eq_right hiu]; unfold ownTau ownCost
          rw [ite_eq_right (by omega : ell + (K + w) ≠ 0), ite_eq_left (by omega : 0 < K + w)]
          push_cast; linarith
      · rw [ite_eq_right hv0]
        have hv_eq : v = 0 := by omega
        have hw_pos : 1 ≤ w := by
          rw [hv_eq, add_zero] at hdm
          by_contra hw0
          have hw : w = 0 := Nat.eq_zero_of_not_pos (fun h => hw0 h)
          rw [hw] at hdm; simp at hdm; omega
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu, ite_eq_left hiu, hv_eq]
          simp only [Nat.not_lt_zero, ↓reduceIte, add_zero]
          unfold ownTau ownCost
          rw [ite_eq_right (by omega : ell + 1 + w ≠ 0), ite_eq_left (by omega : 0 < w)]
          push_cast; linarith
        · rw [ite_eq_right hiu, ite_eq_right hiu]; unfold ownTau ownCost
          rw [ite_eq_right (by omega : ell + (K + w) ≠ 0), ite_eq_left (by omega : 0 < K + w)]
          push_cast; linarith
    · rw [ite_eq_right hvu, ite_eq_right hvu]
      by_cases hiu : i.1 < u
      · rw [ite_eq_left hiu, ite_eq_left hiu]; unfold ownTau ownCost
        rw [ite_eq_right (by omega : ell + 1 + (w + 1) ≠ 0), ite_eq_left (by omega : 0 < w + 1)]
        push_cast; linarith
      · rw [ite_eq_right hiu, ite_eq_right hiu]; unfold ownTau ownCost
        by_cases hiv : i.1 - u < v - u
        · rw [ite_eq_left hiv, ite_eq_right (by omega : ell + (K + w + 1) ≠ 0),
              ite_eq_left (by omega : 0 < K + w + 1)]
          push_cast; linarith
        · rw [ite_eq_right hiv, add_zero, ite_eq_right (by omega : ell + (K + w) ≠ 0),
              ite_eq_left (by omega : 0 < K + w)]
          push_cast; linarith

lemma ownTau_le_pileTau {t p s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) (i : Fin t) :
    ownTau r (pileLarge t p i) (pileSmall t p s K i) ≤ pileTau t p s K r :=
  ownTau_le_pileTauAux (Nat.mod_lt p ht) hr hK_lo hK_hi i

private lemma pileMinSizeAux_le_size {t ell u s K : ℕ}
    (hu_lt : u < t) (hK : 2 ≤ K) (i : Fin t) :
    pileMinSizeAux t ell u s K ≤ pileLargeAux t ell u i + pileSmallAux t u s K i := by
  have htu_pos : 0 < t - u := by omega
  unfold pileMinSizeAux pileLargeAux pileSmallAux
  by_cases hle : s ≤ (t - u) * K
  · rw [ite_eq_left hle, ite_eq_left hle]
    by_cases hu0 : u = 0
    · rw [ite_eq_left hu0, hu0, Nat.sub_zero, ite_eq_right (Nat.not_lt_zero i.1)]
      exact Nat.add_le_add_left (Nat.le_add_right _ _) ell
    · rw [ite_eq_right hu0]
      by_cases hlt : s < t - u
      · rw [ite_eq_left hlt]
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu, ite_eq_left hiu]; omega
        · rw [ite_eq_right hiu, ite_eq_right hiu]; exact Nat.le_add_right _ _
      · rw [ite_eq_right hlt]
        have hq : 1 ≤ s / (t - u) := (Nat.le_div_iff_mul_le htu_pos).mpr (by omega)
        by_cases hiu : i.1 < u
        · rw [ite_eq_left hiu, ite_eq_left hiu]
        · rw [ite_eq_right hiu, ite_eq_right hiu]; omega
  · rw [ite_eq_right hle, ite_eq_right hle]
    generalize (s - (t - u) * K) / t = w
    generalize (s - (t - u) * K) % t = v
    by_cases hu0 : u = 0
    · rw [ite_eq_left hu0, hu0, ite_eq_right (Nat.not_lt_zero i.1)]
      split_ifs <;> omega
    · rw [ite_eq_right hu0]
      by_cases hvu : v < u
      · rw [ite_eq_left hvu, ite_eq_left (le_of_lt hvu)]
        split_ifs <;> omega
      · rw [ite_eq_right hvu]
        by_cases hveq : v ≤ u
        · rw [ite_eq_left hveq]
          by_cases hiu : i.1 < u
          · rw [ite_eq_left hiu, ite_eq_left hiu, ite_eq_left (by omega : i.1 < v)]; omega
          · rw [ite_eq_right hiu, ite_eq_right hiu]; omega
        · rw [ite_eq_right hveq]
          split_ifs <;> omega

lemma pileMinSize_le_size {t p s K : ℕ} (ht : 0 < t) (hK : 2 ≤ K) (i : Fin t) :
    pileMinSize t p s K ≤ pileLarge t p i + pileSmall t p s K i :=
  pileMinSizeAux_le_size (Nat.mod_lt p ht) hK i

lemma maxLargeIdx_large_pos {t p s K : ℕ} (ht : 0 < t) (hp : 0 < p) :
    0 < pileLarge t p (maxLargeIdx t p s K ht) := by
  unfold maxLargeIdx pileLarge pileLargeAux
  by_cases hc : 0 < p % t ∧ 0 < p / t ∧ 0 < s ∧ s ≤ (t - p % t) * K
  · rw [ite_eq_left hc]
    simp only [lt_self_iff_false, ↓reduceIte]
    exact hc.2.1
  · rw [ite_eq_right hc]
    by_cases hu : 0 < p % t
    · rw [ite_eq_left hu]; exact Nat.succ_pos _
    · rw [ite_eq_right hu]
      have hdm : t * (p / t) + p % t = p := Nat.div_add_mod p t
      have hm0 : p % t = 0 := by omega
      by_contra h0
      have hq : p / t = 0 := Nat.eq_zero_of_not_pos (fun h => h0 h)
      rw [hq, hm0] at hdm; simp at hdm; omega

/-! ### Exact Formulas When `u = 0` -/

lemma pileMinSizeAux_u0 {t ell s K : ℕ} (ht : 0 < t) :
    pileMinSizeAux t ell 0 s K = ell + s / t := by
  unfold pileMinSizeAux
  simp only [Nat.sub_zero, ↓reduceIte]
  by_cases h : s ≤ t * K
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have hs_eq : s = t * K + (s - t * K) := by omega
    have hdiv : s / t = K + (s - t * K) / t := by
      conv_lhs => rw [hs_eq]
      exact (add_mul_div_mod ht).1
    omega

lemma pileTauAux_u0_pos {t ell s K : ℕ} {r : ℝ} (ht : 0 < t) (hs : 0 < s) (hK : 1 ≤ K) :
    pileTauAux t ell 0 s K r = (ell : ℝ) * r + ((ceilDiv s t - 1 : ℕ) : ℝ) := by
  unfold pileTauAux
  simp only [Nat.sub_zero]
  by_cases h : s ≤ t * K
  · rw [ite_eq_left h, ite_eq_right (by omega : s ≠ 0)]
  · rw [ite_eq_right h]
    have hs_eq : s = t * K + (s - t * K) := by omega
    have hdm := add_mul_div_mod (K := K) (rem := s - t * K) ht
    have hdiv : s / t = K + (s - t * K) / t := by conv_lhs => rw [hs_eq]; exact hdm.1
    have hmod : s % t = (s - t * K) % t := by conv_lhs => rw [hs_eq]; exact hdm.2
    rw [ceilDiv_eq_div_add_ite ht hs, hdiv, hmod]
    generalize (s - t * K) / t = w
    generalize (s - t * K) % t = v
    by_cases hm0 : v = 0
    · rw [hm0, ite_eq_left (le_refl 0), ite_eq_right (lt_irrefl 0), ite_eq_right (lt_irrefl 0),
          add_zero, Nat.cast_sub (by omega : 1 ≤ K + w)]
      push_cast; ring
    · rw [ite_eq_right (by omega : ¬ v ≤ 0), ite_eq_left (by omega : 0 < v), Nat.add_sub_cancel]
      push_cast; ring

/-! ### Fundamental Bound: `pileTau ≤ r * pileMinSize` -/

private lemma pileTauAux_le_r_mul_minSizeAux {t ell u s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hu_lt : u < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTauAux t ell u s K r ≤ r * (pileMinSizeAux t ell u s K : ℝ) := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have htu_pos : 0 < t - u := by omega
  by_cases hu0 : u = 0
  · rw [hu0, pileMinSizeAux_u0 ht]
    by_cases hs0 : s = 0
    · rw [hs0]; unfold pileTauAux
      simp only [Nat.sub_zero, Nat.zero_le, ↓reduceIte, lt_self_iff_false, Nat.zero_div, add_zero]
      split_ifs with hell0
      · rw [Nat.cast_sub (by omega : 1 ≤ ell)]; push_cast; nlinarith
      · positivity
    · rw [pileTauAux_u0_pos ht (by omega) (by omega)]
      have hceil_le : ceilDiv s t - 1 ≤ s / t := by
        rw [ceilDiv_eq_div_add_ite ht (by omega)]
        split_ifs
        · simp
        · exact Nat.sub_le _ 1
      have h1 : ((ceilDiv s t - 1 : ℕ) : ℝ) ≤ ((s / t : ℕ) : ℝ) := by exact_mod_cast hceil_le
      have h2 : ((s / t : ℕ) : ℝ) ≤ r * ((s / t : ℕ) : ℝ) := by nlinarith
      push_cast; nlinarith
  · unfold pileTauAux pileMinSizeAux
    by_cases hle : s ≤ (t - u) * K
    · rw [ite_eq_left hle, ite_eq_left hle, ite_eq_right hu0]
      by_cases hs0 : s = 0
      · rw [ite_eq_left hs0, ite_eq_left (by omega : 0 < u), ite_eq_left (by omega : s < t - u)]
        linarith
      · rw [ite_eq_right hs0]
        have hs_pos : 0 < s := by omega
        by_cases hlt : s < t - u
        · rw [ite_eq_left hlt]
          have hdiv0 : s / (t - u) = 0 := Nat.div_eq_of_lt hlt
          have hmod : 0 < s % (t - u) := by rw [Nat.mod_eq_of_lt hlt]; exact hs_pos
          have hceil1 : ceilDiv s (t - u) = 1 := by
            rw [ceilDiv_eq_div_add_ite htu_pos hs_pos, hdiv0, ite_eq_left hmod]
          rw [hceil1]; simp; linarith
        · rw [ite_eq_right hlt]
          have hcK : ceilDiv s (t - u) ≤ K := ceilDiv_le_of_le_mul htu_pos hle
          have hcp : 1 ≤ ceilDiv s (t - u) := ceilDiv_pos htu_pos hs_pos
          have h1 : ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
            rw [Nat.cast_sub hcp, Nat.cast_one]
            have : (ceilDiv s (t - u) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcK
            linarith
          push_cast; linarith
    · rw [ite_eq_right hle, ite_eq_right hle, ite_eq_right hu0]
      generalize (s - (t - u) * K) / t = w
      generalize (s - (t - u) * K) % t = v
      have hK_lt_2r : (K : ℝ) < 2 * r := by
        have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
        linarith
      have hw_le : (w : ℝ) ≤ r * (w : ℝ) := by nlinarith
      by_cases hvu : v < u
      · rw [ite_eq_left hvu, ite_eq_left (le_of_lt hvu)]
        split_ifs <;> push_cast <;> nlinarith
      · rw [ite_eq_right hvu]
        split_ifs <;> push_cast <;> nlinarith

lemma pileTau_le_r_mul_minSize {t p s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTau t p s K r ≤ r * (pileMinSize t p s K : ℝ) :=
  pileTauAux_le_r_mul_minSizeAux ht (Nat.mod_lt p ht) hr hK_lo hK_hi

/-! ### Lemma A: Universal `+1` Step Bound -/

private lemma pileTauAux_step_wrap_lt {t ell s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTauAux t (ell + 1) 0 s K r < r * ((pileMinSizeAux t ell (t - 1) s K : ℝ) + 1) := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have htu1 : t - (t - 1) = 1 := by omega
  by_cases hs0 : s = 0
  · rw [hs0]; unfold pileTauAux pileMinSizeAux
    simp only [Nat.sub_zero, Nat.zero_le, ↓reduceIte, lt_self_iff_false, Nat.add_sub_cancel,
      Nat.zero_div, add_zero, htu1, Nat.one_mul]
    rw [ite_eq_left (Nat.succ_pos ell)]
    split_ifs <;> push_cast <;> nlinarith
  · have hs_pos : 0 < s := by omega
    rw [pileTauAux_u0_pos ht hs_pos (by omega)]
    by_cases ht1 : t = 1
    · subst ht1
      rw [Nat.sub_self, pileMinSizeAux_u0 (by omega : 0 < 1), Nat.div_one]
      have hceil_s : ceilDiv s 1 = s := by unfold ceilDiv; simp
      rw [hceil_s, Nat.cast_sub (by omega : 1 ≤ s)]; push_cast
      have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 1 ≤ s)
      nlinarith
    · have ht2 : 2 ≤ t := by omega
      have hu_pos : t - 1 ≠ 0 := by omega
      unfold pileMinSizeAux
      rw [htu1, Nat.one_mul]
      by_cases hsK : s ≤ K
      · rw [ite_eq_left hsK, ite_eq_right hu_pos, ite_eq_right (by omega : ¬ s < 1)]
        have hceil_le : ceilDiv s t ≤ K := by
          have h1 : ceilDiv s t ≤ ceilDiv K t := ceilDiv_mono hsK
          have h2 : ceilDiv K t ≤ K := by
            unfold ceilDiv
            have hle : K + t ≤ t * (K + 1) := by nlinarith
            have hlt : K + t - 1 < t * (K + 1) := by omega
            have := (Nat.div_lt_iff_lt_mul ht).mpr (by rw [Nat.mul_comm]; exact hlt)
            omega
          exact le_trans h1 h2
        have hcp : 1 ≤ ceilDiv s t := ceilDiv_pos ht hs_pos
        have h1 : ((ceilDiv s t - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
          rw [Nat.cast_sub hcp, Nat.cast_one]
          have : (ceilDiv s t : ℝ) ≤ (K : ℝ) := by exact_mod_cast hceil_le
          linarith
        push_cast; nlinarith
      · rw [ite_eq_right hsK, ite_eq_right hu_pos]
        have hs_gt : K < s := by omega
        have hdm' : t * ((s - K) / t) + (s - K) % t = s - K := Nat.div_add_mod (s - K) t
        have hv'_lt : (s - K) % t < t := Nat.mod_lt (s - K) ht
        generalize (s - K) / t = w' at hdm'
        generalize (s - K) % t = v' at hdm' hv'_lt
        have hmin_ge : ell + w' + 1 ≤
            if v' < t - 1 then ell + w' + 1 else ell + w' + 2 := by split_ifs <;> omega
        have hmin_R : (ell : ℝ) + (w' : ℝ) + 1 ≤
            ((if v' < t - 1 then ell + w' + 1 else ell + w' + 2 : ℕ) : ℝ) := by exact_mod_cast hmin_ge
        have hceil_bound : ceilDiv s t - 1 ≤ w' + K - 1 := by
          unfold ceilDiv
          have hs_eq : s = K + t * w' + v' := by omega
          have hlt_aux : K + t * w' + v' + t ≤ t * (w' + K + 1) := by nlinarith
          have hlt : s + t - 1 < t * (w' + K + 1) := by omega
          have hdiv : (s + t - 1) / t < w' + K + 1 :=
            (Nat.div_lt_iff_lt_mul ht).mpr (by rw [Nat.mul_comm]; exact hlt)
          omega
        have hbound_R : ((ceilDiv s t - 1 : ℕ) : ℝ) ≤ (w' : ℝ) + (K : ℝ) - 1 := by
          have h1 : ((ceilDiv s t - 1 : ℕ) : ℝ) ≤ ((w' + K - 1 : ℕ) : ℝ) := by exact_mod_cast hceil_bound
          rw [Nat.cast_sub (by omega : 1 ≤ w' + K), Nat.cast_add, Nat.cast_one] at h1
          exact h1
        have hw'_le : (w' : ℝ) ≤ r * (w' : ℝ) := by nlinarith
        have hrhs : r * ((ell : ℝ) + (w' : ℝ) + 2) ≤
            r * (((if v' < t - 1 then ell + w' + 1 else ell + w' + 2 : ℕ) : ℝ) + 1) := by nlinarith
        have hlhs : ((ell + 1 : ℕ) : ℝ) * r + ((ceilDiv s t - 1 : ℕ) : ℝ) <
            r * ((ell : ℝ) + (w' : ℝ) + 2) := by push_cast; nlinarith
        exact lt_of_lt_of_le hlhs hrhs

private lemma pileTauAux_step_nowrap_over_lt {t ell u s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hu1_lt : u + 1 < t) (hu0 : u ≠ 0)
    (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (hle0 : ¬ s ≤ (t - u) * K) :
    pileTauAux t ell (u + 1) s K r < r * ((pileMinSizeAux t ell u s K : ℝ) + 1) := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have ht3 : 3 ≤ t := by omega
  have hcap_rel : (t - u) * K = (t - (u + 1)) * K + K := by
    have : t - u = (t - (u + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  have hs_gt0 : (t - u) * K < s := by omega
  have hle1 : ¬ s ≤ (t - (u + 1)) * K := by omega
  unfold pileTauAux pileMinSizeAux
  rw [ite_eq_right hle1, ite_eq_right hle0, ite_eq_right hu0]
  have hdm1 : t * ((s - (t - (u + 1)) * K) / t) + (s - (t - (u + 1)) * K) % t = s - (t - (u + 1)) * K :=
    Nat.div_add_mod _ t
  have hv1_lt : (s - (t - (u + 1)) * K) % t < t := Nat.mod_lt _ ht
  have hdm0 : t * ((s - (t - u) * K) / t) + (s - (t - u) * K) % t = s - (t - u) * K :=
    Nat.div_add_mod _ t
  have hv0_lt : (s - (t - u) * K) % t < t := Nat.mod_lt _ ht
  have hdiff_rem : s - (t - (u + 1)) * K = (s - (t - u) * K) + K := by omega
  generalize (s - (t - (u + 1)) * K) / t = w1 at hdm1
  generalize (s - (t - (u + 1)) * K) % t = v1 at hdm1 hv1_lt
  generalize (s - (t - u) * K) / t = w0 at hdm0
  generalize (s - (t - u) * K) % t = v0 at hdm0 hv0_lt
  have hdiff_eq : t * w1 + v1 = t * w0 + v0 + K := by omega
  set M := if v0 < u then ell + w0 + 1 else ell + w0 + 2
  have hmin_ge : ell + w0 + 1 ≤ M := by dsimp only [M]; split_ifs <;> omega
  have hmin_R : (ell : ℝ) + (w0 : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hmin_ge
  have hw0_le : (w0 : ℝ) ≤ r * (w0 : ℝ) := by
    have : (0 : ℝ) ≤ (w0 : ℝ) := Nat.cast_nonneg w0
    nlinarith only [hr, this]
  have hw_le : w0 ≤ w1 := by nlinarith only [hdiff_eq, hv1_lt, ht]
  by_cases hK4 : 4 ≤ K
  · have hw_sub : w0 + (w1 - w0) = w1 := by omega
    have h3diff : 3 * (w1 - w0) ≤ K + 2 := by
      by_cases hd0 : w1 - w0 = 0
      · omega
      · have hsub1 : (w1 - w0 - 1) + 1 = w1 - w0 := by omega
        have hlt : t * (w1 - w0) < K + t := by nlinarith only [hdiff_eq, hv0_lt, hw_sub]
        have hmul : t * (w1 - w0 - 1) + t = t * (w1 - w0) := by
          rw [← Nat.mul_add_one, hsub1]
        have hle_K : t * (w1 - w0 - 1) < K := by omega
        have h3le : 3 * (w1 - w0 - 1) ≤ t * (w1 - w0 - 1) := Nat.mul_le_mul_right _ ht3
        omega
    have h3diff_R : 3 * ((w1 : ℝ) - (w0 : ℝ)) ≤ (K : ℝ) + 2 := by
      have h1 : 3 * ((w1 - w0 : ℕ) : ℝ) ≤ (K : ℝ) + 2 := by exact_mod_cast h3diff
      rw [Nat.cast_sub hw_le] at h1; exact h1
    have hK4_R : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK4
    have hgoal : (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) < r * ((M : ℝ) + 1) := by
      nlinarith only [hmin_R, hw0_le, h3diff_R, hK4_R, hK_lo, hK_hi, hr]
    have htau_le : (if v1 ≤ u + 1 then if 0 < v1 then ((ell + 1 : ℕ) : ℝ) * r + (w1 : ℝ)
        else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) - 1 else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ)) ≤
        (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) := by
      split_ifs <;> (push_cast; linarith only [hK_hi])
    exact lt_of_le_of_lt htau_le hgoal
  · have hK23 : K = 2 ∨ K = 3 := by omega
    rcases hK23 with hK2_eq | hK3_eq
    · have hK2R : (K : ℝ) = 2 := by exact_mod_cast hK2_eq
      have hdw : w1 ≤ w0 + 1 := by nlinarith only [hdiff_eq, hv0_lt, ht3, hK2_eq]
      by_cases heqw : w1 = w0 + 1
      · have hv1_le1 : v1 ≤ 1 := by nlinarith only [hdiff_eq, hv0_lt, heqw, hK2_eq]
        have hw1R : (w1 : ℝ) = (w0 : ℝ) + 1 := by exact_mod_cast heqw
        rw [ite_eq_left (by omega : v1 ≤ u + 1)]
        have htau_le : (if 0 < v1 then ((ell + 1 : ℕ) : ℝ) * r + (w1 : ℝ)
            else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) - 1) ≤ ((ell : ℝ) + 1) * r + (w1 : ℝ) := by
          split_ifs <;> (push_cast; linarith only [hK_lo])
        have hgoal : ((ell : ℝ) + 1) * r + (w1 : ℝ) < r * ((M : ℝ) + 1) := by
          nlinarith only [hmin_R, hw0_le, hw1R, hr]
        exact lt_of_le_of_lt htau_le hgoal
      · have heq0 : w1 = w0 := by omega
        have hw1R : (w1 : ℝ) = (w0 : ℝ) := by exact_mod_cast heq0
        have htau_le : (if v1 ≤ u + 1 then if 0 < v1 then ((ell + 1 : ℕ) : ℝ) * r + (w1 : ℝ)
            else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) - 1 else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ)) ≤
            (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) := by
          split_ifs <;> (push_cast; linarith only [hK_hi])
        have hgoal : (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) < r * ((M : ℝ) + 1) := by
          nlinarith only [hmin_R, hw0_le, hw1R, hK2R, hr]
        exact lt_of_le_of_lt htau_le hgoal
    · have hK3R : (K : ℝ) = 3 := by exact_mod_cast hK3_eq
      have hdw : w1 ≤ w0 + 1 := by nlinarith only [hdiff_eq, hv0_lt, ht3, hK3_eq]
      have hdw_R : (w1 : ℝ) ≤ (w0 : ℝ) + 1 := by exact_mod_cast hdw
      have htau_le : (if v1 ≤ u + 1 then if 0 < v1 then ((ell + 1 : ℕ) : ℝ) * r + (w1 : ℝ)
          else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) - 1 else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ)) ≤
          (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) := by
        split_ifs <;> (push_cast; linarith only [hK_hi])
      have hgoal : (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) < r * ((M : ℝ) + 1) := by
        nlinarith only [hmin_R, hw0_le, hdw_R, hK3R, hK_lo, hr]
      exact lt_of_le_of_lt htau_le hgoal

private lemma pileTauAux_step_nowrap_lt {t ell u s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hu1_lt : u + 1 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTauAux t ell (u + 1) s K r < r * ((pileMinSizeAux t ell u s K : ℝ) + 1) := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have ht2 : 2 ≤ t := by omega
  have htu1_pos : 0 < t - (u + 1) := by omega
  have hcap_rel : (t - u) * K = (t - (u + 1)) * K + K := by
    have : t - u = (t - (u + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  by_cases hle1 : s ≤ (t - (u + 1)) * K
  · have hle0 : s ≤ (t - u) * K := by omega
    unfold pileTauAux pileMinSizeAux
    rw [ite_eq_left hle1, ite_eq_left hle0]
    have htau_lt : (if s = 0 then
          if 0 < u + 1 then (ell : ℝ) * r
          else if 0 < ell then ((ell - 1 : ℕ) : ℝ) * r else 0
        else (ell : ℝ) * r + ((ceilDiv s (t - (u + 1)) - 1 : ℕ) : ℝ)) <
        ((ell : ℝ) + 1) * r := by
      by_cases hs0 : s = 0
      · rw [ite_eq_left hs0, ite_eq_left (Nat.succ_pos u)]; linarith
      · rw [ite_eq_right hs0]
        have hcK : ceilDiv s (t - (u + 1)) ≤ K := ceilDiv_le_of_le_mul htu1_pos hle1
        have hcp : 1 ≤ ceilDiv s (t - (u + 1)) := ceilDiv_pos htu1_pos (by omega)
        have hR : ((ceilDiv s (t - (u + 1)) - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
          rw [Nat.cast_sub hcp, Nat.cast_one]
          have : (ceilDiv s (t - (u + 1)) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcK
          linarith
        linarith
    have hmin_ge : ell ≤ if u = 0 then ell + s / t else if s < t - u then ell else ell + 1 := by
      split_ifs
      · exact Nat.le_add_right _ _
      · exact le_refl _
      · omega
    have hmin_R : (ell : ℝ) ≤
        ((if u = 0 then ell + s / t else if s < t - u then ell else ell + 1 : ℕ) : ℝ) := by
      exact_mod_cast hmin_ge
    nlinarith
  · by_cases hu0 : u = 0
    · subst hu0
      have hs_gt1 : (t - 1) * K < s := by rw [zero_add] at hle1; omega
      have hdm1 : t * ((s - (t - 1) * K) / t) + (s - (t - 1) * K) % t = s - (t - 1) * K :=
        Nat.div_add_mod _ t
      have hv1_lt : (s - (t - 1) * K) % t < t := Nat.mod_lt _ ht
      rw [pileMinSizeAux_u0 ht]
      unfold pileTauAux
      rw [zero_add, ite_eq_right (by omega : ¬ s ≤ (t - 1) * K)]
      generalize (s - (t - 1) * K) / t = w1 at hdm1
      generalize (s - (t - 1) * K) % t = v1 at hdm1 hv1_lt
      have hs_div_ge : w1 + 1 ≤ s / t := by
        have ht_sub : (t - 1) + 1 = t := by omega
        have hs_eq : (t - 1) * K + t * w1 + v1 = s := by omega
        have h1 : t * (w1 + 1) ≤ s := by nlinarith
        exact (Nat.le_div_iff_mul_le ht).mpr (by rw [Nat.mul_comm]; exact h1)
      have hs_div_R : (w1 : ℝ) + 1 ≤ ((s / t : ℕ) : ℝ) := by exact_mod_cast hs_div_ge
      have hw1_le : (w1 : ℝ) ≤ r * (w1 : ℝ) := by nlinarith
      have hK_lt_2r : (K : ℝ) < 2 * r := by
        have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
        linarith
      split_ifs <;> push_cast <;> nlinarith
    · by_cases hle0 : s ≤ (t - u) * K
      · have ht3 : 3 ≤ t := by omega
        have hs_gt1 : (t - (u + 1)) * K < s := by omega
        have hdm1 : t * ((s - (t - (u + 1)) * K) / t) + (s - (t - (u + 1)) * K) % t = s - (t - (u + 1)) * K :=
          Nat.div_add_mod _ t
        have hv1_lt : (s - (t - (u + 1)) * K) % t < t := Nat.mod_lt _ ht
        unfold pileTauAux pileMinSizeAux
        rw [ite_eq_right hle1, ite_eq_left hle0, ite_eq_right hu0]
        have hs_ge_tu : ¬ s < t - u := by
          have : 2 * (t - (u + 1)) ≤ (t - (u + 1)) * K := by nlinarith
          omega
        rw [ite_eq_right hs_ge_tu]
        have hrem1_le_K : s - (t - (u + 1)) * K ≤ K := by omega
        generalize (s - (t - (u + 1)) * K) / t = w1 at hdm1
        generalize (s - (t - (u + 1)) * K) % t = v1 at hdm1 hv1_lt
        by_cases hK4 : 4 ≤ K
        · have hw1_3 : 3 * w1 ≤ K := by nlinarith
          have hw1_R : 3 * (w1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hw1_3
          have hK4_R : (4 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK4
          split_ifs <;> push_cast <;> nlinarith
        · have hK23 : K = 2 ∨ K = 3 := by omega
          rcases hK23 with hK2_eq | hK3_eq
          · have hw1_0 : w1 = 0 := by nlinarith
            have hw1R : (w1 : ℝ) = 0 := by exact_mod_cast hw1_0
            have hK2R : (K : ℝ) = 2 := by exact_mod_cast hK2_eq
            split_ifs <;> push_cast <;> nlinarith
          · have hcases : w1 = 0 ∨ (w1 = 1 ∧ v1 = 0) := by
              by_cases hw0 : w1 = 0
              · left; exact hw0
              · right
                have hw1_ge1 : 1 ≤ w1 := by omega
                have hrem_eq : t * w1 + v1 ≤ 3 := by omega
                constructor
                · nlinarith only [ht3, hrem_eq, hw1_ge1]
                · nlinarith only [ht3, hrem_eq, hw1_ge1]
            have hK3R : (K : ℝ) = 3 := by exact_mod_cast hK3_eq
            rcases hcases with hw0 | ⟨hw1_1, hv1_0⟩
            · have hw1R : (w1 : ℝ) = 0 := by exact_mod_cast hw0
              split_ifs <;> (push_cast; linarith only [hw1R, hK3R, hK_lo, hK_hi, hr])
            · rw [ite_eq_left (by omega : v1 ≤ u + 1), ite_eq_right (by omega : ¬ 0 < v1)]
              have hw1R : (w1 : ℝ) = 1 := by exact_mod_cast hw1_1
              push_cast; linarith only [hw1R, hK3R, hK_lo, hK_hi, hr]
      · exact pileTauAux_step_nowrap_over_lt ht hu1_lt hu0 hr hK_lo hK_hi hle0

/-- **Lemma A (Universal `+1` Step Bound)**: for every `t ≥ 1, p, s ≥ 0, r > 1`,
`pileTau t (p + 1) s K r < r * (pileMinSize t p s K + 1)`. -/
lemma pileTau_step_lt {t p s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTau t (p + 1) s K r < r * ((pileMinSize t p s K : ℝ) + 1) := by
  have hu_lt : p % t < t := Nat.mod_lt p ht
  unfold pileTau pileMinSize
  by_cases hwrap : p % t + 1 = t
  · have hdm := div_mod_succ_of_eq ht hwrap
    have hu_eq : p % t = t - 1 := by omega
    rw [hdm.1, hdm.2, hu_eq]
    exact pileTauAux_step_wrap_lt ht hr hK_lo hK_hi
  · have hdm := div_mod_succ_of_lt ht (show p % t + 1 < t by omega)
    rw [hdm.1, hdm.2]
    exact pileTauAux_step_nowrap_lt ht (show p % t + 1 < t by omega) hr hK_lo hK_hi

/-- **Tight Lemma A**: when `s = 0`, `t = 1`, or `p % t = 0`, we even have
`pileTau t (p + 1) s K r ≤ r * pileMinSize t p s K`. -/
lemma pileTau_step_le_tight {t p s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (hcond : s = 0 ∨ t = 1 ∨ p % t = 0) :
    pileTau t (p + 1) s K r ≤ r * (pileMinSize t p s K : ℝ) := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have ht1_case : t = 1 → pileTau t (p + 1) s K r ≤ r * (pileMinSize t p s K : ℝ) := by
    intro ht1
    subst ht1
    unfold pileTau pileMinSize
    simp only [Nat.div_one, Nat.mod_one]
    rw [pileMinSizeAux_u0 (by omega : 0 < 1), Nat.div_one]
    by_cases hs0 : s = 0
    · rw [hs0]; unfold pileTauAux
      simp only [Nat.sub_zero, Nat.zero_le, ↓reduceIte, lt_self_iff_false, Nat.add_sub_cancel, add_zero]
      rw [ite_eq_left (Nat.succ_pos p)]; linarith
    · rw [pileTauAux_u0_pos (by omega : 0 < 1) (by omega) (by omega)]
      have hc1 : ceilDiv s 1 = s := by unfold ceilDiv; simp
      rw [hc1, Nat.cast_sub (by omega : 1 ≤ s)]; push_cast
      have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 1 ≤ s)
      nlinarith
  have hu_lt : p % t < t := Nat.mod_lt p ht
  rcases hcond with hs0 | ht1 | hu0
  · subst hs0
    unfold pileTau pileMinSize
    by_cases hwrap : p % t + 1 = t
    · have hdm := div_mod_succ_of_eq ht hwrap
      rw [hdm.1, hdm.2]; unfold pileTauAux pileMinSizeAux
      simp only [Nat.zero_le, ↓reduceIte, lt_self_iff_false, Nat.zero_div, add_zero,
        Nat.add_sub_cancel]
      rw [ite_eq_left (Nat.succ_pos (p / t))]
      split_ifs <;> push_cast <;> nlinarith
    · have hdm := div_mod_succ_of_lt ht (show p % t + 1 < t by omega)
      rw [hdm.1, hdm.2]; unfold pileTauAux pileMinSizeAux
      simp only [Nat.zero_le, ↓reduceIte, Nat.zero_div, add_zero]
      rw [ite_eq_left (Nat.succ_pos (p % t))]
      split_ifs <;> push_cast <;> nlinarith
  · exact ht1_case ht1
  · by_cases ht1 : t = 1
    · exact ht1_case ht1
    · have ht2 : 2 ≤ t := by omega
      have hdm := div_mod_succ_of_lt ht (by omega : p % t + 1 < t)
      have htu1_pos : 0 < t - 1 := by omega
      unfold pileTau pileMinSize
      rw [hdm.1, hdm.2, hu0, zero_add, pileMinSizeAux_u0 ht]
      generalize p / t = ell
      unfold pileTauAux
      by_cases hle1 : s ≤ (t - 1) * K
      · rw [ite_eq_left hle1]
        by_cases hs0 : s = 0
        · simp [hs0]; linarith
        · rw [ite_eq_right hs0]
          have hs_pos : 0 < s := by omega
          by_cases hst : s < t
          · have hc1 : ceilDiv s (t - 1) = 1 := by
              have h1 := ceilDiv_pos htu1_pos hs_pos
              have h2 := ceilDiv_le_of_le_mul htu1_pos (by omega : s ≤ (t - 1) * 1)
              omega
            rw [hc1]; simp; nlinarith
          · have hq1 : 1 ≤ s / t := (Nat.le_div_iff_mul_le ht).mpr (by omega)
            have hcK : ceilDiv s (t - 1) ≤ K := ceilDiv_le_of_le_mul htu1_pos hle1
            have hcp : 1 ≤ ceilDiv s (t - 1) := ceilDiv_pos htu1_pos hs_pos
            have hR : ((ceilDiv s (t - 1) - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
              rw [Nat.cast_sub hcp, Nat.cast_one]
              have : (ceilDiv s (t - 1) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcK
              linarith
            have hqR : (1 : ℝ) ≤ ((s / t : ℕ) : ℝ) := by exact_mod_cast hq1
            push_cast; nlinarith
      · rw [ite_eq_right hle1]
        have hs_gt1 : (t - 1) * K < s := by omega
        have hdm1 : t * ((s - (t - 1) * K) / t) + (s - (t - 1) * K) % t = s - (t - 1) * K :=
          Nat.div_add_mod _ t
        have hv1_lt : (s - (t - 1) * K) % t < t := Nat.mod_lt _ ht
        generalize (s - (t - 1) * K) / t = w1 at hdm1
        generalize (s - (t - 1) * K) % t = v1 at hdm1 hv1_lt
        have hw1_le : (w1 : ℝ) ≤ r * (w1 : ℝ) := by nlinarith
        have hs_eq : s = (t - 1) * K + t * w1 + v1 := by omega
        have ht_sub : (t - 1) + 1 = t := by omega
        by_cases hK4 : 4 ≤ K
        · have hq2 : w1 + 2 ≤ s / t := by
            have : t * (w1 + 2) ≤ s := by nlinarith
            exact (Nat.le_div_iff_mul_le ht).mpr (by rw [Nat.mul_comm]; exact this)
          have hq2R : (w1 : ℝ) + 2 ≤ ((s / t : ℕ) : ℝ) := by exact_mod_cast hq2
          have hK_lt_2r : (K : ℝ) < 2 * r := by
            have : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
            linarith
          split_ifs <;> push_cast <;> nlinarith
        · have hK23 : K = 2 ∨ K = 3 := by omega
          rcases hK23 with hK2_eq | hK3_eq
          · have hK2R : (K : ℝ) = 2 := by exact_mod_cast hK2_eq
            by_cases hv1 : v1 ≤ 1
            · rw [ite_eq_left hv1]
              have hq1 : w1 + 1 ≤ s / t := by
                have : t * (w1 + 1) ≤ s := by nlinarith
                exact (Nat.le_div_iff_mul_le ht).mpr (by rw [Nat.mul_comm]; exact this)
              have hq1R : (w1 : ℝ) + 1 ≤ ((s / t : ℕ) : ℝ) := by exact_mod_cast hq1
              split_ifs <;> push_cast <;> nlinarith
            · rw [ite_eq_right hv1]
              have hq2 : w1 + 2 ≤ s / t := by
                have : t * (w1 + 2) ≤ s := by nlinarith
                exact (Nat.le_div_iff_mul_le ht).mpr (by rw [Nat.mul_comm]; exact this)
              have hq2R : (w1 : ℝ) + 2 ≤ ((s / t : ℕ) : ℝ) := by exact_mod_cast hq2
              push_cast; nlinarith
          · have hK3R : (K : ℝ) = 3 := by exact_mod_cast hK3_eq
            by_cases ht2_eq : t = 2
            · subst ht2_eq
              rw [ite_eq_left (by omega : v1 ≤ 1)]
              by_cases hv1_0 : v1 = 0
              · rw [ite_eq_right (by omega : ¬ 0 < v1)]
                have hq1 : w1 + 1 ≤ s / 2 := by
                  have : 2 * (w1 + 1) ≤ s := by omega
                  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact this)
                have hq1R : (w1 : ℝ) + 1 ≤ ((s / 2 : ℕ) : ℝ) := by exact_mod_cast hq1
                push_cast; nlinarith
              · rw [ite_eq_left (by omega : 0 < v1)]
                have hq2 : w1 + 2 ≤ s / 2 := by
                  have : 2 * (w1 + 2) ≤ s := by omega
                  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact this)
                have hq2R : (w1 : ℝ) + 2 ≤ ((s / 2 : ℕ) : ℝ) := by exact_mod_cast hq2
                push_cast; nlinarith
            · have ht3 : 3 ≤ t := by omega
              have hq2 : w1 + 2 ≤ s / t := by
                have : t * (w1 + 2) ≤ s := by nlinarith
                exact (Nat.le_div_iff_mul_le ht).mpr (by rw [Nat.mul_comm]; exact this)
              have hq2R : (w1 : ℝ) + 2 ≤ ((s / t : ℕ) : ℝ) := by exact_mod_cast hq2
              split_ifs <;> (push_cast; nlinarith only [hq2R, hK3R, hK_lo, hK_hi, hw1_le, hr])

/-! ### Monotonicity of `pileTau` in `s` -/

private lemma pileTauAux_step_s {t ell u s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hu_lt : u < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTauAux t ell u s K r ≤ pileTauAux t ell u (s + 1) K r := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have htu_pos : 0 < t - u := by omega
  unfold pileTauAux
  by_cases h1 : s + 1 ≤ (t - u) * K
  · have h0 : s ≤ (t - u) * K := by omega
    rw [ite_eq_left h0, ite_eq_left h1, ite_eq_right (Nat.succ_ne_zero s)]
    by_cases hs0 : s = 0
    · rw [ite_eq_left hs0]
      have hnn : (0 : ℝ) ≤ ((ceilDiv (s + 1) (t - u) - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      split_ifs with hu0 hell0
      · linarith
      · rw [Nat.cast_sub (by omega : 1 ≤ ell)]; push_cast; nlinarith
      · positivity
    · rw [ite_eq_right hs0]
      have hm : ceilDiv s (t - u) - 1 ≤ ceilDiv (s + 1) (t - u) - 1 :=
        Nat.sub_le_sub_right (ceilDiv_mono (by omega)) 1
      have hmR : ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ ((ceilDiv (s + 1) (t - u) - 1 : ℕ) : ℝ) := by
        exact_mod_cast hm
      linarith
  · rw [ite_eq_right h1]
    by_cases h0 : s ≤ (t - u) * K
    · rw [ite_eq_left h0]
      have hrem1 : s + 1 - (t - u) * K = 1 := by omega
      rw [hrem1]
      have hlhs : (if s = 0 then
            if 0 < u then (ell : ℝ) * r
            else if 0 < ell then ((ell - 1 : ℕ) : ℝ) * r else 0
          else (ell : ℝ) * r + ((ceilDiv s (t - u) - 1 : ℕ) : ℝ)) ≤
          (ell : ℝ) * r + (K : ℝ) - 1 := by
        split_ifs with hs0 hu0 hell0
        · linarith
        · rw [Nat.cast_sub (by omega : 1 ≤ ell)]; push_cast; nlinarith
        · have : (0 : ℝ) ≤ (ell : ℝ) * r := by positivity
          linarith
        · have hcK : ceilDiv s (t - u) ≤ K := ceilDiv_le_of_le_mul htu_pos h0
          have hcp : 1 ≤ ceilDiv s (t - u) := ceilDiv_pos htu_pos (by omega)
          have hR : ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
            rw [Nat.cast_sub hcp, Nat.cast_one]
            have : (ceilDiv s (t - u) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcK
            linarith
          linarith
      have hrhs : (ell : ℝ) * r + (K : ℝ) - 1 ≤
          if 1 % t ≤ u then
            if 0 < 1 % t then ((ell + 1 : ℕ) : ℝ) * r + ((1 / t : ℕ) : ℝ)
            else (ell : ℝ) * r + (K : ℝ) + ((1 / t : ℕ) : ℝ) - 1
          else (ell : ℝ) * r + (K : ℝ) + ((1 / t : ℕ) : ℝ) := by
        have hnn : (0 : ℝ) ≤ ((1 / t : ℕ) : ℝ) := Nat.cast_nonneg _
        split_ifs <;> push_cast <;> linarith
      exact le_trans hlhs hrhs
    · rw [ite_eq_right h0]
      have hrem_eq : s + 1 - (t - u) * K = (s - (t - u) * K) + 1 := by omega
      rw [hrem_eq]
      generalize s - (t - u) * K = rem
      have hv_lt : rem % t < t := Nat.mod_lt rem ht
      by_cases hwrap : rem % t + 1 = t
      · have hdm := div_mod_succ_of_eq ht hwrap
        rw [hdm.1, hdm.2, ite_eq_left (Nat.zero_le u), ite_eq_right (lt_irrefl 0)]
        generalize rem / t = w
        generalize rem % t = v
        split_ifs <;> push_cast <;> linarith
      · have hdm := div_mod_succ_of_lt ht (show rem % t + 1 < t by omega)
        rw [hdm.1, hdm.2]
        generalize rem / t = w
        generalize rem % t = v
        split_ifs <;> push_cast <;> linarith

lemma pileTau_mono_s {t p s₁ s₂ K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (hle : s₁ ≤ s₂) :
    pileTau t p s₁ K r ≤ pileTau t p s₂ K r := by
  induction hle with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (pileTauAux_step_s ht (Nat.mod_lt p ht) hr hK_lo hK_hi)

/-! ### Lemma B: Zero-Drop Lemma -/

private lemma pileMinSizeAux_sub_one_ge {t ell u s K Mstar : ℕ} {r : ℝ}
    (ht : 0 < t) (hu_lt : u < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (hs : 1 ≤ s) (hgt : r * (Mstar : ℝ) < pileTauAux t ell u s K r) :
    Mstar + 1 ≤ pileMinSizeAux t ell u (s - 1) K := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have htu_pos : 0 < t - u := by omega
  have hfund := pileTauAux_le_r_mul_minSizeAux (t := t) (ell := ell) (u := u) (s := s) (K := K) ht hu_lt hr hK_lo hK_hi
  have hlt_min : (Mstar : ℝ) < (pileMinSizeAux t ell u s K : ℝ) := by nlinarith
  have hM_le : Mstar + 1 ≤ pileMinSizeAux t ell u s K := by
    have : Mstar < pileMinSizeAux t ell u s K := by exact_mod_cast hlt_min
    omega
  by_contra hcontra
  have hM_eq : pileMinSizeAux t ell u (s - 1) K ≤ Mstar := by omega
  by_cases hu0 : u = 0
  · subst hu0
    rw [pileMinSizeAux_u0 ht] at hM_le hM_eq
    have hdiv_step : (s - 1) / t < s / t := by omega
    have hs_mod : s % t = 0 := by
      have h1 : t * (s / t) + s % t = s := Nat.div_add_mod s t
      have hmlt := Nat.mod_lt s ht
      by_contra hne
      have h3 : s - 1 = t * (s / t) + (s % t - 1) := by omega
      have hsame : (s - 1) / t = s / t := by
        rw [h3, Nat.mul_add_div ht, Nat.div_eq_of_lt (show s % t - 1 < t by omega), add_zero]
      omega
    have hq_pos : 1 ≤ s / t := by
      have h1 : t * (s / t) + s % t = s := Nat.div_add_mod s t
      rw [hs_mod, add_zero] at h1
      by_contra h0
      have hq : s / t = 0 := Nat.eq_zero_of_not_pos (fun h => h0 h)
      rw [hq] at h1; simp at h1; omega
    have hdiv_sub : (s - 1) / t = s / t - 1 := by
      have h1 : t * (s / t) + s % t = s := Nat.div_add_mod s t
      rw [hs_mod, add_zero] at h1
      have hmul : t * (s / t - 1) + t = t * (s / t) := by
        have := Nat.mul_add_one t (s / t - 1)
        have h2 : s / t - 1 + 1 = s / t := by omega
        rw [h2] at this; exact this.symm
      have h3 : s - 1 = t * (s / t - 1) + (t - 1) := by omega
      rw [h3, Nat.mul_add_div ht, Nat.div_eq_of_lt (show t - 1 < t by omega), add_zero]
    have hMstar_ge : ell + (s / t - 1) ≤ Mstar := by omega
    rw [pileTauAux_u0_pos ht (by omega) (by omega), ceilDiv_eq_div_add_ite ht (by omega), hs_mod] at hgt
    simp only [lt_self_iff_false, ↓reduceIte, add_zero] at hgt
    have hMR : (ell : ℝ) + ((s / t - 1 : ℕ) : ℝ) ≤ (Mstar : ℝ) := by exact_mod_cast hMstar_ge
    nlinarith
  · unfold pileMinSizeAux at hM_le hM_eq
    unfold pileTauAux at hgt
    by_cases hle : s ≤ (t - u) * K
    · have hle_p : s - 1 ≤ (t - u) * K := by omega
      rw [ite_eq_left hle, ite_eq_right hu0] at hM_le
      rw [ite_eq_left hle_p, ite_eq_right hu0] at hM_eq
      rw [ite_eq_left hle, ite_eq_right (by omega : s ≠ 0)] at hgt
      by_cases hlt : s < t - u
      · rw [ite_eq_left hlt] at hM_le
        rw [ite_eq_left (by omega : s - 1 < t - u)] at hM_eq; omega
      · rw [ite_eq_right hlt] at hM_le
        by_cases hlt_p : s - 1 < t - u
        · rw [ite_eq_left hlt_p] at hM_eq
          have hc1 : ceilDiv s (t - u) = 1 := by
            have h1 := ceilDiv_pos htu_pos (by omega : 0 < s)
            have h2 := ceilDiv_le_of_le_mul htu_pos (by omega : s ≤ (t - u) * 1)
            omega
          rw [hc1] at hgt
          simp only [Nat.sub_self, Nat.cast_zero, add_zero] at hgt
          have hMR : (ell : ℝ) ≤ (Mstar : ℝ) := by exact_mod_cast hM_eq
          nlinarith
        · rw [ite_eq_right hlt_p] at hM_eq; omega
    · rw [ite_eq_right hle, ite_eq_right hu0] at hM_le
      rw [ite_eq_right hle] at hgt
      by_cases hbd : s - 1 ≤ (t - u) * K
      · rw [ite_eq_left hbd, ite_eq_right hu0] at hM_eq
        have hrem1 : s - (t - u) * K = 1 := by omega
        have hs1_eq : s - 1 = (t - u) * K := by omega
        have hcap_ge : ¬ s - 1 < t - u := by
          have : t - u ≤ (t - u) * K := by nlinarith
          omega
        rw [ite_eq_right hcap_ge] at hM_eq
        rw [hrem1, Nat.div_eq_of_lt (by omega : 1 < t), Nat.mod_eq_of_lt (by omega : 1 < t)] at hgt
        rw [ite_eq_left (by omega : 1 ≤ u), ite_eq_left (by omega : 0 < 1)] at hgt
        have hMR : (ell : ℝ) + 1 ≤ (Mstar : ℝ) := by exact_mod_cast hM_eq
        push_cast at hgt; nlinarith
      · rw [ite_eq_right hbd, ite_eq_right hu0] at hM_eq
        have hrem_eq : s - (t - u) * K = (s - 1 - (t - u) * K) + 1 := by omega
        rw [hrem_eq] at hM_le hgt
        generalize s - 1 - (t - u) * K = rem' at hM_le hM_eq hgt
        have hv'_lt : rem' % t < t := Nat.mod_lt rem' ht
        by_cases hwrap : rem' % t + 1 = t
        · have hdm := div_mod_succ_of_eq ht hwrap
          rw [hdm.1, hdm.2, ite_eq_left (by omega : 0 < u)] at hM_le
          rw [ite_eq_right (by omega : ¬ rem' % t < u)] at hM_eq
          omega
        · have hdm := div_mod_succ_of_lt ht (show rem' % t + 1 < t by omega)
          rw [hdm.1, hdm.2] at hM_le hgt
          generalize rem' / t = w' at hM_le hM_eq hgt
          generalize rem' % t = v' at hM_le hM_eq hgt
          by_cases hvu : v' + 1 < u
          · rw [ite_eq_left hvu] at hM_le
            rw [ite_eq_left (by omega : v' < u)] at hM_eq; omega
          · rw [ite_eq_right hvu] at hM_le
            by_cases hv'u : v' < u
            · rw [ite_eq_left hv'u] at hM_eq
              rw [ite_eq_left (by omega : v' + 1 ≤ u), ite_eq_left (Nat.succ_pos v')] at hgt
              have hMR : (ell : ℝ) + (w' : ℝ) + 1 ≤ (Mstar : ℝ) := by exact_mod_cast hM_eq
              have hw'_le : (w' : ℝ) ≤ r * (w' : ℝ) := by nlinarith
              push_cast at hgt; nlinarith
            · rw [ite_eq_right hv'u] at hM_eq; omega

/-- **Lemma B (Zero-Drop Lemma)**: if `r * Mstar < pileTau t p s K r` and `1 ≤ s`, then
`Mstar + 1 ≤ pileMinSize t p (s - 1) K`. -/
lemma pileMinSize_sub_one_ge {t p s K Mstar : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (hs : 1 ≤ s) (hgt : r * (Mstar : ℝ) < pileTau t p s K r) :
    Mstar + 1 ≤ pileMinSize t p (s - 1) K :=
  pileMinSizeAux_sub_one_ge ht (Nat.mod_lt p ht) hr hK_lo hK_hi hs hgt

/-! ### Lemma C: Single-Pile Impossibility Lemma -/

private lemma pileTauAux_sub_one_le_of_maxLargeSize {t ell u s K Mstar : ℕ} {r : ℝ}
    (ht : 0 < t) (hu_lt : u < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (hs : 1 ≤ s) (hM : 1 ≤ Mstar)
    (hLmax :
      let idx : Fin t := if 0 < u ∧ 0 < ell ∧ 0 < s ∧ s ≤ (t - u) * K then ⟨u, hu_lt⟩ else ⟨0, ht⟩
      pileLargeAux t ell u idx + pileSmallAux t u s K idx ≤ Mstar + 1) :
    pileTauAux t ell u (s - 1) K r ≤ r * (Mstar : ℝ) + 1 := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have hmono : pileTauAux t ell u (s - 1) K r ≤ pileTauAux t ell u s K r := by
    have hs_eq : (s - 1) + 1 = s := by omega
    conv_rhs => rw [← hs_eq]
    exact pileTauAux_step_s ht hu_lt hr hK_lo hK_hi
  have htu_pos : 0 < t - u := by omega
  dsimp only at hLmax
  by_cases hu0 : u = 0
  · subst hu0
    simp only [lt_self_iff_false, false_and, ↓reduceIte, Nat.sub_zero] at hLmax
    have hL0 : pileLargeAux t ell 0 ⟨0, ht⟩ = ell := by unfold pileLargeAux; simp
    have hS0 : pileSmallAux t 0 s K ⟨0, ht⟩ = ceilDiv s t := by
      rw [ceilDiv_eq_div_add_ite ht (by omega : 0 < s)]
      unfold pileSmallAux; simp only [Nat.sub_zero, Nat.not_lt_zero, ↓reduceIte]
      by_cases hle : s ≤ t * K
      · rw [ite_eq_left hle]
      · rw [ite_eq_right hle]
        have hs_eq : s = t * K + (s - t * K) := by omega
        have hdm := add_mul_div_mod (K := K) (rem := s - t * K) ht
        have hdiv : s / t = K + (s - t * K) / t := by conv_lhs => rw [hs_eq]; exact hdm.1
        have hmod : s % t = (s - t * K) % t := by conv_lhs => rw [hs_eq]; exact hdm.2
        rw [hdiv, hmod]
        generalize (s - t * K) / t = w; generalize (s - t * K) % t = v
        by_cases hm0 : v = 0
        · rw [hm0]; simp
        · rw [ite_eq_right (by omega : ¬ v ≤ 0), ite_eq_left (by omega : 0 < v)]
    rw [hL0, hS0] at hLmax
    have hcp : 1 ≤ ceilDiv s t := ceilDiv_pos ht (by omega)
    have htau_eq : pileTauAux t ell 0 s K r = (ell : ℝ) * r + ((ceilDiv s t - 1 : ℕ) : ℝ) :=
      pileTauAux_u0_pos ht (by omega) (by omega)
    have hMR : (ell : ℝ) + ((ceilDiv s t - 1 : ℕ) : ℝ) ≤ (Mstar : ℝ) := by
      have : ell + (ceilDiv s t - 1) ≤ Mstar := by omega
      exact_mod_cast this
    have hc_le : ((ceilDiv s t - 1 : ℕ) : ℝ) ≤ r * ((ceilDiv s t - 1 : ℕ) : ℝ) := by nlinarith
    nlinarith
  · have hu_pos : 0 < u := by omega
    by_cases hle : s ≤ (t - u) * K
    · by_cases hell0 : ell = 0
      · subst hell0
        have htau_lt : pileTauAux t 0 u s K r < r := by
          unfold pileTauAux
          rw [ite_eq_left hle, ite_eq_right (by omega : s ≠ 0)]
          have hcK : ceilDiv s (t - u) ≤ K := ceilDiv_le_of_le_mul htu_pos hle
          have hcp : 1 ≤ ceilDiv s (t - u) := ceilDiv_pos htu_pos (by omega)
          have hR : ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
            rw [Nat.cast_sub hcp, Nat.cast_one]
            have : (ceilDiv s (t - u) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcK
            linarith
          simp only [Nat.cast_zero, zero_mul, zero_add]; linarith
        have hM1R : (1 : ℝ) ≤ (Mstar : ℝ) := by exact_mod_cast hM
        nlinarith
      · have hell_pos : 0 < ell := by omega
        rw [ite_eq_left ⟨hu_pos, hell_pos, by omega, hle⟩] at hLmax
        have hLu : pileLargeAux t ell u ⟨u, hu_lt⟩ = ell := by unfold pileLargeAux; simp
        have hSu : pileSmallAux t u s K ⟨u, hu_lt⟩ = ceilDiv s (t - u) := by
          rw [ceilDiv_eq_div_add_ite htu_pos (by omega : 0 < s)]
          unfold pileSmallAux; rw [ite_eq_left hle]; simp
        rw [hLu, hSu] at hLmax
        have hcp : 1 ≤ ceilDiv s (t - u) := ceilDiv_pos htu_pos (by omega)
        have htau_eq : pileTauAux t ell u s K r = (ell : ℝ) * r + ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) := by
          unfold pileTauAux; rw [ite_eq_left hle, ite_eq_right (by omega : s ≠ 0)]
        have hMR : (ell : ℝ) + ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ (Mstar : ℝ) := by
          have : ell + (ceilDiv s (t - u) - 1) ≤ Mstar := by omega
          exact_mod_cast this
        have hc_le : ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ r * ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) := by nlinarith
        nlinarith
    · rw [ite_eq_right (by intro h; exact absurd h.2.2.2 hle)] at hLmax
      have hL0 : pileLargeAux t ell u ⟨0, ht⟩ = ell + 1 := by unfold pileLargeAux; simp [hu_pos]
      rw [hL0] at hLmax
      have hrem_pos : 0 < s - (t - u) * K := by omega
      have hdm : t * ((s - (t - u) * K) / t) + (s - (t - u) * K) % t = s - (t - u) * K :=
        Nat.div_add_mod _ t
      unfold pileSmallAux at hLmax
      rw [ite_eq_right hle] at hLmax
      have htau_le_case : pileTauAux t ell u s K r ≤ r * (Mstar : ℝ) + 1 := by
        unfold pileTauAux
        rw [ite_eq_right hle]
        generalize (s - (t - u) * K) / t = w at hdm hLmax
        generalize (s - (t - u) * K) % t = v at hdm hLmax
        by_cases hv0 : v = 0
        · subst hv0
          rw [ite_eq_left (Nat.zero_le u), ite_eq_left hu_pos] at hLmax
          simp only [Nat.not_lt_zero, ↓reduceIte, add_zero] at hLmax
          rw [ite_eq_left (Nat.zero_le u), ite_eq_right (lt_irrefl 0)]
          have hw_pos : 1 ≤ w := by
            rw [add_zero] at hdm
            by_contra h0
            have hw : w = 0 := Nat.eq_zero_of_not_pos (fun h => h0 h)
            rw [hw] at hdm; simp at hdm; omega
          have hMR : (ell : ℝ) + (w : ℝ) ≤ (Mstar : ℝ) := by
            have : ell + w ≤ Mstar := by omega
            exact_mod_cast this
          have hw1_le : ((w : ℝ) - 1) ≤ r * ((w : ℝ) - 1) := by
            have : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw_pos
            nlinarith
          nlinarith
        · have hv_pos : 0 < v := by omega
          have hS0 : (if v ≤ u then if (0 : ℕ) < u then w + if (0 : ℕ) < v then 1 else 0 else K + w
              else if (0 : ℕ) < u then w + 1 else K + w + if (0 : ℕ) - u < v - u then 1 else 0) = w + 1 := by
            split_ifs <;> omega
          rw [hS0] at hLmax
          have hMR : (ell : ℝ) + (w : ℝ) + 1 ≤ (Mstar : ℝ) := by
            have : ell + w + 1 ≤ Mstar := by omega
            exact_mod_cast this
          have hw_le : (w : ℝ) ≤ r * (w : ℝ) := by nlinarith
          split_ifs <;> push_cast <;> nlinarith
      exact le_trans hmono htau_le_case

/-- **Lemma C (Single-Pile Impossibility)**: for any single pile with `s ≥ 1, Mstar ≥ 1`, if
`maxLargeSize t p s K ht ≤ Mstar + 1`, then `pileTau t p (s - 1) K r ≤ r * Mstar + 1`. -/
lemma pileTau_sub_one_le_of_maxLargeSize {t p s K Mstar : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ))
    (hs : 1 ≤ s) (hM : 1 ≤ Mstar)
    (hLmax : maxLargeSize t p s K ht ≤ Mstar + 1) :
    pileTau t p (s - 1) K r ≤ r * (Mstar : ℝ) + 1 :=
  pileTauAux_sub_one_le_of_maxLargeSize ht (Nat.mod_lt p ht) hr hK_lo hK_hi hs hM hLmax

/-! ### Phase 1 / Phase 3 No-Jump Bound -/

private lemma phase1_bundle_lower_bound_wrap {t ell c K₂ q : ℕ} {r₁ r₂ : ℝ}
    (ht : 0 < t) (hr₁ : 1 < r₁) (hr₂ : 1 < r₂)
    (hK₂_lo : (K₂ : ℝ) - 1 < r₂) (hK₂_hi : r₂ ≤ (K₂ : ℝ))
    (hgt : (q : ℝ) * r₂ < pileTauAux t (ell + 1) 0 c K₂ r₂) (i : Fin t) :
    (q : ℝ) ≤ (pileLargeAux t ell (t - 1) i : ℝ) + (pileSmallAux t (t - 1) c K₂ i : ℝ) * r₁ := by
  have hK2 : 2 ≤ K₂ := by
    have : (1 : ℝ) < (K₂ : ℝ) := lt_of_lt_of_le hr₂ hK₂_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K₂)
  by_cases hq_le_ell : q ≤ ell
  · have hLi : ell ≤ pileLargeAux t ell (t - 1) i := by unfold pileLargeAux; split_ifs <;> omega
    have h1 : (q : ℝ) ≤ (pileLargeAux t ell (t - 1) i : ℝ) := by exact_mod_cast le_trans hq_le_ell hLi
    have h2 : (0 : ℝ) ≤ (pileSmallAux t (t - 1) c K₂ i : ℝ) * r₁ := by positivity
    linarith
  set d := q - (ell + 1)
  have hq_eq : q = ell + 1 + d := by omega
  by_cases hc0 : c = 0
  · rw [hc0] at hgt; unfold pileTauAux at hgt
    simp only [Nat.sub_zero, Nat.zero_le, ↓reduceIte, lt_self_iff_false, Nat.add_sub_cancel] at hgt
    rw [ite_eq_left (Nat.succ_pos ell)] at hgt
    rw [hq_eq] at hgt; push_cast at hgt; nlinarith
  · have hc_pos : 0 < c := by omega
    rw [pileTauAux_u0_pos ht hc_pos (by omega), hq_eq] at hgt
    push_cast at hgt
    have htu1 : t - (t - 1) = 1 := by omega
    by_cases hd0 : d = 0
    · have hq1 : q = ell + 1 := by omega
      by_cases hiu : i.1 < t - 1
      · have hLi : pileLargeAux t ell (t - 1) i = ell + 1 := ite_eq_left hiu
        rw [hq1, hLi]
        have : (0 : ℝ) ≤ (pileSmallAux t (t - 1) c K₂ i : ℝ) * r₁ := by positivity
        linarith
      · have hLi : pileLargeAux t ell (t - 1) i = ell := ite_eq_right hiu
        have hSi_pos : 1 ≤ pileSmallAux t (t - 1) c K₂ i := by
          unfold pileSmallAux; rw [htu1, Nat.one_mul]
          by_cases hcK : c ≤ K₂
          · rw [ite_eq_left hcK, ite_eq_right hiu, Nat.div_one]; omega
          · rw [ite_eq_right hcK]
            generalize (c - K₂) / t = w; generalize (c - K₂) % t = v
            split_ifs <;> omega
        rw [hq1, hLi]
        have hSiR : (1 : ℝ) ≤ (pileSmallAux t (t - 1) c K₂ i : ℝ) := by exact_mod_cast hSi_pos
        push_cast; nlinarith
    · have hd_pos : 1 ≤ d := by omega
      set m := ceilDiv c t - 1
      have hm_gt : (d : ℝ) * r₂ < (m : ℝ) := by linarith
      have hm_ge_d1 : d + 1 ≤ m := by
        have h1 : (d : ℝ) < (m : ℝ) := by nlinarith
        have h2 : d < m := by exact_mod_cast h1
        omega
      have hm_ge_dK : d * (K₂ - 1) + 1 ≤ m := by
        have h1 : (d : ℝ) * ((K₂ : ℝ) - 1) < (m : ℝ) := by nlinarith
        have h2 : ((d * (K₂ - 1) : ℕ) : ℝ) < (m : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ K₂), Nat.cast_one]; exact h1
        have h3 : d * (K₂ - 1) < m := by exact_mod_cast h2
        omega
      have hc_ge : m * t + 1 ≤ c := ceilDiv_sub_one_mul_lt ht hc_pos
      by_cases ht1 : t = 1
      · subst ht1
        have hLi : pileLargeAux 1 ell 0 i = ell := by unfold pileLargeAux; simp
        have hSi : pileSmallAux 1 0 c K₂ i = c := by
          unfold pileSmallAux
          simp only [Nat.sub_zero, Nat.one_mul, Nat.not_lt_zero, ↓reduceIte, Nat.div_one, Nat.mod_one]
          by_cases hcK : c ≤ K₂
          · rw [ite_eq_left hcK]; simp
          · rw [ite_eq_right hcK]; simp only [le_refl, ↓reduceIte]; omega
        rw [Nat.sub_self, hq_eq, hLi, hSi]
        have hc_ge_d1 : d + 1 ≤ c := by omega
        have hcR : (d : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hc_ge_d1
        push_cast; nlinarith
      · have ht2 : 2 ≤ t := by omega
        have hc_ge_dtK : d * t + K₂ ≤ c := by
          by_cases hK2_eq : K₂ = 2
          · nlinarith only [hc_ge, hm_ge_d1, ht2, hK2_eq]
          · have hK3 : 3 ≤ K₂ := by omega
            have hKsub : (K₂ - 2) + 2 = K₂ := by omega
            have hsub : d * (K₂ - 1) = d + d * (K₂ - 2) := by
              have := Nat.mul_add d 1 (K₂ - 2)
              have h1 : 1 + (K₂ - 2) = K₂ - 1 := by omega
              rw [h1, Nat.mul_one] at this; exact this
            have hge_K2 : K₂ - 2 ≤ d * (K₂ - 2) := Nat.le_mul_of_pos_left _ hd_pos
            have hm_low : d + (K₂ - 2) + 1 ≤ m := by omega
            nlinarith only [hc_ge, hm_low, ht2, hKsub]
        have hc_gt_K : ¬ c ≤ K₂ := by nlinarith only [hc_ge_dtK, ht2, hd_pos]
        have hw'_ge : d ≤ (c - K₂) / t := (Nat.le_div_iff_mul_le ht).mpr (by omega)
        unfold pileSmallAux; rw [htu1, Nat.one_mul, ite_eq_right hc_gt_K]
        generalize (c - K₂) / t = w' at hw'_ge
        generalize (c - K₂) % t = v'
        set S := if v' ≤ t - 1 then if i.1 < t - 1 then w' + if i.1 < v' then 1 else 0 else K₂ + w'
            else if i.1 < t - 1 then w' + 1 else K₂ + w' + if i.1 - (t - 1) < v' - (t - 1) then 1 else 0
        by_cases hiu : i.1 < t - 1
        · have hLi : pileLargeAux t ell (t - 1) i = ell + 1 := ite_eq_left hiu
          have hSi_ge : d ≤ S := by dsimp only [S]; split_ifs <;> omega
          rw [hq_eq, hLi]
          have hSiR : (d : ℝ) ≤ (S : ℝ) := by exact_mod_cast hSi_ge
          push_cast; nlinarith only [hSiR, hr₁]
        · have hLi : pileLargeAux t ell (t - 1) i = ell := ite_eq_right hiu
          have hSi_ge : d + 2 ≤ S := by dsimp only [S]; split_ifs <;> omega
          rw [hq_eq, hLi]
          have hSiR : (d : ℝ) + 2 ≤ (S : ℝ) := by exact_mod_cast hSi_ge
          push_cast; nlinarith only [hSiR, hr₁]

private lemma phase1_bundle_lower_bound_nowrap {t ell u c K₂ q : ℕ} {r₁ r₂ : ℝ}
    (ht : 0 < t) (hu1_lt : u + 1 < t) (hr₁ : 1 < r₁) (hr₂ : 1 < r₂)
    (hK₂_lo : (K₂ : ℝ) - 1 < r₂) (hK₂_hi : r₂ ≤ (K₂ : ℝ))
    (hgt : (q : ℝ) * r₂ < pileTauAux t ell (u + 1) c K₂ r₂) (i : Fin t) :
    (q : ℝ) ≤ (pileLargeAux t ell u i : ℝ) + (pileSmallAux t u c K₂ i : ℝ) * r₁ := by
  have hK2 : 2 ≤ K₂ := by
    have : (1 : ℝ) < (K₂ : ℝ) := lt_of_lt_of_le hr₂ hK₂_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K₂)
  have htu_pos : 0 < t - u := by omega
  have htu1_pos : 0 < t - (u + 1) := by omega
  have hcap_rel : (t - u) * K₂ = (t - (u + 1)) * K₂ + K₂ := by
    have : t - u = (t - (u + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  by_cases hq_le_ell : q ≤ ell
  · have hLi : ell ≤ pileLargeAux t ell u i := by unfold pileLargeAux; split_ifs <;> omega
    have h1 : (q : ℝ) ≤ (pileLargeAux t ell u i : ℝ) := by exact_mod_cast le_trans hq_le_ell hLi
    have h2 : (0 : ℝ) ≤ (pileSmallAux t u c K₂ i : ℝ) * r₁ := by positivity
    linarith
  set d := q - (ell + 1)
  have hq_eq : q = ell + 1 + d := by omega
  have hc_gt1 : (t - (u + 1)) * K₂ < c := by
    by_contra hle1
    push Not at hle1
    unfold pileTauAux at hgt
    rw [ite_eq_left hle1] at hgt
    by_cases hc0 : c = 0
    · rw [ite_eq_left hc0, ite_eq_left (Nat.succ_pos u), hq_eq] at hgt
      push_cast at hgt; nlinarith
    · rw [ite_eq_right hc0] at hgt
      have hcK : ceilDiv c (t - (u + 1)) ≤ K₂ := ceilDiv_le_of_le_mul htu1_pos hle1
      have hcp : 1 ≤ ceilDiv c (t - (u + 1)) := ceilDiv_pos htu1_pos (by omega)
      have hR : ((ceilDiv c (t - (u + 1)) - 1 : ℕ) : ℝ) ≤ (K₂ : ℝ) - 1 := by
        rw [Nat.cast_sub hcp, Nat.cast_one]
        have : (ceilDiv c (t - (u + 1)) : ℝ) ≤ (K₂ : ℝ) := by exact_mod_cast hcK
        linarith
      rw [hq_eq] at hgt; push_cast at hgt; nlinarith
  by_cases hd0 : d = 0
  · have hq1 : q = ell + 1 := by omega
    by_cases hiu : i.1 < u
    · have hLi : pileLargeAux t ell u i = ell + 1 := ite_eq_left hiu
      rw [hq1, hLi]
      have : (0 : ℝ) ≤ (pileSmallAux t u c K₂ i : ℝ) * r₁ := by positivity
      linarith
    · have hLi : pileLargeAux t ell u i = ell := ite_eq_right hiu
      have hc_ge_tu : t - u ≤ c := by
        have : 2 * (t - (u + 1)) ≤ (t - (u + 1)) * K₂ := by nlinarith
        omega
      have hSi_pos : 1 ≤ pileSmallAux t u c K₂ i := by
        unfold pileSmallAux
        by_cases hle0 : c ≤ (t - u) * K₂
        · rw [ite_eq_left hle0, ite_eq_right hiu]
          have : 1 ≤ c / (t - u) := (Nat.le_div_iff_mul_le htu_pos).mpr (by omega)
          exact le_trans this (Nat.le_add_right _ _)
        · rw [ite_eq_right hle0]
          generalize (c - (t - u) * K₂) / t = w; generalize (c - (t - u) * K₂) % t = v
          split_ifs <;> omega
      rw [hq1, hLi]
      have hSiR : (1 : ℝ) ≤ (pileSmallAux t u c K₂ i : ℝ) := by exact_mod_cast hSi_pos
      push_cast; nlinarith
  · have hd_pos : 1 ≤ d := by omega
    have ht2 : 2 ≤ t := by omega
    unfold pileTauAux at hgt
    rw [ite_eq_right (not_le.mpr hc_gt1), hq_eq] at hgt
    push_cast at hgt
    have hdm1 : t * ((c - (t - (u + 1)) * K₂) / t) + (c - (t - (u + 1)) * K₂) % t =
        c - (t - (u + 1)) * K₂ := Nat.div_add_mod _ t
    have hv1_lt : (c - (t - (u + 1)) * K₂) % t < t := Nat.mod_lt _ ht
    have hrem1_ge : d * t + K₂ ≤ c - (t - (u + 1)) * K₂ := by
      have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
      generalize (c - (t - (u + 1)) * K₂) / t = w1 at hgt hdm1
      generalize (c - (t - (u + 1)) * K₂) % t = v1 at hgt hdm1 hv1_lt
      by_cases hvu1 : v1 ≤ u + 1
      · rw [ite_eq_left hvu1] at hgt
        have hw1_gt : (d : ℝ) * r₂ < (w1 : ℝ) := by
          split_ifs at hgt <;> linarith only [hgt, hK₂_lo, hK₂_hi]
        have hw1_ge_d1 : d + 1 ≤ w1 := by
          have h1 : (d : ℝ) < (w1 : ℝ) := by nlinarith only [hw1_gt, hr₂, hdR]
          have h2 : d < w1 := by exact_mod_cast h1
          omega
        have hw1_ge_dK : d * (K₂ - 1) + 1 ≤ w1 := by
          have h1 : (d : ℝ) * ((K₂ : ℝ) - 1) < (w1 : ℝ) := by nlinarith only [hw1_gt, hK₂_lo, hdR]
          have h2 : ((d * (K₂ - 1) : ℕ) : ℝ) < (w1 : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ K₂), Nat.cast_one]; exact h1
          have h3 : d * (K₂ - 1) < w1 := by exact_mod_cast h2
          omega
        by_cases hK2_eq : K₂ = 2
        · nlinarith only [hdm1, hw1_ge_d1, ht2, hK2_eq]
        · have hK3 : 3 ≤ K₂ := by omega
          have hKsub : (K₂ - 2) + 2 = K₂ := by omega
          have hsub : d * (K₂ - 1) = d + d * (K₂ - 2) := by
            have := Nat.mul_add d 1 (K₂ - 2)
            have h1 : 1 + (K₂ - 2) = K₂ - 1 := by omega
            rw [h1, Nat.mul_one] at this; exact this
          have hge_K2 : K₂ - 2 ≤ d * (K₂ - 2) := Nat.le_mul_of_pos_left _ hd_pos
          have hw1_low : d + (K₂ - 2) + 1 ≤ w1 := by omega
          nlinarith only [hdm1, hw1_low, ht2, hKsub]
      · rw [ite_eq_right hvu1] at hgt
        have hv1_ge2 : 2 ≤ v1 := by omega
        have ht3 : 3 ≤ t := by omega
        have hw1_ge_dK : d * (K₂ - 1) ≤ w1 := by
          have h1 : ((d : ℝ) + 1) * ((K₂ : ℝ) - 1) < (K₂ : ℝ) + (w1 : ℝ) := by
            nlinarith only [hgt, hK₂_lo, hdR]
          have h3 : ((d * (K₂ - 1) : ℕ) : ℝ) < (w1 : ℝ) + 1 := by
            rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ K₂), Nat.cast_one]; linarith only [h1]
          have h4 : d * (K₂ - 1) < w1 + 1 := by exact_mod_cast h3
          omega
        by_cases hK2_eq : K₂ = 2
        · have hd_le : d ≤ w1 := by rw [hK2_eq] at hw1_ge_dK; simpa using hw1_ge_dK
          nlinarith only [hdm1, hd_le, hv1_ge2, hK2_eq]
        · have hK3 : 3 ≤ K₂ := by omega
          have hKsub : (K₂ - 2) + 2 = K₂ := by omega
          have hsub : d * (K₂ - 1) = d + d * (K₂ - 2) := by
            have := Nat.mul_add d 1 (K₂ - 2)
            have h1 : 1 + (K₂ - 2) = K₂ - 1 := by omega
            rw [h1, Nat.mul_one] at this; exact this
          have hge_K2 : K₂ - 2 ≤ d * (K₂ - 2) := Nat.le_mul_of_pos_left _ hd_pos
          have hw1_low : d + (K₂ - 2) ≤ w1 := by omega
          nlinarith only [hdm1, hw1_low, hv1_ge2, ht3, hKsub]
    have hdt_pos : 1 ≤ d * t := Nat.mul_pos hd_pos ht
    have hc_gt0 : (t - u) * K₂ < c := by omega
    have hw0_ge : d ≤ (c - (t - u) * K₂) / t := (Nat.le_div_iff_mul_le ht).mpr (by omega)
    unfold pileSmallAux; rw [ite_eq_right (not_le.mpr hc_gt0)]
    generalize (c - (t - u) * K₂) / t = w0 at hw0_ge
    generalize (c - (t - u) * K₂) % t = v0
    set S := if v0 ≤ u then if i.1 < u then w0 + if i.1 < v0 then 1 else 0 else K₂ + w0
        else if i.1 < u then w0 + 1 else K₂ + w0 + if i.1 - u < v0 - u then 1 else 0
    by_cases hiu : i.1 < u
    · have hLi : pileLargeAux t ell u i = ell + 1 := ite_eq_left hiu
      have hSi_ge : d ≤ S := by dsimp only [S]; split_ifs <;> omega
      rw [hq_eq, hLi]
      have hSiR : (d : ℝ) ≤ (S : ℝ) := by exact_mod_cast hSi_ge
      push_cast; nlinarith only [hSiR, hr₁]
    · have hLi : pileLargeAux t ell u i = ell := ite_eq_right hiu
      have hSi_ge : d + 2 ≤ S := by dsimp only [S]; split_ifs <;> omega
      rw [hq_eq, hLi]
      have hSiR : (d : ℝ) + 2 ≤ (S : ℝ) := by exact_mod_cast hSi_ge
      push_cast; nlinarith only [hSiR, hr₁]

/-- **Phase-1 / Phase-3 No-Jump Lemma**: if `q * r₂ < pileTau t (p + 1) c K₂ r₂`, then every
bundle `i : Fin t` of `identicalPile t p c K₂` satisfies `(q : ℝ) ≤ L_i + S_i * r₁`. -/
lemma phase1_bundle_lower_bound {t p c K₂ q : ℕ} {r₁ r₂ : ℝ}
    (ht : 0 < t) (hr₁ : 1 < r₁) (hr₂ : 1 < r₂)
    (hK₂_lo : (K₂ : ℝ) - 1 < r₂) (hK₂_hi : r₂ ≤ (K₂ : ℝ))
    (hgt : (q : ℝ) * r₂ < pileTau t (p + 1) c K₂ r₂) (i : Fin t) :
    (q : ℝ) ≤ (pileLarge t p i : ℝ) + (pileSmall t p c K₂ i : ℝ) * r₁ := by
  have hu_lt : p % t < t := Nat.mod_lt p ht
  unfold pileTau at hgt
  unfold pileLarge pileSmall
  by_cases hwrap : p % t + 1 = t
  · have hdm := div_mod_succ_of_eq ht hwrap
    have hu_eq : p % t = t - 1 := by omega
    rw [hdm.1, hdm.2] at hgt
    rw [hu_eq]
    exact phase1_bundle_lower_bound_wrap ht hr₁ hr₂ hK₂_lo hK₂_hi hgt i
  · have hdm := div_mod_succ_of_lt ht (show p % t + 1 < t by omega)
    rw [hdm.1, hdm.2] at hgt
    exact phase1_bundle_lower_bound_nowrap ht (show p % t + 1 < t by omega) hr₁ hr₂ hK₂_lo hK₂_hi hgt i

end BivaluedChoresEFX
