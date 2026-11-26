module

public import BivaluedChoresEFX.IdenticalAgents
public import BivaluedChoresEFX.TwoAgentTypes
public import BivaluedChoresEFX.Sperner2D

/-!
# EFX Existence for Three-Agent-Type Personalized Bi-Valued Chores (2D Sperner + Chain/Star Bridge)

Theorem C2 (`exists_efx_three_agent_types_bivalued`) gives a complete EFX allocation
for `n ≥ 1` agents with three type labels. Each type `b` assigns costs in `{p b, q b}`
with `0 < p b ≤ q b`. An item has cost `p b` for zero, one, or all three types. A type
may be empty or assign a constant cost to all chores.

## Proof architecture

1. `pileTau_mono_p` bounds the change of a pile's threshold when its large-item count grows.
2. A vertex of the triangular grid specifies the number of chores in each of the three piles.
   The conservative threshold `tildeTau` vanishes at an empty pile, giving Sperner's
   boundary condition. A grid point passing all three cross-pile tests already gives EFX.
3. Otherwise `sperner_2d` supplies a rainbow triangle. For an up-triangle, the bounds exclude
   the five nonidentity color permutations. For a down-triangle they exclude the identity
   permutation and reduce the other five cases to `threeTypeSpec_of_subcase4a`.
4. In subcase 4a, two piles tie for smallest bundle size. Fix the third pile and use a
   single-item bridge. In subcase 4b all three piles tie. The threshold tests give a
   two-step chain bridge if some type is EASY, and a two-spoke star bridge if all are HARD.
-/

@[expose] public section

namespace BivaluedChoresEFX

open scoped BigOperators

/-! ### Part 1: Monotonicity of `pileTau` in Large-Item Count `p` -/

private lemma ceilDiv_antitone_denom {s d₁ d₂ : ℕ} (hd₁ : 0 < d₁) (hle : d₁ ≤ d₂) :
    ceilDiv s d₂ ≤ ceilDiv s d₁ := by
  have hd₂ : 0 < d₂ := lt_of_lt_of_le hd₁ hle
  refine ceilDiv_le_of_le_mul hd₂ ?_
  have h1 : s ≤ d₁ * ceilDiv s d₁ := by
    unfold ceilDiv
    have hdm := Nat.div_add_mod (s + d₁ - 1) d₁
    have hmlt := Nat.mod_lt (s + d₁ - 1) hd₁
    omega
  exact le_trans h1 (Nat.mul_le_mul_right _ hle)

private lemma pileTauAux_mono_p_wrap {t ell s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTauAux t ell (t - 1) s K r ≤ pileTauAux t (ell + 1) 0 s K r := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have hcap0 : (t - (t - 1)) * K = K := by
    have : t - (t - 1) = 1 := by omega
    rw [this, Nat.one_mul]
  have hcap1 : (t - 0) * K = t * K := by simp
  have hK_le_tK : K ≤ t * K := Nat.le_mul_of_pos_left K ht
  by_cases hs0 : s = 0
  · subst hs0
    unfold pileTauAux
    rw [ite_eq_left (Nat.zero_le _), ite_eq_left (Nat.zero_le _),
        ite_eq_left rfl, ite_eq_left rfl, ite_eq_right (Nat.not_lt_zero 0),
        ite_eq_left (Nat.succ_pos ell)]
    simp only [Nat.add_sub_cancel]
    split_ifs
    · exact le_refl _
    · have : ((ell - 1 : ℕ) : ℝ) ≤ (ell : ℝ) := by exact_mod_cast Nat.sub_le ell 1
      nlinarith only [this, hr]
    · have : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
      nlinarith only [this, hr]
  · by_cases hsK : s ≤ K
    · have hle0 : s ≤ (t - (t - 1)) * K := by omega
      have hle1 : s ≤ (t - 0) * K := by omega
      unfold pileTauAux
      rw [ite_eq_left hle0, ite_eq_left hle1, ite_eq_right hs0, ite_eq_right hs0]
      have htu : t - (t - 1) = 1 := by omega
      have hcd1 : ceilDiv s 1 = s := by unfold ceilDiv; simp
      rw [htu, hcd1]
      have hs_ge1 : 1 ≤ s := by omega
      have hsubR : ((s - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
        rw [Nat.cast_sub hs_ge1, Nat.cast_one]
        have : (s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hsK
        linarith only [this]
      have hnn : (0 : ℝ) ≤ ((ceilDiv s (t - 0) - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      push_cast
      linarith only [hsubR, hK_lo, hnn]
    · by_cases hstK : s ≤ t * K
      · have hgt0 : ¬ s ≤ (t - (t - 1)) * K := by omega
        have hle1 : s ≤ (t - 0) * K := by omega
        unfold pileTauAux
        rw [ite_eq_right hgt0, ite_eq_left hle1, ite_eq_right hs0, hcap0, Nat.sub_zero]
        have hv_le : (s - K) % t ≤ t - 1 := by have := Nat.mod_lt (s - K) ht; omega
        rw [ite_eq_left hv_le]
        have hdm : t * ((s - K) / t) + (s - K) % t = s - K := Nat.div_add_mod (s - K) t
        have hlt_s : t * ((s - K) / t) < s := by omega
        have hwc : (s - K) / t + 1 ≤ ceilDiv s t := by
          have h1 : t * ((s - K) / t + 1) ≤ s + t - 1 := by rw [Nat.mul_add, Nat.mul_one]; omega
          exact (Nat.le_div_iff_mul_le ht).mpr (by rw [Nat.mul_comm]; exact h1)
        have hcp : 1 ≤ ceilDiv s t := ceilDiv_pos ht (by omega)
        have hwR : (((s - K) / t : ℕ) : ℝ) ≤ ((ceilDiv s t - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : (s - K) / t ≤ ceilDiv s t - 1)
        split_ifs <;> (push_cast; linarith only [hwR, hK_lo])
      · have hgt0 : ¬ s ≤ (t - (t - 1)) * K := by omega
        have hgt1 : ¬ s ≤ (t - 0) * K := by omega
        unfold pileTauAux
        rw [ite_eq_right hgt0, ite_eq_right hgt1, hcap0, hcap1]
        have hv0_le : (s - K) % t ≤ t - 1 := by have := Nat.mod_lt (s - K) ht; omega
        rw [ite_eq_left hv0_le]
        have hdm0 : t * ((s - K) / t) + (s - K) % t = s - K := Nat.div_add_mod (s - K) t
        have hdm1 : t * ((s - t * K) / t) + (s - t * K) % t = s - t * K := Nat.div_add_mod (s - t * K) t
        have hv1_lt : (s - t * K) % t < t := Nat.mod_lt (s - t * K) ht
        generalize (s - K) / t = w0 at hdm0
        generalize (s - K) % t = v0 at hdm0 hv0_le
        generalize (s - t * K) / t = w1 at hdm1
        generalize (s - t * K) % t = v1 at hdm1 hv1_lt
        have hrem_rel : t * w0 + v0 + K = t * (w1 + K) + v1 := by
          have : t * (w1 + K) = t * w1 + t * K := Nat.mul_add t w1 K
          omega
        by_cases hv10 : v1 = 0
        · rw [hv10, ite_eq_left (le_refl 0), ite_eq_right (Nat.not_lt_zero 0)]
          have hw_le : w0 + 1 ≤ w1 + K := by
            have : t * w0 < t * (w1 + K) := by omega
            have : w0 < w1 + K := Nat.lt_of_mul_lt_mul_left this
            omega
          have hwR : (w0 : ℝ) ≤ (w1 : ℝ) + (K : ℝ) - 1 := by
            have : (w0 : ℝ) + 1 ≤ (w1 : ℝ) + (K : ℝ) := by exact_mod_cast hw_le
            linarith only [this]
          split_ifs <;> (push_cast; linarith only [hwR, hK_lo])
        · have hv1_gt : ¬ v1 ≤ 0 := by omega
          rw [ite_eq_right hv1_gt]
          have hw_le : w0 ≤ w1 + K := by
            have : t * w0 < t * (w1 + K + 1) := by
              rw [Nat.mul_add, Nat.mul_one]; omega
            have : w0 < w1 + K + 1 := Nat.lt_of_mul_lt_mul_left this
            omega
          have hwR : (w0 : ℝ) ≤ (w1 : ℝ) + (K : ℝ) := by exact_mod_cast hw_le
          split_ifs <;> (push_cast; linarith only [hwR, hK_lo])

private lemma pileTauAux_mono_p_nowrap {t ell u s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hu1_lt : u + 1 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTauAux t ell u s K r ≤ pileTauAux t ell (u + 1) s K r := by
  have hK2 : 2 ≤ K := by
    have : (1 : ℝ) < (K : ℝ) := lt_of_lt_of_le hr hK_hi
    exact_mod_cast (by linarith : (1 : ℝ) < K)
  have htu1_pos : 0 < t - (u + 1) := by omega
  have hcap_rel : (t - u) * K = (t - (u + 1)) * K + K := by
    have : t - u = (t - (u + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
  by_cases hs0 : s = 0
  · subst hs0
    unfold pileTauAux
    rw [ite_eq_left (Nat.zero_le _), ite_eq_left (Nat.zero_le _),
        ite_eq_left rfl, ite_eq_left rfl, ite_eq_left (Nat.succ_pos u)]
    split_ifs
    · exact le_refl _
    · have : ((ell - 1 : ℕ) : ℝ) ≤ (ell : ℝ) := by exact_mod_cast Nat.sub_le ell 1
      nlinarith only [this, hr]
    · have : (0 : ℝ) ≤ (ell : ℝ) := Nat.cast_nonneg ell
      nlinarith only [this, hr]
  · by_cases hle1 : s ≤ (t - (u + 1)) * K
    · have hle0 : s ≤ (t - u) * K := by omega
      unfold pileTauAux
      rw [ite_eq_left hle0, ite_eq_left hle1, ite_eq_right hs0, ite_eq_right hs0]
      have hc : ceilDiv s (t - u) ≤ ceilDiv s (t - (u + 1)) :=
        ceilDiv_antitone_denom htu1_pos (by omega)
      have hcR : ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ ((ceilDiv s (t - (u + 1)) - 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le_sub_right hc 1
      linarith only [hcR]
    · by_cases hle0 : s ≤ (t - u) * K
      · unfold pileTauAux
        rw [ite_eq_left hle0, ite_eq_right hle1, ite_eq_right hs0]
        have htu0_pos : 0 < t - u := by omega
        have hcK : ceilDiv s (t - u) ≤ K := ceilDiv_le_of_le_mul htu0_pos hle0
        have hcp : 1 ≤ ceilDiv s (t - u) := ceilDiv_pos htu0_pos (by omega)
        have hLHS : ((ceilDiv s (t - u) - 1 : ℕ) : ℝ) ≤ (K : ℝ) - 1 := by
          rw [Nat.cast_sub hcp, Nat.cast_one]
          have : (ceilDiv s (t - u) : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcK
          linarith only [this]
        have hdm1 : t * ((s - (t - (u + 1)) * K) / t) + (s - (t - (u + 1)) * K) % t =
            s - (t - (u + 1)) * K := Nat.div_add_mod _ t
        generalize (s - (t - (u + 1)) * K) / t = w1 at hdm1
        generalize (s - (t - (u + 1)) * K) % t = v1 at hdm1
        have hw1_nn : (0 : ℝ) ≤ (w1 : ℝ) := Nat.cast_nonneg w1
        split_ifs with h1 h2
        · push_cast; linarith only [hLHS, hK_lo, hw1_nn]
        · have hv10 : v1 = 0 := by omega
          have hw1_pos : 1 ≤ w1 := by
            have : 0 < t * w1 := by omega
            exact Nat.pos_of_mul_pos_left this
          have hw1R : (1 : ℝ) ≤ (w1 : ℝ) := by exact_mod_cast hw1_pos
          linarith only [hLHS, hw1R]
        · linarith only [hLHS, hw1_nn]
      · unfold pileTauAux
        rw [ite_eq_right hle0, ite_eq_right hle1]
        have hdm0 : t * ((s - (t - u) * K) / t) + (s - (t - u) * K) % t = s - (t - u) * K :=
          Nat.div_add_mod _ t
        have hdm1 : t * ((s - (t - (u + 1)) * K) / t) + (s - (t - (u + 1)) * K) % t =
            s - (t - (u + 1)) * K := Nat.div_add_mod _ t
        have hv0_lt : (s - (t - u) * K) % t < t := Nat.mod_lt _ ht
        have hv1_lt : (s - (t - (u + 1)) * K) % t < t := Nat.mod_lt _ ht
        generalize (s - (t - u) * K) / t = w0 at hdm0
        generalize (s - (t - u) * K) % t = v0 at hdm0 hv0_lt
        generalize (s - (t - (u + 1)) * K) / t = w1 at hdm1
        generalize (s - (t - (u + 1)) * K) % t = v1 at hdm1 hv1_lt
        have hrel : t * w1 + v1 = t * w0 + v0 + K := by omega
        have hw_le : w0 ≤ w1 := by
          by_contra hgt
          have : t * (w1 + 1) ≤ t * w0 := Nat.mul_le_mul_left t (by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        by_cases hw_lt : w0 + 1 ≤ w1
        · have hwR : (w0 : ℝ) + 1 ≤ (w1 : ℝ) := by exact_mod_cast hw_lt
          have hLHS_le : (if v0 ≤ u then
              if 0 < v0 then ((ell + 1 : ℕ) : ℝ) * r + (w0 : ℝ)
              else (ell : ℝ) * r + (K : ℝ) + (w0 : ℝ) - 1
            else (ell : ℝ) * r + (K : ℝ) + (w0 : ℝ)) ≤ (ell : ℝ) * r + (K : ℝ) + (w0 : ℝ) := by
            split_ifs <;> (push_cast; linarith only [hK_hi])
          have hRHS_ge : (ell : ℝ) * r + (K : ℝ) + (w0 : ℝ) ≤
              (if v1 ≤ u + 1 then
                if 0 < v1 then ((ell + 1 : ℕ) : ℝ) * r + (w1 : ℝ)
                else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ) - 1
              else (ell : ℝ) * r + (K : ℝ) + (w1 : ℝ)) := by
            split_ifs <;> (push_cast; linarith only [hK_lo, hwR])
          exact le_trans hLHS_le hRHS_ge
        · have hweq : w1 = w0 := by omega
          subst hweq
          have hv1_eq : v1 = v0 + K := by omega
          split_ifs with h1 h2 h3 h4 h5 h6
          · exact le_refl _
          · omega
          · push_cast; linarith only [hK_hi]
          · push_cast; linarith only [hK_lo]
          · omega
          · linarith only []
          · omega
          · omega
          · exact le_refl _

/-- **Monotonicity of `pileTau` in Large-Item Count `p`**:
adding one large item never decreases the closed-form EFX envy threshold `pileTau`. -/
lemma pileTau_mono_p {t p s K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    pileTau t p s K r ≤ pileTau t (p + 1) s K r := by
  have hu_lt : p % t < t := Nat.mod_lt p ht
  unfold pileTau
  by_cases hwrap : p % t + 1 = t
  · have hdm := div_mod_succ_of_eq ht hwrap
    rw [hdm.1, hdm.2, show p % t = t - 1 by omega]
    exact pileTauAux_mono_p_wrap ht hr hK_lo hK_hi
  · have hdm := div_mod_succ_of_lt (p := p) ht (by omega)
    rw [hdm.1, hdm.2]
    exact pileTauAux_mono_p_nowrap ht (by omega) hr hK_lo hK_hi

/-- When `s = 1`, dropping to `s = 0` after adding 1 large item satisfies
`pileTau t (p + 1) 0 K r ≤ r * pileMinSize t p 1 K`, so `nB = 1` is always EASY. -/
private lemma pileTau_succ_zero_le_mul_minSize {t p K : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK2 : 2 ≤ K) :
    pileTau t (p + 1) 0 K r ≤ r * (pileMinSize t p 1 K : ℝ) := by
  have htau_eq : pileTau t (p + 1) 0 K r = ((p / t : ℕ) : ℝ) * r := by
    have hu_lt : p % t < t := Nat.mod_lt p ht
    unfold pileTau
    by_cases hwrap : p % t + 1 = t
    · have hdm := div_mod_succ_of_eq ht hwrap
      rw [hdm.1, hdm.2]; unfold pileTauAux
      rw [ite_eq_left (Nat.zero_le _), ite_eq_left rfl,
          ite_eq_right (Nat.not_lt_zero 0), ite_eq_left (Nat.succ_pos _)]
      simp
    · have hdm := div_mod_succ_of_lt (p := p) ht (by omega)
      rw [hdm.1, hdm.2]; unfold pileTauAux
      rw [ite_eq_left (Nat.zero_le _), ite_eq_left rfl, ite_eq_left (Nat.succ_pos _)]
  have hmin_ge : p / t ≤ pileMinSize t p 1 K := by
    have hle1 : 1 ≤ (t - p % t) * K := by
      have hmlt : p % t < t := Nat.mod_lt p ht
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    unfold pileMinSize pileMinSizeAux
    rw [ite_eq_left hle1]
    split_ifs <;> first
      | exact le_refl _
      | exact Nat.le_add_right _ _
  have hminR : ((p / t : ℕ) : ℝ) ≤ (pileMinSize t p 1 K : ℝ) := by exact_mod_cast hmin_ge
  rw [htau_eq]
  nlinarith only [hminR, hr]

/-! ### Part 2: Unified Total-Chore Simplex Functions (`tauM`, `minM`, `tildeTau`) -/

/-- Closed-form threshold of a pile with total chore count `m` (`min m nB` small, `m - nB` large). -/
private def tauM (t nB K : ℕ) (r : ℝ) (m : ℕ) : ℝ :=
  pileTau t (m - nB) (min m nB) K r

/-- Closed-form minimum bundle size of a pile with total chore count `m`. -/
private def minM (t nB K : ℕ) (m : ℕ) : ℕ :=
  pileMinSize t (m - nB) (min m nB) K

/-- Normalized conservative threshold `tildeTau`:
`tauM / r` in Case A (`nB ≤ m`), and `tauM` in Case B (`m < nB`). -/
private noncomputable def tildeTau (t nB K : ℕ) (r : ℝ) (m : ℕ) : ℝ :=
  if nB ≤ m then tauM t nB K r m / r else tauM t nB K r m

private lemma minM_of_le {t nB K m : ℕ} (ht : 0 < t) (hle : m ≤ nB) :
    minM t nB K m = m / t := by
  unfold minM pileMinSize
  rw [Nat.sub_eq_zero_of_le hle, Nat.min_eq_left hle, Nat.zero_div, Nat.zero_mod,
      pileMinSizeAux_u0 ht, zero_add]

private lemma tauM_of_le_pos {t nB K m : ℕ} {r : ℝ} (ht : 0 < t) (hle : m ≤ nB)
    (hm : 0 < m) (hK2 : 2 ≤ K) :
    tauM t nB K r m = ((ceilDiv m t - 1 : ℕ) : ℝ) := by
  unfold tauM pileTau
  rw [Nat.sub_eq_zero_of_le hle, Nat.min_eq_left hle, Nat.zero_div, Nat.zero_mod,
      pileTauAux_u0_pos ht hm (by omega : 1 ≤ K)]
  simp

private lemma tildeTau_zero {t nB K : ℕ} {r : ℝ} :
    tildeTau t nB K r 0 = 0 := by
  have htau0 : tauM t nB K r 0 = 0 := by
    unfold tauM pileTau pileTauAux
    simp
  unfold tildeTau
  rw [htau0]
  split_ifs <;> simp

private lemma tildeTau_le_minM {t nB K m : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK2 : 2 ≤ K) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    tildeTau t nB K r m ≤ (minM t nB K m : ℝ) := by
  unfold tildeTau
  by_cases hA : nB ≤ m
  · rw [ite_eq_left hA]
    have hf := pileTau_le_r_mul_minSize (t := t) (p := m - nB) (s := min m nB) (K := K)
      ht hr hK_lo hK_hi
    exact (div_le_iff₀ (by linarith : 0 < r)).mpr (by unfold tauM minM at *; linarith only [hf])
  · rw [ite_eq_right hA]
    have hle : m ≤ nB := by omega
    rw [minM_of_le ht hle]
    by_cases hm0 : m = 0
    · subst hm0; unfold tauM pileTau pileTauAux; simp
    · rw [tauM_of_le_pos ht hle (by omega) hK2]
      have hcd : ceilDiv m t - 1 ≤ m / t := by
        have : m = (m - 1) + 1 := by omega
        rw [this, ceilDiv_succ_sub_one ht]
        exact Nat.div_le_div_right (by omega)
      exact_mod_cast hcd

private lemma tildeTau_le_minM_succ {t nB K m : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK2 : 2 ≤ K) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    tildeTau t nB K r m ≤ (minM t nB K (m + 1) : ℝ) := by
  unfold tildeTau
  by_cases hA : nB ≤ m
  · rw [ite_eq_left hA]
    have hsub : m + 1 - nB = (m - nB) + 1 := by omega
    have hmin0 : min m nB = nB := Nat.min_eq_right hA
    have hmin1 : min (m + 1) nB = nB := Nat.min_eq_right (by omega)
    have hmono := pileTau_mono_p (t := t) (p := m - nB) (s := nB) (K := K) ht hr hK_lo hK_hi
    have hf := pileTau_le_r_mul_minSize (t := t) (p := (m - nB) + 1) (s := nB) (K := K)
      ht hr hK_lo hK_hi
    have hle : tauM t nB K r m ≤ r * (minM t nB K (m + 1) : ℝ) := by
      unfold tauM minM; rw [hmin0, hmin1, hsub]; exact le_trans hmono hf
    exact (div_le_iff₀ (by linarith : 0 < r)).mpr (by linarith only [hle])
  · rw [ite_eq_right hA]
    have hle1 : m + 1 ≤ nB := by omega
    rw [minM_of_le ht hle1]
    have hle0 : tildeTau t nB K r m ≤ (minM t nB K m : ℝ) :=
      tildeTau_le_minM ht hr hK2 hK_lo hK_hi
    unfold tildeTau at hle0
    rw [ite_eq_right hA, minM_of_le ht (by omega)] at hle0
    have hdiv : ((m / t : ℕ) : ℝ) ≤ (((m + 1) / t : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_le_div_right (Nat.le_succ m)
    exact le_trans hle0 hdiv

private lemma tildeTau_succ_le_of_lt {t nB K m : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK2 : 2 ≤ K) (hlt : m < nB) :
    tildeTau t nB K r (m + 1) ≤ (minM t nB K m : ℝ) := by
  have htau : tauM t nB K r (m + 1) = ((m / t : ℕ) : ℝ) := by
    rw [tauM_of_le_pos ht (by omega) (Nat.succ_pos m) hK2, ceilDiv_succ_sub_one ht]
  rw [minM_of_le ht (le_of_lt hlt)]
  unfold tildeTau
  rw [htau]
  split_ifs
  · have hnn : (0 : ℝ) ≤ ((m / t : ℕ) : ℝ) := Nat.cast_nonneg _
    exact (div_le_iff₀ (by linarith : 0 < r)).mpr (by nlinarith only [hnn, hr])
  · exact le_refl _

private lemma tildeTau_succ_lt {t nB K m : ℕ} {r : ℝ}
    (ht : 0 < t) (hr : 1 < r) (hK2 : 2 ≤ K) (hK_lo : (K : ℝ) - 1 < r) (hK_hi : r ≤ (K : ℝ)) :
    tildeTau t nB K r (m + 1) < (minM t nB K m : ℝ) + 1 := by
  by_cases hA : nB ≤ m
  · unfold tildeTau
    rw [ite_eq_left (by omega : nB ≤ m + 1)]
    have hsub : m + 1 - nB = (m - nB) + 1 := by omega
    have hmin0 : min m nB = nB := Nat.min_eq_right hA
    have hmin1 : min (m + 1) nB = nB := Nat.min_eq_right (by omega)
    have hstep := pileTau_step_lt (t := t) (p := m - nB) (s := nB) (K := K) ht hr hK_lo hK_hi
    have hlt : tauM t nB K r (m + 1) < r * ((minM t nB K m : ℝ) + 1) := by
      unfold tauM minM; rw [hmin0, hmin1, hsub]; exact hstep
    exact (div_lt_iff₀ (by linarith : 0 < r)).mpr (by linarith only [hlt])
  · have hle := tildeTau_succ_le_of_lt (t := t) (nB := nB) (K := K) (m := m) (r := r) ht hr hK2 (by omega)
    linarith only [hle]

/-! ### Part 3: Abstract Three-Type Specification, Symmetry, and Concrete Realization -/

/-- A valid EFX bundle-count specification for 3 agent types (`t₀, t₁, t₂`) and 4 chore pools
`(nA, nB₀, nB₁, nB₂)` with normalized costs `r₀, r₁, r₂ > 1`. -/
structure ThreeTypeSpec (t0 t1 t2 nA nB0 nB1 nB2 : ℕ) (r0 r1 r2 : ℝ) where
  A0 : Fin t0 → ℕ
  B00 : Fin t0 → ℕ
  B10 : Fin t0 → ℕ
  B20 : Fin t0 → ℕ
  A1 : Fin t1 → ℕ
  B01 : Fin t1 → ℕ
  B11 : Fin t1 → ℕ
  B21 : Fin t1 → ℕ
  A2 : Fin t2 → ℕ
  B02 : Fin t2 → ℕ
  B12 : Fin t2 → ℕ
  B22 : Fin t2 → ℕ
  sumA  : ∑ i, A0 i + ∑ j, A1 j + ∑ k, A2 k = nA
  sumB0 : ∑ i, B00 i + ∑ j, B01 j + ∑ k, B02 k = nB0
  sumB1 : ∑ i, B10 i + ∑ j, B11 j + ∑ k, B12 k = nB1
  sumB2 : ∑ i, B20 i + ∑ j, B21 j + ∑ k, B22 k = nB2
  efx00 : ∀ i j : Fin t0,
    ownTau r0 (A0 i + B10 i + B20 i) (B00 i) ≤ ownCost r0 (A0 j + B10 j + B20 j) (B00 j)
  efx01 : ∀ (i : Fin t0) (j : Fin t1),
    ownTau r0 (A0 i + B10 i + B20 i) (B00 i) ≤ ownCost r0 (A1 j + B11 j + B21 j) (B01 j)
  efx02 : ∀ (i : Fin t0) (k : Fin t2),
    ownTau r0 (A0 i + B10 i + B20 i) (B00 i) ≤ ownCost r0 (A2 k + B12 k + B22 k) (B02 k)
  efx10 : ∀ (i : Fin t1) (j : Fin t0),
    ownTau r1 (A1 i + B01 i + B21 i) (B11 i) ≤ ownCost r1 (A0 j + B00 j + B20 j) (B10 j)
  efx11 : ∀ i j : Fin t1,
    ownTau r1 (A1 i + B01 i + B21 i) (B11 i) ≤ ownCost r1 (A1 j + B01 j + B21 j) (B11 j)
  efx12 : ∀ (i : Fin t1) (k : Fin t2),
    ownTau r1 (A1 i + B01 i + B21 i) (B11 i) ≤ ownCost r1 (A2 k + B02 k + B22 k) (B12 k)
  efx20 : ∀ (i : Fin t2) (j : Fin t0),
    ownTau r2 (A2 i + B02 i + B12 i) (B22 i) ≤ ownCost r2 (A0 j + B00 j + B10 j) (B20 j)
  efx21 : ∀ (i : Fin t2) (j : Fin t1),
    ownTau r2 (A2 i + B02 i + B12 i) (B22 i) ≤ ownCost r2 (A1 j + B01 j + B11 j) (B21 j)
  efx22 : ∀ i j : Fin t2,
    ownTau r2 (A2 i + B02 i + B12 i) (B22 i) ≤ ownCost r2 (A2 j + B02 j + B12 j) (B22 j)

/-- Swap Types 0 and 1 in a `ThreeTypeSpec`. -/
def ThreeTypeSpec.swap01 {t0 t1 t2 nA nB0 nB1 nB2 : ℕ} {r0 r1 r2 : ℝ}
    (S : ThreeTypeSpec t1 t0 t2 nA nB1 nB0 nB2 r1 r0 r2) :
    ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2 where
  A0 := S.A1
  B00 := S.B11
  B10 := S.B01
  B20 := S.B21
  A1 := S.A0
  B01 := S.B10
  B11 := S.B00
  B21 := S.B20
  A2 := S.A2
  B02 := S.B12
  B12 := S.B02
  B22 := S.B22
  sumA  := by have := S.sumA; omega
  sumB0 := by have := S.sumB1; omega
  sumB1 := by have := S.sumB0; omega
  sumB2 := by have := S.sumB2; omega
  efx00 := S.efx11
  efx01 := S.efx10
  efx02 := S.efx12
  efx10 := S.efx01
  efx11 := S.efx00
  efx12 := S.efx02
  efx20 := fun i j => by
    have h := S.efx21 i j
    have heq1 : S.A2 i + S.B12 i + S.B02 i = S.A2 i + S.B02 i + S.B12 i := by omega
    have heq2 : S.A1 j + S.B11 j + S.B01 j = S.A1 j + S.B01 j + S.B11 j := by omega
    rw [heq1, heq2]; exact h
  efx21 := fun i j => by
    have h := S.efx20 i j
    have heq1 : S.A2 i + S.B12 i + S.B02 i = S.A2 i + S.B02 i + S.B12 i := by omega
    have heq2 : S.A0 j + S.B10 j + S.B00 j = S.A0 j + S.B00 j + S.B10 j := by omega
    rw [heq1, heq2]; exact h
  efx22 := fun i j => by
    have h := S.efx22 i j
    have heq1 : S.A2 i + S.B12 i + S.B02 i = S.A2 i + S.B02 i + S.B12 i := by omega
    have heq2 : S.A2 j + S.B12 j + S.B02 j = S.A2 j + S.B02 j + S.B12 j := by omega
    rw [heq1, heq2]; exact h

/-- Cyclic rotation `(0, 1, 2) ↦ (1, 2, 0)` on a `ThreeTypeSpec`. -/
def ThreeTypeSpec.rot {t0 t1 t2 nA nB0 nB1 nB2 : ℕ} {r0 r1 r2 : ℝ}
    (S : ThreeTypeSpec t1 t2 t0 nA nB1 nB2 nB0 r1 r2 r0) :
    ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2 where
  A0 := S.A2
  B00 := S.B22
  B10 := S.B02
  B20 := S.B12
  A1 := S.A0
  B01 := S.B20
  B11 := S.B00
  B21 := S.B10
  A2 := S.A1
  B02 := S.B21
  B12 := S.B01
  B22 := S.B11
  sumA  := by have := S.sumA; omega
  sumB0 := by have := S.sumB2; omega
  sumB1 := by have := S.sumB0; omega
  sumB2 := by have := S.sumB1; omega
  efx00 := S.efx22
  efx01 := S.efx20
  efx02 := S.efx21
  efx10 := fun i j => by
    have h := S.efx02 i j
    have h1 : S.A0 i + S.B20 i + S.B10 i = S.A0 i + S.B10 i + S.B20 i := by omega
    have h2 : S.A2 j + S.B22 j + S.B12 j = S.A2 j + S.B12 j + S.B22 j := by omega
    rw [h1, h2]; exact h
  efx11 := fun i j => by
    have h := S.efx00 i j
    have h1 : S.A0 i + S.B20 i + S.B10 i = S.A0 i + S.B10 i + S.B20 i := by omega
    have h2 : S.A0 j + S.B20 j + S.B10 j = S.A0 j + S.B10 j + S.B20 j := by omega
    rw [h1, h2]; exact h
  efx12 := fun i j => by
    have h := S.efx01 i j
    have h1 : S.A0 i + S.B20 i + S.B10 i = S.A0 i + S.B10 i + S.B20 i := by omega
    have h2 : S.A1 j + S.B21 j + S.B11 j = S.A1 j + S.B11 j + S.B21 j := by omega
    rw [h1, h2]; exact h
  efx20 := fun i j => by
    have h := S.efx12 i j
    have h1 : S.A1 i + S.B21 i + S.B01 i = S.A1 i + S.B01 i + S.B21 i := by omega
    have h2 : S.A2 j + S.B22 j + S.B02 j = S.A2 j + S.B02 j + S.B22 j := by omega
    rw [h1, h2]; exact h
  efx21 := fun i j => by
    have h := S.efx10 i j
    have h1 : S.A1 i + S.B21 i + S.B01 i = S.A1 i + S.B01 i + S.B21 i := by omega
    have h2 : S.A0 j + S.B20 j + S.B00 j = S.A0 j + S.B00 j + S.B20 j := by omega
    rw [h1, h2]; exact h
  efx22 := fun i j => by
    have h := S.efx11 i j
    have h1 : S.A1 i + S.B21 i + S.B01 i = S.A1 i + S.B01 i + S.B21 i := by omega
    have h2 : S.A1 j + S.B21 j + S.B01 j = S.A1 j + S.B01 j + S.B21 j := by omega
    rw [h1, h2]; exact h

/-- Split a function `L : Fin t → ℕ` summing to `a + b + c + d` into 4 functions with those sums. -/
private lemma exists_split4 {t : ℕ} (L : Fin t → ℕ) (a b c d : ℕ)
    (hsum : ∑ i : Fin t, L i = a + b + c + d) :
    ∃ A B C D : Fin t → ℕ,
      (∀ i, A i + B i + C i + D i = L i) ∧
      (∑ i, A i = a) ∧ (∑ i, B i = b) ∧ (∑ i, C i = c) ∧ (∑ i, D i = d) := by
  obtain ⟨AB, CD, h1, hAB, hCD⟩ := exists_split_counts L (a + b) (c + d) (by omega)
  obtain ⟨A, B, h2, hA, hB⟩ := exists_split_counts AB a b hAB
  obtain ⟨C, D, h3, hC, hD⟩ := exists_split_counts CD c d hCD
  exact ⟨A, B, C, D, fun i => by have := h1 i; have := h2 i; have := h3 i; omega, hA, hB, hC, hD⟩

/-- Split a 3-group vector of large-item slots `(L0, L1, L2)` summing to `sA + sB0 + sB1 + sB2`
where `B_c` must NOT go into Group `c` (so `B0_0 = 0`, `B1_1 = 0`, `B2_2 = 0`!).
Valid whenever `sB0 ≤ sum1 + sum2`, `sB1 ≤ sum0 + sum2`, `sB2 ≤ sum0 + sum1`! -/
private lemma split_shared_pool_3 {t0 t1 t2 sA sB0 sB1 sB2 : ℕ}
    (L0 : Fin t0 → ℕ) (L1 : Fin t1 → ℕ) (L2 : Fin t2 → ℕ)
    (hsum : ∑ i, L0 i + ∑ j, L1 j + ∑ k, L2 k = sA + sB0 + sB1 + sB2)
    (h0 : sB0 = 0 ∨ ∑ i, L0 i = 0)
    (h1 : sB1 = 0 ∨ ∑ j, L1 j = 0)
    (h2 : sB2 = 0 ∨ ∑ k, L2 k = 0) :
    ∃ (A0 B10 B20 : Fin t0 → ℕ) (A1 B01 B21 : Fin t1 → ℕ) (A2 B02 B12 : Fin t2 → ℕ),
      (∀ i, A0 i + B10 i + B20 i = L0 i) ∧
      (∀ j, A1 j + B01 j + B21 j = L1 j) ∧
      (∀ k, A2 k + B02 k + B12 k = L2 k) ∧
      (∑ i, A0 i + ∑ j, A1 j + ∑ k, A2 k = sA) ∧
      (∑ j, B01 j + ∑ k, B02 k = sB0) ∧
      (∑ i, B10 i + ∑ k, B12 k = sB1) ∧
      (∑ i, B20 i + ∑ j, B21 j = sB2) := by
  let Ltot : Fin ((t0 + t1) + t2) → ℕ := Fin.addCases (Fin.addCases L0 L1) L2
  have hLtot : ∑ x, Ltot x = sA + sB0 + sB1 + sB2 := by
    simp only [Ltot, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]
    exact hsum
  obtain ⟨A, B0, B1, B2, hsplit, hA, hB0, hB1, hB2⟩ := exists_split4 Ltot sA sB0 sB1 sB2 hLtot
  let A0 := fun i : Fin t0 => A (Fin.castAdd t2 (Fin.castAdd t1 i))
  let B00 := fun i : Fin t0 => B0 (Fin.castAdd t2 (Fin.castAdd t1 i))
  let B10 := fun i : Fin t0 => B1 (Fin.castAdd t2 (Fin.castAdd t1 i))
  let B20 := fun i : Fin t0 => B2 (Fin.castAdd t2 (Fin.castAdd t1 i))
  let A1 := fun j : Fin t1 => A (Fin.castAdd t2 (Fin.natAdd t0 j))
  let B01 := fun j : Fin t1 => B0 (Fin.castAdd t2 (Fin.natAdd t0 j))
  let B11 := fun j : Fin t1 => B1 (Fin.castAdd t2 (Fin.natAdd t0 j))
  let B21 := fun j : Fin t1 => B2 (Fin.castAdd t2 (Fin.natAdd t0 j))
  let A2 := fun k : Fin t2 => A (Fin.natAdd (t0 + t1) k)
  let B02 := fun k : Fin t2 => B0 (Fin.natAdd (t0 + t1) k)
  let B12 := fun k : Fin t2 => B1 (Fin.natAdd (t0 + t1) k)
  let B22 := fun k : Fin t2 => B2 (Fin.natAdd (t0 + t1) k)
  have hA_eq : ∑ i, A0 i + ∑ j, A1 j + ∑ k, A2 k = sA := by
    simpa [A0, A1, A2, Fin.sum_univ_add] using hA
  have hB0_eq : ∑ i, B00 i + ∑ j, B01 j + ∑ k, B02 k = sB0 := by
    simpa [B00, B01, B02, Fin.sum_univ_add] using hB0
  have hB1_eq : ∑ i, B10 i + ∑ j, B11 j + ∑ k, B12 k = sB1 := by
    simpa [B10, B11, B12, Fin.sum_univ_add] using hB1
  have hB2_eq : ∑ i, B20 i + ∑ j, B21 j + ∑ k, B22 k = sB2 := by
    simpa [B20, B21, B22, Fin.sum_univ_add] using hB2
  have hsp0 : ∀ i, A0 i + B00 i + B10 i + B20 i = L0 i := fun i => by
    simpa [Ltot, A0, B00, B10, B20] using hsplit (Fin.castAdd t2 (Fin.castAdd t1 i))
  have hsp1 : ∀ j, A1 j + B01 j + B11 j + B21 j = L1 j := fun j => by
    simpa [Ltot, A1, B01, B11, B21] using hsplit (Fin.castAdd t2 (Fin.natAdd t0 j))
  have hsp2 : ∀ k, A2 k + B02 k + B12 k + B22 k = L2 k := fun k => by
    simpa [Ltot, A2, B02, B12, B22] using hsplit (Fin.natAdd (t0 + t1) k)
  have hB00_zero : ∀ i, B00 i = 0 := by
    intro i
    rcases h0 with hs0 | hL0
    · have : B00 i ≤ ∑ x, B00 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    · have : L0 i ≤ ∑ x, L0 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have := hsp0 i; omega
  have hB11_zero : ∀ j, B11 j = 0 := by
    intro j
    rcases h1 with hs1 | hL1
    · have : B11 j ≤ ∑ x, B11 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      omega
    · have : L1 j ≤ ∑ x, L1 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      have := hsp1 j; omega
  have hB22_zero : ∀ k, B22 k = 0 := by
    intro k
    rcases h2 with hs2 | hL2
    · have : B22 k ≤ ∑ x, B22 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      omega
    · have : L2 k ≤ ∑ x, L2 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      have := hsp2 k; omega
  refine ⟨A0, B10, B20, A1, B01, B21, A2, B02, B12, ?_, ?_, ?_, hA_eq, ?_, ?_, ?_⟩
  · intro i; have := hsp0 i; have := hB00_zero i; omega
  · intro j; have := hsp1 j; have := hB11_zero j; omega
  · intro k; have := hsp2 k; have := hB22_zero k; omega
  · have : ∑ i, B00 i = 0 := Finset.sum_eq_zero (fun i _ => hB00_zero i); omega
  · have : ∑ j, B11 j = 0 := Finset.sum_eq_zero (fun j _ => hB11_zero j); omega
  · have : ∑ k, B22 k = 0 := Finset.sum_eq_zero (fun k _ => hB22_zero k); omega

/-! ### Part 4: Grid Vertex, Subcase 4a, and Subcase 4b (Chain/Star Bridge) Constructors -/

/-- Cross-pile EFX bound directly from `tildeTau ≤ minM`. -/
private lemma cross_of_tildeTau_le_minM
    {tc nBc Kc mc to_ nBo Ko mo : ℕ} {rc : ℝ}
    (htc : 0 < tc) (hto : 0 < to_) (hrc : 1 < rc) (hKo2 : 2 ≤ Ko)
    (hKc_lo : (Kc : ℝ) - 1 < rc) (hKc_hi : rc ≤ (Kc : ℝ))
    (htilde : tildeTau tc nBc Kc rc mc ≤ (minM to_ nBo Ko mo : ℝ))
    (i : Fin tc) (j : Fin to_) (Lo So : ℕ)
    (htot : Lo + So = pileLarge to_ (mo - nBo) j + pileSmall to_ (mo - nBo) (min mo nBo) Ko j)
    (hSo0 : nBc ≤ mc → So = 0) :
    ownTau rc (pileLarge tc (mc - nBc) i) (pileSmall tc (mc - nBc) (min mc nBc) Kc i) ≤
      ownCost rc Lo So := by
  have htau := ownTau_le_pileTau htc hrc hKc_lo hKc_hi (p := mc - nBc) (s := min mc nBc) i
  have hmin := pileMinSize_le_size hto hKo2 (p := mo - nBo) (s := min mo nBo) j
  have hminR : (minM to_ nBo Ko mo : ℝ) ≤ (Lo : ℝ) + (So : ℝ) := by
    have : minM to_ nBo Ko mo ≤ Lo + So := by unfold minM; omega
    exact_mod_cast this
  unfold ownCost
  by_cases hA : nBc ≤ mc
  · have hS0 : So = 0 := hSo0 hA
    rw [hS0, Nat.cast_zero, add_zero]
    unfold tildeTau tauM at htilde
    rw [ite_eq_left hA] at htilde
    have htau_le : pileTau tc (mc - nBc) (min mc nBc) Kc rc ≤ rc * (minM to_ nBo Ko mo : ℝ) := by
      have := (div_le_iff₀ (by linarith : 0 < rc)).mp htilde
      linarith only [this]
    rw [hS0, Nat.cast_zero, add_zero] at hminR
    nlinarith only [htau, htau_le, hminR, hrc]
  · unfold tildeTau tauM at htilde
    rw [ite_eq_right hA] at htilde
    have hLo_nn : (0 : ℝ) ≤ (Lo : ℝ) := Nat.cast_nonneg Lo
    nlinarith only [htau, htilde, hminR, hLo_nn, hrc]

/-- Construct a `ThreeTypeSpec` directly from a grid vertex `(m0, m1, m2)` where none of the
three conservative envy predicates hold. -/
private lemma threeTypeSpec_of_grid
    {t0 t1 t2 nA nB0 nB1 nB2 K0 K1 K2 m0 m1 m2 : ℕ} {r0 r1 r2 : ℝ}
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hr0 : 1 < r0) (hr1 : 1 < r1) (hr2 : 1 < r2)
    (hK02 : 2 ≤ K0) (hK0_lo : (K0 : ℝ) - 1 < r0) (hK0_hi : r0 ≤ (K0 : ℝ))
    (hK12 : 2 ≤ K1) (hK1_lo : (K1 : ℝ) - 1 < r1) (hK1_hi : r1 ≤ (K1 : ℝ))
    (hK22 : 2 ≤ K2) (hK2_lo : (K2 : ℝ) - 1 < r2) (hK2_hi : r2 ≤ (K2 : ℝ))
    (hsumM : m0 + m1 + m2 = nA + nB0 + nB1 + nB2)
    (hE0 : tildeTau t0 nB0 K0 r0 m0 ≤ min (minM t1 nB1 K1 m1 : ℝ) (minM t2 nB2 K2 m2 : ℝ))
    (hE1 : tildeTau t1 nB1 K1 r1 m1 ≤ min (minM t0 nB0 K0 m0 : ℝ) (minM t2 nB2 K2 m2 : ℝ))
    (hE2 : tildeTau t2 nB2 K2 r2 m2 ≤ min (minM t0 nB0 K0 m0 : ℝ) (minM t1 nB1 K1 m1 : ℝ)) :
    Nonempty (ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2) := by
  have hsumL0 : ∑ i, pileLarge t0 (m0 - nB0) i = m0 - nB0 := sum_pileLarge ht0
  have hsumL1 : ∑ j, pileLarge t1 (m1 - nB1) j = m1 - nB1 := sum_pileLarge ht1
  have hsumL2 : ∑ k, pileLarge t2 (m2 - nB2) k = m2 - nB2 := sum_pileLarge ht2
  have hsumS0 : ∑ i, pileSmall t0 (m0 - nB0) (min m0 nB0) K0 i = min m0 nB0 := sum_pileSmall ht0
  have hsumS1 : ∑ j, pileSmall t1 (m1 - nB1) (min m1 nB1) K1 j = min m1 nB1 := sum_pileSmall ht1
  have hsumS2 : ∑ k, pileSmall t2 (m2 - nB2) (min m2 nB2) K2 k = min m2 nB2 := sum_pileSmall ht2
  have hpool : ∑ i, pileLarge t0 (m0 - nB0) i + ∑ j, pileLarge t1 (m1 - nB1) j +
      ∑ k, pileLarge t2 (m2 - nB2) k = nA + (nB0 - m0) + (nB1 - m1) + (nB2 - m2) := by
    rw [hsumL0, hsumL1, hsumL2]; clear * - hsumM; omega
  obtain ⟨A0, B10, B20, A1, B01, B21, A2, B02, B12,
      hsp0, hsp1, hsp2, hsumA, hsumB0', hsumB1', hsumB2'⟩ :=
    split_shared_pool_3 (pileLarge t0 (m0 - nB0)) (pileLarge t1 (m1 - nB1)) (pileLarge t2 (m2 - nB2)) hpool
      (if h : nB0 ≤ m0 then Or.inl (Nat.sub_eq_zero_of_le h) else Or.inr (by rw [hsumL0]; exact Nat.sub_eq_zero_of_le (le_of_not_ge h)))
      (if h : nB1 ≤ m1 then Or.inl (Nat.sub_eq_zero_of_le h) else Or.inr (by rw [hsumL1]; exact Nat.sub_eq_zero_of_le (le_of_not_ge h)))
      (if h : nB2 ≤ m2 then Or.inl (Nat.sub_eq_zero_of_le h) else Or.inr (by rw [hsumL2]; exact Nat.sub_eq_zero_of_le (le_of_not_ge h)))
  have hB01_zero : nB0 ≤ m0 → ∀ j, B01 j = 0 := fun h j => by
    have hle : B01 j ≤ ∑ x, B01 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hsub : nB0 - m0 = 0 := Nat.sub_eq_zero_of_le h
    clear * - hle hsumB0' hsub; omega
  have hB02_zero : nB0 ≤ m0 → ∀ k, B02 k = 0 := fun h k => by
    have hle : B02 k ≤ ∑ x, B02 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hsub : nB0 - m0 = 0 := Nat.sub_eq_zero_of_le h
    clear * - hle hsumB0' hsub; omega
  have hB10_zero : nB1 ≤ m1 → ∀ i, B10 i = 0 := fun h i => by
    have hle : B10 i ≤ ∑ x, B10 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hsub : nB1 - m1 = 0 := Nat.sub_eq_zero_of_le h
    clear * - hle hsumB1' hsub; omega
  have hB12_zero : nB1 ≤ m1 → ∀ k, B12 k = 0 := fun h k => by
    have hle : B12 k ≤ ∑ x, B12 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hsub : nB1 - m1 = 0 := Nat.sub_eq_zero_of_le h
    clear * - hle hsumB1' hsub; omega
  have hB20_zero : nB2 ≤ m2 → ∀ i, B20 i = 0 := fun h i => by
    have hle : B20 i ≤ ∑ x, B20 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hsub : nB2 - m2 = 0 := Nat.sub_eq_zero_of_le h
    clear * - hle hsumB2' hsub; omega
  have hB21_zero : nB2 ≤ m2 → ∀ j, B21 j = 0 := fun h j => by
    have hle : B21 j ≤ ∑ x, B21 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hsub : nB2 - m2 = 0 := Nat.sub_eq_zero_of_le h
    clear * - hle hsumB2' hsub; omega
  refine ⟨{
    A0 := A0, B00 := pileSmall t0 (m0 - nB0) (min m0 nB0) K0, B10 := B10, B20 := B20
    A1 := A1, B01 := B01, B11 := pileSmall t1 (m1 - nB1) (min m1 nB1) K1, B21 := B21
    A2 := A2, B02 := B02, B12 := B12, B22 := pileSmall t2 (m2 - nB2) (min m2 nB2) K2
    sumA := hsumA
    sumB0 := by rw [hsumS0, add_assoc, hsumB0']; clear * -; omega
    sumB1 := by rw [add_comm (∑ i, B10 i), add_assoc, hsumS1, hsumB1']; clear * -; omega
    sumB2 := by rw [hsumB2', hsumS2]; clear * -; omega
    efx00 := fun i j => by rw [hsp0 i, hsp0 j]; exact identicalPile_internal_efx ht0 hr0 hK0_lo hK0_hi i j
    efx11 := fun i j => by rw [hsp1 i, hsp1 j]; exact identicalPile_internal_efx ht1 hr1 hK1_lo hK1_hi i j
    efx22 := fun i j => by rw [hsp2 i, hsp2 j]; exact identicalPile_internal_efx ht2 hr2 hK2_lo hK2_hi i j
    efx01 := fun i j => by
      rw [hsp0 i]
      exact cross_of_tildeTau_le_minM ht0 ht1 hr0 hK12 hK0_lo hK0_hi
        (le_trans hE0 (min_le_left _ _)) i j (A1 j + pileSmall t1 (m1 - nB1) (min m1 nB1) K1 j + B21 j) (B01 j)
        (by have h := hsp1 j; clear * - h; omega) (fun h => hB01_zero h j)
    efx02 := fun i k => by
      rw [hsp0 i]
      exact cross_of_tildeTau_le_minM ht0 ht2 hr0 hK22 hK0_lo hK0_hi
        (le_trans hE0 (min_le_right _ _)) i k (A2 k + B12 k + pileSmall t2 (m2 - nB2) (min m2 nB2) K2 k) (B02 k)
        (by have h := hsp2 k; clear * - h; omega) (fun h => hB02_zero h k)
    efx10 := fun i j => by
      rw [hsp1 i]
      exact cross_of_tildeTau_le_minM ht1 ht0 hr1 hK02 hK1_lo hK1_hi
        (le_trans hE1 (min_le_left _ _)) i j (A0 j + pileSmall t0 (m0 - nB0) (min m0 nB0) K0 j + B20 j) (B10 j)
        (by have h := hsp0 j; clear * - h; omega) (fun h => hB10_zero h j)
    efx12 := fun i k => by
      rw [hsp1 i]
      exact cross_of_tildeTau_le_minM ht1 ht2 hr1 hK22 hK1_lo hK1_hi
        (le_trans hE1 (min_le_right _ _)) i k (A2 k + B02 k + pileSmall t2 (m2 - nB2) (min m2 nB2) K2 k) (B12 k)
        (by have h := hsp2 k; clear * - h; omega) (fun h => hB12_zero h k)
    efx20 := fun i j => by
      rw [hsp2 i]
      exact cross_of_tildeTau_le_minM ht2 ht0 hr2 hK02 hK2_lo hK2_hi
        (le_trans hE2 (min_le_left _ _)) i j (A0 j + pileSmall t0 (m0 - nB0) (min m0 nB0) K0 j + B10 j) (B20 j)
        (by have h := hsp0 j; clear * - h; omega) (fun h => hB20_zero h j)
    efx21 := fun i j => by
      rw [hsp2 i]
      exact cross_of_tildeTau_le_minM ht2 ht1 hr2 hK12 hK2_lo hK2_hi
        (le_trans hE2 (min_le_right _ _)) i j (A1 j + B01 j + pileSmall t1 (m1 - nB1) (min m1 nB1) K1 j) (B21 j)
        (by have h := hsp1 j; clear * - h; omega) (fun h => hB21_zero h j)
  }⟩

/-- **Subcase 4a (`M₀ = M₁ < M₂`)**: Hold Pile 2 fixed at `m₂` (with `M₂ ≥ M* + 1` and
`tildeTau₂(m₂) < M* + 1`), and run the exact 2-type single-item bridge between Piles 0 and 1! -/
private lemma threeTypeSpec_of_subcase4a
    {t0 t1 t2 nA nB0 nB1 nB2 K0 K1 K2 m0 m1 m2 : ℕ} {r0 r1 r2 : ℝ}
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hr0 : 1 < r0) (hr1 : 1 < r1) (hr2 : 1 < r2)
    (hK02 : 2 ≤ K0) (hK0_lo : (K0 : ℝ) - 1 < r0) (hK0_hi : r0 ≤ (K0 : ℝ))
    (hK12 : 2 ≤ K1) (hK1_lo : (K1 : ℝ) - 1 < r1) (hK1_hi : r1 ≤ (K1 : ℝ))
    (hK22 : 2 ≤ K2) (hK2_lo : (K2 : ℝ) - 1 < r2) (hK2_hi : r2 ≤ (K2 : ℝ))
    (hsumM : m0 + m1 + m2 + 1 = nA + nB0 + nB1 + nB2)
    (hA0 : nB0 ≤ m0) (hA1 : nB1 ≤ m1)
    (hMeq : minM t0 nB0 K0 m0 = minM t1 nB1 K1 m1)
    (hM2gt : minM t0 nB0 K0 m0 < minM t2 nB2 K2 m2)
    (h0_gt : (minM t0 nB0 K0 m0 : ℝ) < tildeTau t0 nB0 K0 r0 (m0 + 1))
    (h1_gt : (minM t0 nB0 K0 m0 : ℝ) < tildeTau t1 nB1 K1 r1 (m1 + 1))
    (h2_lt : tildeTau t2 nB2 K2 r2 m2 < (minM t0 nB0 K0 m0 : ℝ) + 1) :
    Nonempty (ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2) := by
  set a0 := m0 - nB0
  set a1 := m1 - nB1
  set Mstar := minM t0 nB0 K0 m0
  -- Translate into pileTau / pileMinSize form for Piles 0 and 1!
  have hM0_eq : pileMinSize t0 a0 nB0 K0 = Mstar := by
    unfold Mstar minM; rw [Nat.min_eq_right hA0]
  have hM1_eq : pileMinSize t1 a1 nB1 K1 = Mstar := by
    rw [hMeq]; unfold minM; rw [Nat.min_eq_right hA1]
  have htau0_gt : r0 * (Mstar : ℝ) < pileTau t0 (a0 + 1) nB0 K0 r0 := by
    unfold tildeTau tauM at h0_gt
    rw [ite_eq_left (by omega : nB0 ≤ m0 + 1), Nat.min_eq_right (by omega : nB0 ≤ m0 + 1),
        show m0 + 1 - nB0 = a0 + 1 by omega] at h0_gt
    have := (lt_div_iff₀ (by linarith : 0 < r0)).mp h0_gt
    linarith only [this]
  have htau1_gt : r1 * (Mstar : ℝ) < pileTau t1 (a1 + 1) nB1 K1 r1 := by
    unfold tildeTau tauM at h1_gt
    rw [ite_eq_left (by omega : nB1 ≤ m1 + 1), Nat.min_eq_right (by omega : nB1 ≤ m1 + 1),
        show m1 + 1 - nB1 = a1 + 1 by omega] at h1_gt
    have := (lt_div_iff₀ (by linarith : 0 < r1)).mp h1_gt
    linarith only [this]
  -- Shared pool for Pile 0 & Pile 1's large items (plus Pile 2's large items if nB2 ≤ m2):
  -- Total large slots needed across (Pile 0, Pile 1) is (a0 + a1 + 1), and Pile 2 has (m2 - nB2) large slots,
  -- total = nA + (nB2 - m2) = nA + leftover B2!
  -- Apply our ALREADY PROVED 2-type Phase-2 jump bridge on (t0, t1, nA' := a0 + a1 + 1, nB0, nB1)!
  -- Even cleaner: build the 2-type bridge spec between Pile 0 and Pile 1 using exists_twoTypeSpec_phase2_jump
  -- NO: just build it directly in 50 lines using Lemmas A, B, C so we have exact `minSize ≥ Mstar + 1`!
  have hstep0 : pileTau t0 (a0 + 1) nB0 K0 r0 < r0 * ((Mstar : ℝ) + 1) := by
    rw [← hM0_eq]; exact pileTau_step_lt ht0 hr0 hK0_lo hK0_hi
  have hstep1 : pileTau t1 (a1 + 1) nB1 K1 r1 < r1 * ((Mstar : ℝ) + 1) := by
    rw [← hM1_eq]; exact pileTau_step_lt ht1 hr1 hK1_lo hK1_hi
  have hnB0_pos : 1 ≤ nB0 := by
    by_contra h0; have hb : nB0 = 0 := by omega
    have ht := pileTau_step_le_tight (t := t0) (p := a0) (s := nB0) (K := K0) ht0 hr0 hK0_lo hK0_hi (Or.inl hb)
    rw [hM0_eq] at ht; linarith only [htau0_gt, ht]
  have hnB1_pos : 1 ≤ nB1 := by
    by_contra h0; have hb : nB1 = 0 := by omega
    have ht := pileTau_step_le_tight (t := t1) (p := a1) (s := nB1) (K := K1) ht1 hr1 hK1_lo hK1_hi (Or.inl hb)
    rw [hM1_eq] at ht; linarith only [htau1_gt, ht]
  have hMstar_pos : 1 ≤ Mstar := by
    by_contra hM0
    have hMz : pileMinSize t0 a0 nB0 K0 = 0 := by omega
    have hu0_ne0 : a0 % t0 ≠ 0 := by
      intro h0
      have ht := pileTau_step_le_tight (t := t0) (p := a0) (s := nB0) (K := K0) ht0 hr0 hK0_lo hK0_hi (Or.inr (Or.inr h0))
      rw [hM0_eq] at ht; linarith only [htau0_gt, ht]
    have hu0_lt : a0 % t0 < t0 := Nat.mod_lt a0 ht0
    unfold pileMinSize pileMinSizeAux at hMz
    have hle_cap : nB0 ≤ (t0 - a0 % t0) * K0 := by
      by_contra hgt; rw [ite_eq_right hgt, ite_eq_right hu0_ne0] at hMz; split_ifs at hMz
    rw [ite_eq_left hle_cap, ite_eq_right hu0_ne0] at hMz
    have hnB_lt : nB0 < t0 - a0 % t0 := by
      by_contra hge; rw [ite_eq_right hge] at hMz; simp at hMz
    rw [ite_eq_left hnB_lt] at hMz
    have hdm := div_mod_succ_of_lt ht0 (by omega : a0 % t0 + 1 < t0)
    have htu_pos : 0 < t0 - (a0 % t0 + 1) := by omega
    have hnB_le_u1 : nB0 ≤ t0 - (a0 % t0 + 1) := by omega
    have hnB_le1 : nB0 ≤ (t0 - (a0 % t0 + 1)) * K0 :=
      le_trans hnB_le_u1 (Nat.le_mul_of_pos_right _ (by omega))
    have hc1 : ceilDiv nB0 (t0 - (a0 % t0 + 1)) = 1 := by
      have ha := ceilDiv_pos htu_pos (by omega : 0 < nB0)
      have hb := ceilDiv_le_of_le_mul htu_pos (by omega : nB0 ≤ (t0 - (a0 % t0 + 1)) * 1)
      omega
    have htz : pileTau t0 (a0 + 1) nB0 K0 r0 = 0 := by
      unfold pileTau; rw [hdm.1, hdm.2, hMz]; unfold pileTauAux
      rw [ite_eq_left hnB_le1, ite_eq_right (by omega : nB0 ≠ 0), hc1]; simp
    rw [htz, show Mstar = 0 by omega] at htau0_gt; simp at htau0_gt
  have hM0_ge : Mstar + 1 ≤ pileMinSize t0 (a0 + 1) nB0 K0 := by
    have hf := pileTau_le_r_mul_minSize (t := t0) (p := a0 + 1) (s := nB0) (K := K0) ht0 hr0 hK0_lo hK0_hi
    have : (Mstar : ℝ) < (pileMinSize t0 (a0 + 1) nB0 K0 : ℝ) := by nlinarith only [htau0_gt, hf, hr0]
    have : Mstar < pileMinSize t0 (a0 + 1) nB0 K0 := by exact_mod_cast this
    omega
  have hM1_ge : Mstar + 1 ≤ pileMinSize t1 (a1 + 1) nB1 K1 := by
    have hf := pileTau_le_r_mul_minSize (t := t1) (p := a1 + 1) (s := nB1) (K := K1) ht1 hr1 hK1_lo hK1_hi
    have : (Mstar : ℝ) < (pileMinSize t1 (a1 + 1) nB1 K1 : ℝ) := by nlinarith only [htau1_gt, hf, hr1]
    have : Mstar < pileMinSize t1 (a1 + 1) nB1 K1 := by exact_mod_cast this
    omega
  have hB0 : Mstar + 1 ≤ pileMinSize t0 (a0 + 1) (nB0 - 1) K0 :=
    pileMinSize_sub_one_ge ht0 hr0 hK0_lo hK0_hi hnB0_pos htau0_gt
  have hB1 : Mstar + 1 ≤ pileMinSize t1 (a1 + 1) (nB1 - 1) K1 :=
    pileMinSize_sub_one_ge ht1 hr1 hK1_lo hK1_hi hnB1_pos htau1_gt
  have hmono0 : pileTau t0 (a0 + 1) (nB0 - 1) K0 r0 ≤ pileTau t0 (a0 + 1) nB0 K0 r0 :=
    pileTau_mono_s ht0 hr0 hK0_lo hK0_hi (by omega)
  have hmono1 : pileTau t1 (a1 + 1) (nB1 - 1) K1 r1 ≤ pileTau t1 (a1 + 1) nB1 K1 r1 :=
    pileTau_mono_s ht1 hr1 hK1_lo hK1_hi (by omega)
  -- Helper to assemble a ThreeTypeSpec given Pile 0 = (a0+1, s0), Pile 1 = (a1+1, s1), Pile 2 = (m2-nB2, min m2 nB2),
  -- with 1 single cross-item moved from Pile 0→1 (dir=0) or Pile 1→0 (dir=1)!
  -- Because of symmetry swap01, we prove a single helper for direction 0 → 1!
  have hbuild01 :
      ∀ (t0' t1' nB0' nB1' K0' K1' a0' a1' : ℕ) (r0' r1' : ℝ),
        0 < t0' → (ht1' : 0 < t1') → 1 < r0' → 1 < r1' →
        2 ≤ K0' → (K0' : ℝ) - 1 < r0' → r0' ≤ (K0' : ℝ) →
        2 ≤ K1' → (K1' : ℝ) - 1 < r1' → r1' ≤ (K1' : ℝ) →
        1 ≤ nB0' →
        a0' + a1' + (m2 - nB2) + 1 = nA + (nB2 - m2) →
        Mstar + 1 ≤ pileMinSize t0' (a0' + 1) (nB0' - 1) K0' →
        Mstar + 1 ≤ pileMinSize t1' (a1' + 1) nB1' K1' →
        pileTau t0' (a0' + 1) (nB0' - 1) K0' r0' < r0' * ((Mstar : ℝ) + 1) →
        pileTau t1' (a1' + 1) nB1' K1' r1' < r1' * ((Mstar : ℝ) + 1) →
        pileTau t0' (a0' + 1) (nB0' - 1) K0' r0' ≤
          r0' * ((maxLargeSize t1' (a1' + 1) nB1' K1' ht1' - 1 : ℕ) : ℝ) + 1 →
        Nonempty (ThreeTypeSpec t0' t1' t2 nA nB0' nB1' nB2 r0' r1' r2) := by
    intro t0' t1' nB0' nB1' K0' K1' a0' a1' r0' r1' ht0' ht1' hr0' hr1'
      hK02' hK0_lo' hK0_hi' hK12' hK1_lo' hK1_hi' hnB0p hpool_sum
      hM0' hM1' htau0_lt htau1_lt hbridge
    let idx1 : Fin t1' := maxLargeIdx t1' (a1' + 1) nB1' K1' ht1'
    have hidx1_pos : 0 < pileLarge t1' (a1' + 1) idx1 := maxLargeIdx_large_pos ht1' (Nat.succ_pos a1')
    let B01_fn : Fin t1' → ℕ := fun j => if j = idx1 then 1 else 0
    let L1_rem : Fin t1' → ℕ := fun j => if j = idx1 then pileLarge t1' (a1' + 1) j - 1 else pileLarge t1' (a1' + 1) j
    have hL1_eq : ∀ j, L1_rem j + B01_fn j = pileLarge t1' (a1' + 1) j := by
      intro j; simp only [L1_rem, B01_fn]; split_ifs with hj
      · subst hj; omega
      · omega
    have hsumB01 : ∑ j, B01_fn j = 1 := by simp [B01_fn]
    have hsumL1_rem : ∑ j, L1_rem j = a1' := by
      have htot : ∑ j, (L1_rem j + B01_fn j) = a1' + 1 := by simp_rw [hL1_eq]; exact sum_pileLarge ht1'
      rw [Finset.sum_add_distrib, hsumB01] at htot; omega
    -- Split shared pool nA + (nB2 - m2) across L0' = pileLarge(a0'+1), L1_rem (sum a1'), L2' = pileLarge(m2-nB2)!
    have hsp_sum : ∑ i, pileLarge t0' (a0' + 1) i + ∑ j, L1_rem j + ∑ k, pileLarge t2 (m2 - nB2) k =
        nA + 0 + 0 + (nB2 - m2) := by
      rw [sum_pileLarge ht0', hsumL1_rem, sum_pileLarge ht2]; omega
    obtain ⟨A0, B10, B20, A1, B01_z, B21, A2, B02, B12,
        hsp0, hsp1, hsp2, hsumA, hsum0z, hsum1z, hsumB2'⟩ :=
      split_shared_pool_3 (pileLarge t0' (a0' + 1)) L1_rem (pileLarge t2 (m2 - nB2)) hsp_sum
        (Or.inl rfl) (Or.inl rfl)
        (if h : nB2 ≤ m2 then Or.inl (by omega) else Or.inr (by rw [sum_pileLarge ht2]; omega))
    have hB10_z : ∀ i, B10 i = 0 := fun i => by
      have : B10 i ≤ ∑ x, B10 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i); omega
    have hB01_z : ∀ j, B01_z j = 0 := fun j => by
      have : B01_z j ≤ ∑ x, B01_z x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j); omega
    have hB02_z : ∀ k, B02 k = 0 := fun k => by
      have : B02 k ≤ ∑ x, B02 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k); omega
    have hB12_z : ∀ k, B12 k = 0 := fun k => by
      have : B12 k ≤ ∑ x, B12 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k); omega
    have hB20_z : nB2 ≤ m2 → ∀ i, B20 i = 0 := fun h i => by
      have : B20 i ≤ ∑ x, B20 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i); omega
    have hB21_z : nB2 ≤ m2 → ∀ j, B21 j = 0 := fun h j => by
      have : B21 j ≤ ∑ x, B21 x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j); omega
    refine ⟨{
      A0 := A0, B00 := pileSmall t0' (a0' + 1) (nB0' - 1) K0', B10 := fun _ => 0, B20 := B20
      A1 := A1, B01 := B01_fn, B11 := pileSmall t1' (a1' + 1) nB1' K1', B21 := B21
      A2 := A2, B02 := fun _ => 0, B12 := fun _ => 0, B22 := pileSmall t2 (m2 - nB2) (min m2 nB2) K2
      sumA := hsumA
      sumB0 := by rw [sum_pileSmall ht0', hsumB01]; simp; omega
      sumB1 := by simp [sum_pileSmall ht1']
      sumB2 := by rw [sum_pileSmall ht2]; omega
      efx00 := fun i j => by
        have h1 : A0 i + 0 + B20 i = pileLarge t0' (a0' + 1) i := by have := hsp0 i; have := hB10_z i; omega
        have h2 : A0 j + 0 + B20 j = pileLarge t0' (a0' + 1) j := by have := hsp0 j; have := hB10_z j; omega
        rw [h1, h2]; exact identicalPile_internal_efx ht0' hr0' hK0_lo' hK0_hi' i j
      efx11 := fun i j => by
        have h1 : A1 i + B01_fn i + B21 i = pileLarge t1' (a1' + 1) i := by
          have := hsp1 i; have := hB01_z i; have := hL1_eq i; omega
        have h2 : A1 j + B01_fn j + B21 j = pileLarge t1' (a1' + 1) j := by
          have := hsp1 j; have := hB01_z j; have := hL1_eq j; omega
        rw [h1, h2]; exact identicalPile_internal_efx ht1' hr1' hK1_lo' hK1_hi' i j
      efx22 := fun i j => by
        have h1 : A2 i + 0 + 0 = pileLarge t2 (m2 - nB2) i := by
          have := hsp2 i; have := hB02_z i; have := hB12_z i; omega
        have h2 : A2 j + 0 + 0 = pileLarge t2 (m2 - nB2) j := by
          have := hsp2 j; have := hB02_z j; have := hB12_z j; omega
        rw [h1, h2]; exact identicalPile_internal_efx ht2 hr2 hK2_lo hK2_hi i j
      efx01 := fun i j => by
        have h1 : A0 i + 0 + B20 i = pileLarge t0' (a0' + 1) i := by have := hsp0 i; have := hB10_z i; omega
        rw [h1]
        have htau := ownTau_le_pileTau ht0' hr0' hK0_lo' hK0_hi' (p := a0' + 1) (s := nB0' - 1) i
        by_cases hj : j = idx1
        · subst hj
          have hsz : A1 idx1 + pileSmall t1' (a1' + 1) nB1' K1' idx1 + B21 idx1 =
              maxLargeSize t1' (a1' + 1) nB1' K1' ht1' - 1 := by
            unfold maxLargeSize
            have := hsp1 idx1; have := hB01_z idx1; have := hL1_eq idx1
            simp only [B01_fn, ↓reduceIte] at this
            dsimp only [idx1] at *; omega
          have hB1i : B01_fn idx1 = 1 := by simp [B01_fn]
          rw [hsz, hB1i]; unfold ownCost; simp only [Nat.cast_one]
          linarith only [htau, hbridge]
        · have hB1j : B01_fn j = 0 := ite_eq_right hj
          have hsz : Mstar + 1 ≤ A1 j + pileSmall t1' (a1' + 1) nB1' K1' j + B21 j := by
            have := hsp1 j; have := hB01_z j; have := hL1_eq j
            have hmin := pileMinSize_le_size ht1' hK12' (p := a1' + 1) (s := nB1') j
            omega
          have hszR : (Mstar : ℝ) + 1 ≤ ((A1 j + pileSmall t1' (a1' + 1) nB1' K1' j + B21 j : ℕ) : ℝ) := by
            exact_mod_cast hsz
          rw [hB1j]; unfold ownCost; simp only [Nat.cast_zero, add_zero]
          nlinarith only [htau, htau0_lt, hszR, hr0']
      efx02 := fun i k => by
        have h1 : A0 i + 0 + B20 i = pileLarge t0' (a0' + 1) i := by have := hsp0 i; have := hB10_z i; omega
        rw [h1]
        have htau := ownTau_le_pileTau ht0' hr0' hK0_lo' hK0_hi' (p := a0' + 1) (s := nB0' - 1) i
        have hsz : Mstar + 1 ≤ A2 k + pileSmall t2 (m2 - nB2) (min m2 nB2) K2 k := by
          have := hsp2 k; have := hB02_z k; have := hB12_z k
          have hmin := pileMinSize_le_size ht2 hK22 (p := m2 - nB2) (s := min m2 nB2) k
          unfold minM at hM2gt; omega
        have hszR : (Mstar : ℝ) + 1 ≤ ((A2 k + pileSmall t2 (m2 - nB2) (min m2 nB2) K2 k : ℕ) : ℝ) := by
          exact_mod_cast hsz
        unfold ownCost; simp only [add_zero, Nat.cast_zero]
        nlinarith only [htau, htau0_lt, hszR, hr0']
      efx10 := fun i j => by
        have h1 : A1 i + B01_fn i + B21 i = pileLarge t1' (a1' + 1) i := by
          have := hsp1 i; have := hB01_z i; have := hL1_eq i; omega
        rw [h1]
        have htau := ownTau_le_pileTau ht1' hr1' hK1_lo' hK1_hi' (p := a1' + 1) (s := nB1') i
        have hsz : Mstar + 1 ≤ A0 j + pileSmall t0' (a0' + 1) (nB0' - 1) K0' j + B20 j := by
          have := hsp0 j; have := hB10_z j
          have hmin := pileMinSize_le_size ht0' hK02' (p := a0' + 1) (s := nB0' - 1) j
          omega
        have hszR : (Mstar : ℝ) + 1 ≤ ((A0 j + pileSmall t0' (a0' + 1) (nB0' - 1) K0' j + B20 j : ℕ) : ℝ) := by
          exact_mod_cast hsz
        unfold ownCost; simp only [Nat.cast_zero, add_zero]
        nlinarith only [htau, htau1_lt, hszR, hr1']
      efx12 := fun i k => by
        have h1 : A1 i + B01_fn i + B21 i = pileLarge t1' (a1' + 1) i := by
          have := hsp1 i; have := hB01_z i; have := hL1_eq i; omega
        rw [h1]
        have htau := ownTau_le_pileTau ht1' hr1' hK1_lo' hK1_hi' (p := a1' + 1) (s := nB1') i
        have hsz : Mstar + 1 ≤ A2 k + pileSmall t2 (m2 - nB2) (min m2 nB2) K2 k := by
          have := hsp2 k; have := hB02_z k; have := hB12_z k
          have hmin := pileMinSize_le_size ht2 hK22 (p := m2 - nB2) (s := min m2 nB2) k
          unfold minM at hM2gt; omega
        have hszR : (Mstar : ℝ) + 1 ≤ ((A2 k + pileSmall t2 (m2 - nB2) (min m2 nB2) K2 k : ℕ) : ℝ) := by
          exact_mod_cast hsz
        unfold ownCost; simp only [add_zero, Nat.cast_zero]
        nlinarith only [htau, htau1_lt, hszR, hr1']
      efx20 := fun i j => by
        have h1 : A2 i + 0 + 0 = pileLarge t2 (m2 - nB2) i := by
          have := hsp2 i; have := hB02_z i; have := hB12_z i; omega
        rw [h1]
        have htau := ownTau_le_pileTau ht2 hr2 hK2_lo hK2_hi (p := m2 - nB2) (s := min m2 nB2) i
        have hsz : Mstar + 1 ≤ (A0 j + pileSmall t0' (a0' + 1) (nB0' - 1) K0' j + 0) + B20 j := by
          have := hsp0 j; have := hB10_z j
          have hmin := pileMinSize_le_size ht0' hK02' (p := a0' + 1) (s := nB0' - 1) j
          omega
        have hszR : (Mstar : ℝ) + 1 ≤ ((A0 j + pileSmall t0' (a0' + 1) (nB0' - 1) K0' j + 0 : ℕ) : ℝ) + (B20 j : ℝ) := by
          exact_mod_cast hsz
        unfold ownCost tildeTau tauM at *
        by_cases hA2 : nB2 ≤ m2
        · rw [ite_eq_left hA2] at h2_lt
          have h2_mul : pileTau t2 (m2 - nB2) (min m2 nB2) K2 r2 < r2 * ((Mstar : ℝ) + 1) := by
            have := (div_lt_iff₀ (by linarith : 0 < r2)).mp h2_lt; linarith only [this]
          have hB0j : B20 j = 0 := hB20_z hA2 j
          rw [hB0j, Nat.cast_zero, add_zero] at hszR ⊢
          nlinarith only [htau, h2_mul, hszR, hr2]
        · rw [ite_eq_right hA2] at h2_lt
          have hnn : (0 : ℝ) ≤ ((A0 j + pileSmall t0' (a0' + 1) (nB0' - 1) K0' j + 0 : ℕ) : ℝ) := Nat.cast_nonneg _
          nlinarith only [htau, h2_lt, hszR, hnn, hr2]
      efx21 := fun i j => by
        have h1 : A2 i + 0 + 0 = pileLarge t2 (m2 - nB2) i := by
          have := hsp2 i; have := hB02_z i; have := hB12_z i; omega
        rw [h1]
        have htau := ownTau_le_pileTau ht2 hr2 hK2_lo hK2_hi (p := m2 - nB2) (s := min m2 nB2) i
        have hsz : Mstar + 1 ≤ (A1 j + B01_fn j + pileSmall t1' (a1' + 1) nB1' K1' j) + B21 j := by
          have := hsp1 j; have := hB01_z j; have := hL1_eq j
          have hmin := pileMinSize_le_size ht1' hK12' (p := a1' + 1) (s := nB1') j
          omega
        have hszR : (Mstar : ℝ) + 1 ≤ ((A1 j + B01_fn j + pileSmall t1' (a1' + 1) nB1' K1' j : ℕ) : ℝ) + (B21 j : ℝ) := by
          exact_mod_cast hsz
        unfold ownCost tildeTau tauM at *
        by_cases hA2 : nB2 ≤ m2
        · rw [ite_eq_left hA2] at h2_lt
          have h2_mul : pileTau t2 (m2 - nB2) (min m2 nB2) K2 r2 < r2 * ((Mstar : ℝ) + 1) := by
            have := (div_lt_iff₀ (by linarith : 0 < r2)).mp h2_lt; linarith only [this]
          have hB1j : B21 j = 0 := hB21_z hA2 j
          rw [hB1j, Nat.cast_zero, add_zero] at hszR ⊢
          nlinarith only [htau, h2_mul, hszR, hr2]
        · rw [ite_eq_right hA2] at h2_lt
          have hnn : (0 : ℝ) ≤ ((A1 j + B01_fn j + pileSmall t1' (a1' + 1) nB1' K1' j : ℕ) : ℝ) := Nat.cast_nonneg _
          nlinarith only [htau, h2_lt, hszR, hnn, hr2]
    }⟩
  -- Now split on whether 0 → 1 bridge holds, else Lemma C forces 1 → 0 bridge!
  by_cases hbr0 : pileTau t0 (a0 + 1) (nB0 - 1) K0 r0 ≤
      r0 * ((maxLargeSize t1 (a1 + 1) nB1 K1 ht1 - 1 : ℕ) : ℝ) + 1
  · exact hbuild01 t0 t1 nB0 nB1 K0 K1 a0 a1 r0 r1 ht0 ht1 hr0 hr1
      hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi hnB0_pos (by omega)
      hB0 hM1_ge (lt_of_le_of_lt hmono0 hstep0) hstep1 hbr0
  · push Not at hbr0
    have hL1_ge : Mstar + 1 ≤ maxLargeSize t1 (a1 + 1) nB1 K1 ht1 :=
      le_trans hM1_ge (pileMinSize_le_size ht1 hK12 _)
    have htau0_gt1 : r0 * (Mstar : ℝ) + 1 < pileTau t0 (a0 + 1) (nB0 - 1) K0 r0 := by
      have hMR : (Mstar : ℝ) ≤ ((maxLargeSize t1 (a1 + 1) nB1 K1 ht1 - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Mstar ≤ maxLargeSize t1 (a1 + 1) nB1 K1 ht1 - 1)
      nlinarith only [hbr0, hMR, hr0]
    have hL0_ge : Mstar + 2 ≤ maxLargeSize t0 (a0 + 1) nB0 K0 ht0 := by
      by_contra hle
      have hC := pileTau_sub_one_le_of_maxLargeSize (p := a0 + 1) ht0 hr0 hK0_lo hK0_hi hnB0_pos hMstar_pos (by omega)
      linarith only [hC, htau0_gt1]
    have hbr1 : pileTau t1 (a1 + 1) (nB1 - 1) K1 r1 ≤
        r1 * ((maxLargeSize t0 (a0 + 1) nB0 K0 ht0 - 1 : ℕ) : ℝ) + 1 := by
      have hMR : (Mstar : ℝ) + 1 ≤ ((maxLargeSize t0 (a0 + 1) nB0 K0 ht0 - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Mstar + 1 ≤ maxLargeSize t0 (a0 + 1) nB0 K0 ht0 - 1)
      nlinarith only [hmono1, hstep1, hMR, hr1]
    obtain ⟨S⟩ := hbuild01 t1 t0 nB1 nB0 K1 K0 a1 a0 r1 r0 ht1 ht0 hr1 hr0
      hK12 hK1_lo hK1_hi hK02 hK0_lo hK0_hi hnB1_pos (by omega)
      hB1 hM0_ge (lt_of_le_of_lt hmono1 hstep1) hstep0 hbr1
    exact ⟨S.swap01⟩

/-- **2-Step Chain Bridge (`0 → 1 → 2`)** for Subcase 4b when Type 0 is EASY and either
Type 1 is EASY or Type 2 is HARD (`maxLargeSize₂ ≥ M* + 2`). -/
private lemma threeTypeSpec_chain_bridge
    {t0 t1 t2 nA nB0 nB1 nB2 K0 K1 K2 a0 a1 a2 Mstar : ℕ} {r0 r1 r2 : ℝ}
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hr0 : 1 < r0) (hr1 : 1 < r1) (hr2 : 1 < r2)
    (hK02 : 2 ≤ K0) (hK0_lo : (K0 : ℝ) - 1 < r0) (hK0_hi : r0 ≤ (K0 : ℝ))
    (hK12 : 2 ≤ K1) (hK1_lo : (K1 : ℝ) - 1 < r1) (hK1_hi : r1 ≤ (K1 : ℝ))
    (hK22 : 2 ≤ K2) (hK2_lo : (K2 : ℝ) - 1 < r2) (hK2_hi : r2 ≤ (K2 : ℝ))
    (hsumA : a0 + a1 + a2 + 1 = nA)
    (hnB0 : 1 ≤ nB0) (hnB1 : 1 ≤ nB1)
    (hM0 : Mstar + 1 ≤ pileMinSize t0 (a0 + 1) (nB0 - 1) K0)
    (hM1 : Mstar + 1 ≤ pileMinSize t1 (a1 + 1) (nB1 - 1) K1)
    (hM2 : Mstar + 1 ≤ pileMinSize t2 (a2 + 1) nB2 K2)
    (htau0 : pileTau t0 (a0 + 1) (nB0 - 1) K0 r0 < r0 * ((Mstar : ℝ) + 1))
    (htau1 : pileTau t1 (a1 + 1) (nB1 - 1) K1 r1 < r1 * ((Mstar : ℝ) + 1))
    (htau2 : pileTau t2 (a2 + 1) nB2 K2 r2 < r2 * ((Mstar : ℝ) + 1))
    (hbr01 : pileTau t0 (a0 + 1) (nB0 - 1) K0 r0 ≤
      r0 * ((maxLargeSize t1 (a1 + 1) (nB1 - 1) K1 ht1 - 1 : ℕ) : ℝ) + 1)
    (hbr12 : pileTau t1 (a1 + 1) (nB1 - 1) K1 r1 ≤
      r1 * ((maxLargeSize t2 (a2 + 1) nB2 K2 ht2 - 1 : ℕ) : ℝ) + 1) :
    Nonempty (ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2) := by
  let idx1 : Fin t1 := maxLargeIdx t1 (a1 + 1) (nB1 - 1) K1 ht1
  let idx2 : Fin t2 := maxLargeIdx t2 (a2 + 1) nB2 K2 ht2
  have hidx1_pos : 0 < pileLarge t1 (a1 + 1) idx1 := maxLargeIdx_large_pos ht1 (Nat.succ_pos a1)
  have hidx2_pos : 0 < pileLarge t2 (a2 + 1) idx2 := maxLargeIdx_large_pos ht2 (Nat.succ_pos a2)
  let B01_fn : Fin t1 → ℕ := fun j => if j = idx1 then 1 else 0
  let A1_fn : Fin t1 → ℕ := fun j => if j = idx1 then pileLarge t1 (a1 + 1) j - 1 else pileLarge t1 (a1 + 1) j
  let B12_fn : Fin t2 → ℕ := fun k => if k = idx2 then 1 else 0
  let A2_fn : Fin t2 → ℕ := fun k => if k = idx2 then pileLarge t2 (a2 + 1) k - 1 else pileLarge t2 (a2 + 1) k
  have hL1 : ∀ j, A1_fn j + B01_fn j = pileLarge t1 (a1 + 1) j := by
    intro j; simp only [A1_fn, B01_fn]; split_ifs with hj
    · subst hj; omega
    · omega
  have hL2 : ∀ k, A2_fn k + B12_fn k = pileLarge t2 (a2 + 1) k := by
    intro k; simp only [A2_fn, B12_fn]; split_ifs with hk
    · subst hk; omega
    · omega
  have hsumB01 : ∑ j, B01_fn j = 1 := by simp [B01_fn]
  have hsumB12 : ∑ k, B12_fn k = 1 := by simp [B12_fn]
  have hsumA1 : ∑ j, A1_fn j = a1 := by
    have htot : ∑ j, (A1_fn j + B01_fn j) = a1 + 1 := by simp_rw [hL1]; exact sum_pileLarge ht1
    rw [Finset.sum_add_distrib, hsumB01] at htot; omega
  have hsumA2 : ∑ k, A2_fn k = a2 := by
    have htot : ∑ k, (A2_fn k + B12_fn k) = a2 + 1 := by simp_rw [hL2]; exact sum_pileLarge ht2
    rw [Finset.sum_add_distrib, hsumB12] at htot; omega
  refine ⟨{
    A0 := pileLarge t0 (a0 + 1), B00 := pileSmall t0 (a0 + 1) (nB0 - 1) K0, B10 := fun _ => 0, B20 := fun _ => 0
    A1 := A1_fn, B01 := B01_fn, B11 := pileSmall t1 (a1 + 1) (nB1 - 1) K1, B21 := fun _ => 0
    A2 := A2_fn, B02 := fun _ => 0, B12 := B12_fn, B22 := pileSmall t2 (a2 + 1) nB2 K2
    sumA := by rw [sum_pileLarge ht0, hsumA1, hsumA2]; omega
    sumB0 := by rw [sum_pileSmall ht0, hsumB01]; simp; omega
    sumB1 := by rw [sum_pileSmall ht1, hsumB12]; simp; omega
    sumB2 := by simp [sum_pileSmall ht2]
    efx00 := fun i j => by simpa using identicalPile_internal_efx ht0 hr0 hK0_lo hK0_hi i j
    efx11 := fun i j => by
      simp only [add_zero]; rw [hL1 i, hL1 j]
      exact identicalPile_internal_efx ht1 hr1 hK1_lo hK1_hi i j
    efx22 := fun i j => by
      simp only [add_zero]; rw [hL2 i, hL2 j]
      exact identicalPile_internal_efx ht2 hr2 hK2_lo hK2_hi i j
    efx01 := fun i j => by
      simp only [add_zero]
      have htau := ownTau_le_pileTau ht0 hr0 hK0_lo hK0_hi (p := a0 + 1) (s := nB0 - 1) i
      by_cases hj : j = idx1
      · subst hj
        have hsz : A1_fn idx1 + pileSmall t1 (a1 + 1) (nB1 - 1) K1 idx1 =
            maxLargeSize t1 (a1 + 1) (nB1 - 1) K1 ht1 - 1 := by
          unfold maxLargeSize; simp only [A1_fn, ↓reduceIte]; dsimp only [idx1] at *; omega
        have hB : B01_fn idx1 = 1 := by simp [B01_fn]
        rw [hsz, hB]; unfold ownCost; simp only [Nat.cast_one]
        linarith only [htau, hbr01]
      · have hB : B01_fn j = 0 := ite_eq_right hj
        have hA : A1_fn j = pileLarge t1 (a1 + 1) j := ite_eq_right hj
        have hmin := pileMinSize_le_size ht1 hK12 (p := a1 + 1) (s := nB1 - 1) j
        have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t1 (a1 + 1) j + pileSmall t1 (a1 + 1) (nB1 - 1) K1 j : ℕ) : ℝ) := by
          exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t1 (a1 + 1) j + pileSmall t1 (a1 + 1) (nB1 - 1) K1 j)
        rw [hA, hB]; unfold ownCost; simp only [Nat.cast_zero, add_zero]
        nlinarith only [htau, htau0, hszR, hr0]
    efx02 := fun i k => by
      simp only [add_zero]
      have htau := ownTau_le_pileTau ht0 hr0 hK0_lo hK0_hi (p := a0 + 1) (s := nB0 - 1) i
      have hmin := pileMinSize_le_size ht2 hK22 (p := a2 + 1) (s := nB2) k
      have hszR : (Mstar : ℝ) + 1 ≤ ((A2_fn k + B12_fn k + pileSmall t2 (a2 + 1) nB2 K2 k : ℕ) : ℝ) := by
        rw [hL2 k]; exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t2 (a2 + 1) k + pileSmall t2 (a2 + 1) nB2 K2 k)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau0, hszR, hr0]
    efx10 := fun i j => by
      simp only [add_zero]; rw [hL1 i]
      have htau := ownTau_le_pileTau ht1 hr1 hK1_lo hK1_hi (p := a1 + 1) (s := nB1 - 1) i
      have hmin := pileMinSize_le_size ht0 hK02 (p := a0 + 1) (s := nB0 - 1) j
      have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 1) K0 j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 1) K0 j)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau1, hszR, hr1]
    efx12 := fun i k => by
      simp only [add_zero]; rw [hL1 i]
      have htau := ownTau_le_pileTau ht1 hr1 hK1_lo hK1_hi (p := a1 + 1) (s := nB1 - 1) i
      by_cases hk : k = idx2
      · subst hk
        have hsz : A2_fn idx2 + pileSmall t2 (a2 + 1) nB2 K2 idx2 =
            maxLargeSize t2 (a2 + 1) nB2 K2 ht2 - 1 := by
          unfold maxLargeSize; simp only [A2_fn, ↓reduceIte]; dsimp only [idx2] at *; omega
        have hB : B12_fn idx2 = 1 := by simp [B12_fn]
        rw [hsz, hB]; unfold ownCost; simp only [Nat.cast_one]
        linarith only [htau, hbr12]
      · have hB : B12_fn k = 0 := ite_eq_right hk
        have hA : A2_fn k = pileLarge t2 (a2 + 1) k := ite_eq_right hk
        have hmin := pileMinSize_le_size ht2 hK22 (p := a2 + 1) (s := nB2) k
        have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t2 (a2 + 1) k + pileSmall t2 (a2 + 1) nB2 K2 k : ℕ) : ℝ) := by
          exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t2 (a2 + 1) k + pileSmall t2 (a2 + 1) nB2 K2 k)
        rw [hA, hB]; unfold ownCost; simp only [Nat.cast_zero, add_zero]
        nlinarith only [htau, htau1, hszR, hr1]
    efx20 := fun i j => by
      simp only [add_zero]; rw [hL2 i]
      have htau := ownTau_le_pileTau ht2 hr2 hK2_lo hK2_hi (p := a2 + 1) (s := nB2) i
      have hmin := pileMinSize_le_size ht0 hK02 (p := a0 + 1) (s := nB0 - 1) j
      have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 1) K0 j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 1) K0 j)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau2, hszR, hr2]
    efx21 := fun i j => by
      simp only [add_zero]; rw [hL2 i]
      have htau := ownTau_le_pileTau ht2 hr2 hK2_lo hK2_hi (p := a2 + 1) (s := nB2) i
      have hmin := pileMinSize_le_size ht1 hK12 (p := a1 + 1) (s := nB1 - 1) j
      have hszR : (Mstar : ℝ) + 1 ≤ ((A1_fn j + B01_fn j + pileSmall t1 (a1 + 1) (nB1 - 1) K1 j : ℕ) : ℝ) := by
        rw [hL1 j]; exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t1 (a1 + 1) j + pileSmall t1 (a1 + 1) (nB1 - 1) K1 j)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau2, hszR, hr2]
  }⟩

/-- **2-Spoke Star Bridge (`1 ← 0 → 2`)** for Subcase 4b when ALL 3 types are HARD! -/
private lemma threeTypeSpec_star_bridge
    {t0 t1 t2 nA nB0 nB1 nB2 K0 K1 K2 a0 a1 a2 Mstar : ℕ} {r0 r1 r2 : ℝ}
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hr0 : 1 < r0) (hr1 : 1 < r1) (hr2 : 1 < r2)
    (hK02 : 2 ≤ K0) (hK0_lo : (K0 : ℝ) - 1 < r0) (hK0_hi : r0 ≤ (K0 : ℝ))
    (hK12 : 2 ≤ K1) (hK1_lo : (K1 : ℝ) - 1 < r1) (hK1_hi : r1 ≤ (K1 : ℝ))
    (hK22 : 2 ≤ K2) (hK2_lo : (K2 : ℝ) - 1 < r2) (hK2_hi : r2 ≤ (K2 : ℝ))
    (hsumA : a0 + a1 + a2 + 1 = nA)
    (hnB0 : 2 ≤ nB0)
    (hM0 : Mstar + 1 ≤ pileMinSize t0 (a0 + 1) (nB0 - 2) K0)
    (hM1 : Mstar + 1 ≤ pileMinSize t1 (a1 + 1) nB1 K1)
    (hM2 : Mstar + 1 ≤ pileMinSize t2 (a2 + 1) nB2 K2)
    (htau0 : pileTau t0 (a0 + 1) (nB0 - 2) K0 r0 < r0 * ((Mstar : ℝ) + 1))
    (htau1 : pileTau t1 (a1 + 1) nB1 K1 r1 < r1 * ((Mstar : ℝ) + 1))
    (htau2 : pileTau t2 (a2 + 1) nB2 K2 r2 < r2 * ((Mstar : ℝ) + 1))
    (hL1 : Mstar + 2 ≤ maxLargeSize t1 (a1 + 1) nB1 K1 ht1)
    (hL2 : Mstar + 2 ≤ maxLargeSize t2 (a2 + 1) nB2 K2 ht2) :
    Nonempty (ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2) := by
  let idx1 : Fin t1 := maxLargeIdx t1 (a1 + 1) nB1 K1 ht1
  let idx2 : Fin t2 := maxLargeIdx t2 (a2 + 1) nB2 K2 ht2
  have hidx1_pos : 0 < pileLarge t1 (a1 + 1) idx1 := maxLargeIdx_large_pos ht1 (Nat.succ_pos a1)
  have hidx2_pos : 0 < pileLarge t2 (a2 + 1) idx2 := maxLargeIdx_large_pos ht2 (Nat.succ_pos a2)
  let B01_fn : Fin t1 → ℕ := fun j => if j = idx1 then 1 else 0
  let A1_fn : Fin t1 → ℕ := fun j => if j = idx1 then pileLarge t1 (a1 + 1) j - 1 else pileLarge t1 (a1 + 1) j
  let B02_fn : Fin t2 → ℕ := fun k => if k = idx2 then 1 else 0
  let A2_fn : Fin t2 → ℕ := fun k => if k = idx2 then pileLarge t2 (a2 + 1) k - 1 else pileLarge t2 (a2 + 1) k
  have hEq1 : ∀ j, A1_fn j + B01_fn j = pileLarge t1 (a1 + 1) j := by
    intro j; simp only [A1_fn, B01_fn]; split_ifs with hj
    · subst hj; omega
    · omega
  have hEq2 : ∀ k, A2_fn k + B02_fn k = pileLarge t2 (a2 + 1) k := by
    intro k; simp only [A2_fn, B02_fn]; split_ifs with hk
    · subst hk; omega
    · omega
  have hsumB01 : ∑ j, B01_fn j = 1 := by simp [B01_fn]
  have hsumB02 : ∑ k, B02_fn k = 1 := by simp [B02_fn]
  have hsumA1 : ∑ j, A1_fn j = a1 := by
    have htot : ∑ j, (A1_fn j + B01_fn j) = a1 + 1 := by simp_rw [hEq1]; exact sum_pileLarge ht1
    rw [Finset.sum_add_distrib, hsumB01] at htot; omega
  have hsumA2 : ∑ k, A2_fn k = a2 := by
    have htot : ∑ k, (A2_fn k + B02_fn k) = a2 + 1 := by simp_rw [hEq2]; exact sum_pileLarge ht2
    rw [Finset.sum_add_distrib, hsumB02] at htot; omega
  refine ⟨{
    A0 := pileLarge t0 (a0 + 1), B00 := pileSmall t0 (a0 + 1) (nB0 - 2) K0, B10 := fun _ => 0, B20 := fun _ => 0
    A1 := A1_fn, B01 := B01_fn, B11 := pileSmall t1 (a1 + 1) nB1 K1, B21 := fun _ => 0
    A2 := A2_fn, B02 := B02_fn, B12 := fun _ => 0, B22 := pileSmall t2 (a2 + 1) nB2 K2
    sumA := by rw [sum_pileLarge ht0, hsumA1, hsumA2]; omega
    sumB0 := by rw [sum_pileSmall ht0, hsumB01, hsumB02]; omega
    sumB1 := by simp [sum_pileSmall ht1]
    sumB2 := by simp [sum_pileSmall ht2]
    efx00 := fun i j => by simpa using identicalPile_internal_efx ht0 hr0 hK0_lo hK0_hi i j
    efx11 := fun i j => by
      simp only [add_zero]; rw [hEq1 i, hEq1 j]
      exact identicalPile_internal_efx ht1 hr1 hK1_lo hK1_hi i j
    efx22 := fun i j => by
      simp only [add_zero]; rw [hEq2 i, hEq2 j]
      exact identicalPile_internal_efx ht2 hr2 hK2_lo hK2_hi i j
    efx01 := fun i j => by
      simp only [add_zero]
      have htau := ownTau_le_pileTau ht0 hr0 hK0_lo hK0_hi (p := a0 + 1) (s := nB0 - 2) i
      by_cases hj : j = idx1
      · subst hj
        have hsz : A1_fn idx1 + pileSmall t1 (a1 + 1) nB1 K1 idx1 =
            maxLargeSize t1 (a1 + 1) nB1 K1 ht1 - 1 := by
          unfold maxLargeSize; simp only [A1_fn, ↓reduceIte]; dsimp only [idx1] at *; omega
        have hB : B01_fn idx1 = 1 := by simp [B01_fn]
        have hMR : (Mstar : ℝ) + 1 ≤ ((maxLargeSize t1 (a1 + 1) nB1 K1 ht1 - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : Mstar + 1 ≤ maxLargeSize t1 (a1 + 1) nB1 K1 ht1 - 1)
        rw [hsz, hB]; unfold ownCost; simp only [Nat.cast_one]
        nlinarith only [htau, htau0, hMR, hr0]
      · have hB : B01_fn j = 0 := ite_eq_right hj
        have hA : A1_fn j = pileLarge t1 (a1 + 1) j := ite_eq_right hj
        have hmin := pileMinSize_le_size ht1 hK12 (p := a1 + 1) (s := nB1) j
        have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t1 (a1 + 1) j + pileSmall t1 (a1 + 1) nB1 K1 j : ℕ) : ℝ) := by
          exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t1 (a1 + 1) j + pileSmall t1 (a1 + 1) nB1 K1 j)
        rw [hA, hB]; unfold ownCost; simp only [Nat.cast_zero, add_zero]
        nlinarith only [htau, htau0, hszR, hr0]
    efx02 := fun i k => by
      simp only [add_zero]
      have htau := ownTau_le_pileTau ht0 hr0 hK0_lo hK0_hi (p := a0 + 1) (s := nB0 - 2) i
      by_cases hk : k = idx2
      · subst hk
        have hsz : A2_fn idx2 + pileSmall t2 (a2 + 1) nB2 K2 idx2 =
            maxLargeSize t2 (a2 + 1) nB2 K2 ht2 - 1 := by
          unfold maxLargeSize; simp only [A2_fn, ↓reduceIte]; dsimp only [idx2] at *; omega
        have hB : B02_fn idx2 = 1 := by simp [B02_fn]
        have hMR : (Mstar : ℝ) + 1 ≤ ((maxLargeSize t2 (a2 + 1) nB2 K2 ht2 - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : Mstar + 1 ≤ maxLargeSize t2 (a2 + 1) nB2 K2 ht2 - 1)
        rw [hsz, hB]; unfold ownCost; simp only [Nat.cast_one]
        nlinarith only [htau, htau0, hMR, hr0]
      · have hB : B02_fn k = 0 := ite_eq_right hk
        have hA : A2_fn k = pileLarge t2 (a2 + 1) k := ite_eq_right hk
        have hmin := pileMinSize_le_size ht2 hK22 (p := a2 + 1) (s := nB2) k
        have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t2 (a2 + 1) k + pileSmall t2 (a2 + 1) nB2 K2 k : ℕ) : ℝ) := by
          exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t2 (a2 + 1) k + pileSmall t2 (a2 + 1) nB2 K2 k)
        rw [hA, hB]; unfold ownCost; simp only [Nat.cast_zero, add_zero]
        nlinarith only [htau, htau0, hszR, hr0]
    efx10 := fun i j => by
      simp only [add_zero]; rw [hEq1 i]
      have htau := ownTau_le_pileTau ht1 hr1 hK1_lo hK1_hi (p := a1 + 1) (s := nB1) i
      have hmin := pileMinSize_le_size ht0 hK02 (p := a0 + 1) (s := nB0 - 2) j
      have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 2) K0 j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 2) K0 j)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau1, hszR, hr1]
    efx12 := fun i k => by
      simp only [add_zero]; rw [hEq1 i]
      have htau := ownTau_le_pileTau ht1 hr1 hK1_lo hK1_hi (p := a1 + 1) (s := nB1) i
      have hmin := pileMinSize_le_size ht2 hK22 (p := a2 + 1) (s := nB2) k
      have hszR : (Mstar : ℝ) + 1 ≤ ((A2_fn k + B02_fn k + pileSmall t2 (a2 + 1) nB2 K2 k : ℕ) : ℝ) := by
        rw [hEq2 k]; exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t2 (a2 + 1) k + pileSmall t2 (a2 + 1) nB2 K2 k)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau1, hszR, hr1]
    efx20 := fun i j => by
      simp only [add_zero]; rw [hEq2 i]
      have htau := ownTau_le_pileTau ht2 hr2 hK2_lo hK2_hi (p := a2 + 1) (s := nB2) i
      have hmin := pileMinSize_le_size ht0 hK02 (p := a0 + 1) (s := nB0 - 2) j
      have hszR : (Mstar : ℝ) + 1 ≤ ((pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 2) K0 j : ℕ) : ℝ) := by
        exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t0 (a0 + 1) j + pileSmall t0 (a0 + 1) (nB0 - 2) K0 j)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau2, hszR, hr2]
    efx21 := fun i j => by
      simp only [add_zero]; rw [hEq2 i]
      have htau := ownTau_le_pileTau ht2 hr2 hK2_lo hK2_hi (p := a2 + 1) (s := nB2) i
      have hmin := pileMinSize_le_size ht1 hK12 (p := a1 + 1) (s := nB1) j
      have hszR : (Mstar : ℝ) + 1 ≤ ((A1_fn j + B01_fn j + pileSmall t1 (a1 + 1) nB1 K1 j : ℕ) : ℝ) := by
        rw [hEq1 j]; exact_mod_cast (by omega : Mstar + 1 ≤ pileLarge t1 (a1 + 1) j + pileSmall t1 (a1 + 1) nB1 K1 j)
      unfold ownCost; simp only [Nat.cast_zero, add_zero]
      nlinarith only [htau, htau2, hszR, hr2]
  }⟩

/-- **Subcase 4b (`M₀ = M₁ = M₂ = M*`)**: all 3 types are in Case A; resolves via
2-Step Chain Bridge (`≤ 2` HARD types) or 2-Spoke Star Bridge (3 HARD types). -/
private lemma threeTypeSpec_of_subcase4b
    {t0 t1 t2 nA nB0 nB1 nB2 K0 K1 K2 m0 m1 m2 : ℕ} {r0 r1 r2 : ℝ}
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hr0 : 1 < r0) (hr1 : 1 < r1) (hr2 : 1 < r2)
    (hK02 : 2 ≤ K0) (hK0_lo : (K0 : ℝ) - 1 < r0) (hK0_hi : r0 ≤ (K0 : ℝ))
    (hK12 : 2 ≤ K1) (hK1_lo : (K1 : ℝ) - 1 < r1) (hK1_hi : r1 ≤ (K1 : ℝ))
    (hK22 : 2 ≤ K2) (hK2_lo : (K2 : ℝ) - 1 < r2) (hK2_hi : r2 ≤ (K2 : ℝ))
    (hsumM : m0 + m1 + m2 + 1 = nA + nB0 + nB1 + nB2)
    (hA0 : nB0 ≤ m0) (hA1 : nB1 ≤ m1) (hA2 : nB2 ≤ m2)
    (hM01 : minM t0 nB0 K0 m0 = minM t1 nB1 K1 m1)
    (hM02 : minM t0 nB0 K0 m0 = minM t2 nB2 K2 m2)
    (h0_gt : (minM t0 nB0 K0 m0 : ℝ) < tildeTau t0 nB0 K0 r0 (m0 + 1))
    (h1_gt : (minM t0 nB0 K0 m0 : ℝ) < tildeTau t1 nB1 K1 r1 (m1 + 1))
    (h2_gt : (minM t0 nB0 K0 m0 : ℝ) < tildeTau t2 nB2 K2 r2 (m2 + 1)) :
    Nonempty (ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2) := by
  set a0 := m0 - nB0
  set a1 := m1 - nB1
  set a2 := m2 - nB2
  set Mstar := minM t0 nB0 K0 m0
  have hsumA : a0 + a1 + a2 + 1 = nA := by omega
  have hM0_eq : pileMinSize t0 a0 nB0 K0 = Mstar := by unfold Mstar minM; rw [Nat.min_eq_right hA0]
  have hM1_eq : pileMinSize t1 a1 nB1 K1 = Mstar := by rw [hM01]; unfold minM; rw [Nat.min_eq_right hA1]
  have hM2_eq : pileMinSize t2 a2 nB2 K2 = Mstar := by rw [hM02]; unfold minM; rw [Nat.min_eq_right hA2]
  have htau0_gt : r0 * (Mstar : ℝ) < pileTau t0 (a0 + 1) nB0 K0 r0 := by
    unfold tildeTau tauM at h0_gt
    rw [ite_eq_left (by omega : nB0 ≤ m0 + 1), Nat.min_eq_right (by omega : nB0 ≤ m0 + 1),
        show m0 + 1 - nB0 = a0 + 1 by omega] at h0_gt
    have := (lt_div_iff₀ (by linarith : 0 < r0)).mp h0_gt; linarith only [this]
  have htau1_gt : r1 * (Mstar : ℝ) < pileTau t1 (a1 + 1) nB1 K1 r1 := by
    unfold tildeTau tauM at h1_gt
    rw [ite_eq_left (by omega : nB1 ≤ m1 + 1), Nat.min_eq_right (by omega : nB1 ≤ m1 + 1),
        show m1 + 1 - nB1 = a1 + 1 by omega] at h1_gt
    have := (lt_div_iff₀ (by linarith : 0 < r1)).mp h1_gt; linarith only [this]
  have htau2_gt : r2 * (Mstar : ℝ) < pileTau t2 (a2 + 1) nB2 K2 r2 := by
    unfold tildeTau tauM at h2_gt
    rw [ite_eq_left (by omega : nB2 ≤ m2 + 1), Nat.min_eq_right (by omega : nB2 ≤ m2 + 1),
        show m2 + 1 - nB2 = a2 + 1 by omega] at h2_gt
    have := (lt_div_iff₀ (by linarith : 0 < r2)).mp h2_gt; linarith only [this]
  -- Extract uniform properties per pile via one helper!
  have hpile_props : ∀ (t a nB K : ℕ) (r : ℝ),
      0 < t → 1 < r → 2 ≤ K → (K : ℝ) - 1 < r → r ≤ (K : ℝ) →
      pileMinSize t a nB K = Mstar →
      r * (Mstar : ℝ) < pileTau t (a + 1) nB K r →
      1 ≤ nB ∧
      Mstar + 1 ≤ pileMinSize t (a + 1) nB K ∧
      Mstar + 1 ≤ pileMinSize t (a + 1) (nB - 1) K ∧
      pileTau t (a + 1) nB K r < r * ((Mstar : ℝ) + 1) ∧
      pileTau t (a + 1) (nB - 1) K r < r * ((Mstar : ℝ) + 1) := by
    intro t a nB K r ht hr hK2 hK_lo hK_hi hMeq hgt
    have hstep : pileTau t (a + 1) nB K r < r * ((Mstar : ℝ) + 1) := by
      rw [← hMeq]; exact pileTau_step_lt ht hr hK_lo hK_hi
    have hnB_pos : 1 ≤ nB := by
      by_contra h0; have hb : nB = 0 := by omega
      have hti := pileTau_step_le_tight (t := t) (p := a) (s := nB) (K := K) ht hr hK_lo hK_hi (Or.inl hb)
      rw [hMeq] at hti; linarith only [hgt, hti]
    have hMge : Mstar + 1 ≤ pileMinSize t (a + 1) nB K := by
      have hf := pileTau_le_r_mul_minSize (t := t) (p := a + 1) (s := nB) (K := K) ht hr hK_lo hK_hi
      have : (Mstar : ℝ) < (pileMinSize t (a + 1) nB K : ℝ) := by nlinarith only [hgt, hf, hr]
      have : Mstar < pileMinSize t (a + 1) nB K := by exact_mod_cast this
      omega
    have hB := pileMinSize_sub_one_ge ht hr hK_lo hK_hi hnB_pos hgt
    have hmono := pileTau_mono_s (t := t) (p := a + 1) (s₁ := nB - 1) (s₂ := nB) (K := K) ht hr hK_lo hK_hi (by omega)
    exact ⟨hnB_pos, hMge, hB, hstep, lt_of_le_of_lt hmono hstep⟩
  obtain ⟨hnB0, hM0_ge, hB0, hstep0, htau0_sub⟩ := hpile_props t0 a0 nB0 K0 r0 ht0 hr0 hK02 hK0_lo hK0_hi hM0_eq htau0_gt
  obtain ⟨hnB1, hM1_ge, hB1, hstep1, htau1_sub⟩ := hpile_props t1 a1 nB1 K1 r1 ht1 hr1 hK12 hK1_lo hK1_hi hM1_eq htau1_gt
  obtain ⟨hnB2, hM2_ge, hB2, hstep2, htau2_sub⟩ := hpile_props t2 a2 nB2 K2 r2 ht2 hr2 hK22 hK2_lo hK2_hi hM2_eq htau2_gt
  have hMstar_pos : 1 ≤ Mstar := by
    by_contra hM0
    have hMz : pileMinSize t0 a0 nB0 K0 = 0 := by omega
    have hu0_ne0 : a0 % t0 ≠ 0 := by
      intro h0
      have ht := pileTau_step_le_tight (t := t0) (p := a0) (s := nB0) (K := K0) ht0 hr0 hK0_lo hK0_hi (Or.inr (Or.inr h0))
      rw [hM0_eq] at ht; linarith only [htau0_gt, ht]
    have hu0_lt : a0 % t0 < t0 := Nat.mod_lt a0 ht0
    unfold pileMinSize pileMinSizeAux at hMz
    have hle_cap : nB0 ≤ (t0 - a0 % t0) * K0 := by
      by_contra hgt; rw [ite_eq_right hgt, ite_eq_right hu0_ne0] at hMz; split_ifs at hMz
    rw [ite_eq_left hle_cap, ite_eq_right hu0_ne0] at hMz
    have hnB_lt : nB0 < t0 - a0 % t0 := by
      by_contra hge; rw [ite_eq_right hge] at hMz; simp at hMz
    rw [ite_eq_left hnB_lt] at hMz
    have hdm := div_mod_succ_of_lt ht0 (by omega : a0 % t0 + 1 < t0)
    have htu_pos : 0 < t0 - (a0 % t0 + 1) := by omega
    have hnB_le_u1 : nB0 ≤ t0 - (a0 % t0 + 1) := by omega
    have hnB_le1 : nB0 ≤ (t0 - (a0 % t0 + 1)) * K0 :=
      le_trans hnB_le_u1 (Nat.le_mul_of_pos_right _ (by omega))
    have hc1 : ceilDiv nB0 (t0 - (a0 % t0 + 1)) = 1 := by
      have ha := ceilDiv_pos htu_pos (by omega : 0 < nB0)
      have hb := ceilDiv_le_of_le_mul htu_pos (by omega : nB0 ≤ (t0 - (a0 % t0 + 1)) * 1)
      omega
    have htz : pileTau t0 (a0 + 1) nB0 K0 r0 = 0 := by
      unfold pileTau; rw [hdm.1, hdm.2, hMz]; unfold pileTauAux
      rw [ite_eq_left hnB_le1, ite_eq_right (by omega : nB0 ≠ 0), hc1]; simp
    rw [htz, show Mstar = 0 by omega] at htau0_gt; simp at htau0_gt
  -- Helper for HARD properties:
  have hHARD_props : ∀ (t a nB K : ℕ) (r : ℝ) (ht : 0 < t),
      1 < r → 2 ≤ K → (K : ℝ) - 1 < r → r ≤ (K : ℝ) →
      1 ≤ nB → pileMinSize t a nB K = Mstar →
      r * (Mstar : ℝ) + 1 < pileTau t (a + 1) (nB - 1) K r →
      Mstar + 2 ≤ maxLargeSize t (a + 1) nB K ht ∧
      2 ≤ nB ∧
      Mstar + 1 ≤ pileMinSize t (a + 1) (nB - 2) K ∧
      pileTau t (a + 1) (nB - 2) K r < r * ((Mstar : ℝ) + 1) := by
    intro t a nB K r ht hr hK2 hK_lo hK_hi hnB hMeq hhard
    have hL : Mstar + 2 ≤ maxLargeSize t (a + 1) nB K ht := by
      by_contra hle
      have hC := pileTau_sub_one_le_of_maxLargeSize (p := a + 1) ht hr hK_lo hK_hi hnB hMstar_pos (by omega)
      linarith only [hC, hhard]
    have hnB2 : 2 ≤ nB := by
      by_contra hlt
      have hb1 : nB = 1 := by omega
      have h0 := pileTau_succ_zero_le_mul_minSize (t := t) (p := a) (K := K) ht hr hK2
      rw [hb1] at hMeq hhard
      rw [hMeq] at h0; simp only [Nat.sub_self] at hhard
      linarith only [h0, hhard]
    have hgt1 : r * (Mstar : ℝ) < pileTau t (a + 1) (nB - 1) K r := by linarith only [hhard]
    have hB2' : Mstar + 1 ≤ pileMinSize t (a + 1) (nB - 2) K := by
      have h := pileMinSize_sub_one_ge ht hr hK_lo hK_hi (by omega : 1 ≤ nB - 1) hgt1
      have heq : nB - 1 - 1 = nB - 2 := by omega
      rw [heq] at h; exact h
    have hstep : pileTau t (a + 1) nB K r < r * ((Mstar : ℝ) + 1) := by
      rw [← hMeq]; exact pileTau_step_lt ht hr hK_lo hK_hi
    have hmono := pileTau_mono_s (t := t) (p := a + 1) (s₁ := nB - 2) (s₂ := nB) (K := K) ht hr hK_lo hK_hi (by omega)
    exact ⟨hL, hnB2, hB2', lt_of_le_of_lt hmono hstep⟩
  -- Helper: EASY implies hbr to ANY pile with minSize ≥ Mstar + 1!
  have hEASY_br : ∀ (t a nB K t' p' s' K' : ℕ) (r : ℝ) (ht' : 0 < t'),
      1 < r → 2 ≤ K' →
      Mstar + 1 ≤ pileMinSize t' p' s' K' →
      pileTau t (a + 1) (nB - 1) K r ≤ r * (Mstar : ℝ) + 1 →
      pileTau t (a + 1) (nB - 1) K r ≤ r * ((maxLargeSize t' p' s' K' ht' - 1 : ℕ) : ℝ) + 1 := by
    intro t a nB K t' p' s' K' r ht' hr hK2' hM' heasy
    have hL' : Mstar + 1 ≤ maxLargeSize t' p' s' K' ht' :=
      le_trans hM' (pileMinSize_le_size ht' hK2' _)
    have hMR : (Mstar : ℝ) ≤ ((maxLargeSize t' p' s' K' ht' - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : Mstar ≤ maxLargeSize t' p' s' K' ht' - 1)
    nlinarith only [heasy, hMR, hr]
  -- Helper: target HARD (L_max ≥ M* + 2) implies hbr from ANY pile with tau < r*(M* + 1)!
  have hHARD_br : ∀ (t a nB K t' p' s' K' : ℕ) (r : ℝ) (ht' : 0 < t'),
      1 < r →
      pileTau t (a + 1) (nB - 1) K r < r * ((Mstar : ℝ) + 1) →
      Mstar + 2 ≤ maxLargeSize t' p' s' K' ht' →
      pileTau t (a + 1) (nB - 1) K r ≤ r * ((maxLargeSize t' p' s' K' ht' - 1 : ℕ) : ℝ) + 1 := by
    intro t a nB K t' p' s' K' r ht' hr htau hL'
    have hMR : (Mstar : ℝ) + 1 ≤ ((maxLargeSize t' p' s' K' ht' - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : Mstar + 1 ≤ maxLargeSize t' p' s' K' ht' - 1)
    nlinarith only [htau, hMR, hr]
  -- Case split on EASY vs HARD for the 3 types!
  by_cases hE0 : pileTau t0 (a0 + 1) (nB0 - 1) K0 r0 ≤ r0 * (Mstar : ℝ) + 1
  · by_cases hE1 : pileTau t1 (a1 + 1) (nB1 - 1) K1 r1 ≤ r1 * (Mstar : ℝ) + 1
    · -- Chain 0 → 1 → 2 (0 EASY, 1 EASY)!
      exact threeTypeSpec_chain_bridge ht0 ht1 ht2 hr0 hr1 hr2 hK02 hK0_lo hK0_hi
        hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi hsumA hnB0 hnB1 hB0 hB1 hM2_ge
        htau0_sub htau1_sub hstep2
        (hEASY_br _ _ _ _ _ _ _ _ _ ht1 hr0 hK12 hB1 hE0)
        (hEASY_br _ _ _ _ _ _ _ _ _ ht2 hr1 hK22 hM2_ge hE1)
    · by_cases hE2 : pileTau t2 (a2 + 1) (nB2 - 1) K2 r2 ≤ r2 * (Mstar : ℝ) + 1
      · -- 0 EASY, 2 EASY, 1 HARD → Chain 0 → 2 → 1 (via swap 1↔2 = rot ∘ swap01 ∘ rot²)!
        -- Even simpler: Chain 2 → 0 → 1 (both 2 and 0 EASY!) via `rot`!
        obtain ⟨S⟩ := threeTypeSpec_chain_bridge (nA := nA) ht2 ht0 ht1 hr2 hr0 hr1 hK22 hK2_lo hK2_hi
          hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi (by omega) hnB2 hnB0 hB2 hB0 hM1_ge
          htau2_sub htau0_sub hstep1
          (hEASY_br _ _ _ _ _ _ _ _ _ ht0 hr2 hK02 hB0 hE2)
          (hEASY_br _ _ _ _ _ _ _ _ _ ht1 hr0 hK12 hM1_ge hE0)
        exact ⟨S.rot.rot⟩
      · -- 0 EASY, 1 HARD, 2 HARD → Chain 0 → 1 → 2 (2 is HARD so L_max₂ ≥ M* + 2)!
        push Not at hE2
        obtain ⟨hL2, _, _, _⟩ := hHARD_props t2 a2 nB2 K2 r2 ht2 hr2 hK22 hK2_lo hK2_hi hnB2 hM2_eq hE2
        exact threeTypeSpec_chain_bridge ht0 ht1 ht2 hr0 hr1 hr2 hK02 hK0_lo hK0_hi
          hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi hsumA hnB0 hnB1 hB0 hB1 hM2_ge
          htau0_sub htau1_sub hstep2
          (hEASY_br _ _ _ _ _ _ _ _ _ ht1 hr0 hK12 hB1 hE0)
          (hHARD_br _ _ _ _ _ _ _ _ _ ht2 hr1 htau1_sub hL2)
  · push Not at hE0
    obtain ⟨hL0, hnB0_2, hB0_2, htau0_2⟩ := hHARD_props t0 a0 nB0 K0 r0 ht0 hr0 hK02 hK0_lo hK0_hi hnB0 hM0_eq hE0
    by_cases hE1 : pileTau t1 (a1 + 1) (nB1 - 1) K1 r1 ≤ r1 * (Mstar : ℝ) + 1
    · -- 1 EASY, 0 HARD → Chain 1 → 2 → 0 (via `rot`, since 0 is HARD so L_max₀ ≥ M* + 2)!
      obtain ⟨S⟩ := threeTypeSpec_chain_bridge (nA := nA) ht1 ht2 ht0 hr1 hr2 hr0 hK12 hK1_lo hK1_hi
        hK22 hK2_lo hK2_hi hK02 hK0_lo hK0_hi (by omega) hnB1 hnB2 hB1 hB2 hM0_ge
        htau1_sub htau2_sub hstep0
        (hEASY_br _ _ _ _ _ _ _ _ _ ht2 hr1 hK22 hB2 hE1)
        (hHARD_br _ _ _ _ _ _ _ _ _ ht0 hr2 htau2_sub hL0)
      exact ⟨S.rot⟩
    · push Not at hE1
      obtain ⟨hL1, _, _, _⟩ := hHARD_props t1 a1 nB1 K1 r1 ht1 hr1 hK12 hK1_lo hK1_hi hnB1 hM1_eq hE1
      by_cases hE2 : pileTau t2 (a2 + 1) (nB2 - 1) K2 r2 ≤ r2 * (Mstar : ℝ) + 1
      · -- 2 EASY, 0 HARD, 1 HARD → Chain 2 → 0 → 1 (via `rot.rot`, since 1 is HARD)!
        obtain ⟨S⟩ := threeTypeSpec_chain_bridge (nA := nA) ht2 ht0 ht1 hr2 hr0 hr1 hK22 hK2_lo hK2_hi
          hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi (by omega) hnB2 hnB0 hB2 hB0 hM1_ge
          htau2_sub htau0_sub hstep1
          (hEASY_br _ _ _ _ _ _ _ _ _ ht0 hr2 hK02 hB0 hE2)
          (hHARD_br _ _ _ _ _ _ _ _ _ ht1 hr0 htau0_sub hL1)
        exact ⟨S.rot.rot⟩
      · -- ALL 3 HARD → 2-Spoke Star Bridge 1 ← 0 → 2!
        push Not at hE2
        obtain ⟨hL2, _, _, _⟩ := hHARD_props t2 a2 nB2 K2 r2 ht2 hr2 hK22 hK2_lo hK2_hi hnB2 hM2_eq hE2
        exact threeTypeSpec_star_bridge ht0 ht1 ht2 hr0 hr1 hr2 hK02 hK0_lo hK0_hi
          hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi hsumA hnB0_2 hB0_2 hM1_ge hM2_ge
          htau0_2 hstep1 hstep2 hL1 hL2

/-! ### Part 5: Main 3-Type Combinatorial Existence via 2D Sperner's Lemma -/

/-- **Main 3-Type Combinatorial Theorem**: for all `t₀, t₁, t₂ ≥ 1`, all chore counts
`(nA, nB₀, nB₁, nB₂)`, and arbitrary personalized ratios `r₀, r₁, r₂ > 1`, a `ThreeTypeSpec` exists. -/
theorem exists_threeTypeSpec {t0 t1 t2 nA nB0 nB1 nB2 : ℕ} {r0 r1 r2 : ℝ}
    (ht0 : 0 < t0) (ht1 : 0 < t1) (ht2 : 0 < t2)
    (hr0 : 1 < r0) (hr1 : 1 < r1) (hr2 : 1 < r2) :
    Nonempty (ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2) := by
  obtain ⟨K0, hK02, hK0_lo, hK0_hi⟩ := exists_ceil_gt_one hr0
  obtain ⟨K1, hK12, hK1_lo, hK1_hi⟩ := exists_ceil_gt_one hr1
  obtain ⟨K2, hK22, hK2_lo, hK2_hi⟩ := exists_ceil_gt_one hr2
  set N := nA + nB0 + nB1 + nB2
  by_cases hN0 : N = 0
  · -- Zero chores: trivial empty specification!
    have h0 : nA = 0 ∧ nB0 = 0 ∧ nB1 = 0 ∧ nB2 = 0 := by omega
    refine ⟨{
      A0 := fun _ => 0, B00 := fun _ => 0, B10 := fun _ => 0, B20 := fun _ => 0
      A1 := fun _ => 0, B01 := fun _ => 0, B11 := fun _ => 0, B21 := fun _ => 0
      A2 := fun _ => 0, B02 := fun _ => 0, B12 := fun _ => 0, B22 := fun _ => 0
      sumA := by simp [h0.1]
      sumB0 := by simp [h0.2.1]
      sumB1 := by simp [h0.2.2.1]
      sumB2 := by simp [h0.2.2.2]
      efx00 := fun _ _ => by simp [ownTau, ownCost]
      efx01 := fun _ _ => by simp [ownTau, ownCost]
      efx02 := fun _ _ => by simp [ownTau, ownCost]
      efx10 := fun _ _ => by simp [ownTau, ownCost]
      efx11 := fun _ _ => by simp [ownTau, ownCost]
      efx12 := fun _ _ => by simp [ownTau, ownCost]
      efx20 := fun _ _ => by simp [ownTau, ownCost]
      efx21 := fun _ _ => by simp [ownTau, ownCost]
      efx22 := fun _ _ => by simp [ownTau, ownCost]
    }⟩
  have hN_pos : 1 ≤ N := by omega
  let T0 := tildeTau t0 nB0 K0 r0
  let T1 := tildeTau t1 nB1 K1 r1
  let T2 := tildeTau t2 nB2 K2 r2
  let M0 := minM t0 nB0 K0
  let M1 := minM t1 nB1 K1
  let M2 := minM t2 nB2 K2
  let E0 (a b : ℕ) : Prop := min (M1 b : ℝ) (M2 (N - a - b) : ℝ) < T0 a
  let E1 (a b : ℕ) : Prop := min (M0 a : ℝ) (M2 (N - a - b) : ℝ) < T1 b
  let E2 (a b : ℕ) : Prop := min (M0 a : ℝ) (M1 b : ℝ) < T2 (N - a - b)
  -- Check if ANY grid vertex is directly non-envious!
  by_cases hgrid : ∃ a b, a + b ≤ N ∧ ¬ E0 a b ∧ ¬ E1 a b ∧ ¬ E2 a b
  · rcases hgrid with ⟨a, b, hab, h0, h1, h2⟩
    dsimp only [E0, E1, E2] at h0 h1 h2; push Not at h0 h1 h2
    exact threeTypeSpec_of_grid ht0 ht1 ht2 hr0 hr1 hr2
      hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi
      (by omega : a + b + (N - a - b) = N) h0 h1 h2
  -- Otherwise, every vertex (a, b) with a + b ≤ N has E0 ∨ E1 ∨ E2!
  push Not at hgrid
  have hall : ∀ a b, a + b ≤ N → E0 a b ∨ E1 a b ∨ E2 a b := by
    intro a b hab
    by_contra hnone; push Not at hnone
    exact hnone.2.2 (hgrid a b hab hnone.1 hnone.2.1)
  -- Define Sperner 3-coloring breaking ties by maximum tildeTau!
  classical
  let col : ℕ → ℕ → Fin 3 := fun a b =>
    if E0 a b ∧ (¬ E1 a b ∨ T1 b ≤ T0 a) ∧ (¬ E2 a b ∨ T2 (N - a - b) ≤ T0 a) then 0
    else if E1 a b ∧ (¬ E2 a b ∨ T2 (N - a - b) ≤ T1 b) then 1
    else 2
  have hcol0 : ∀ a b, a + b ≤ N → col a b = 0 →
      E0 a b ∧ (E1 a b → T1 b ≤ T0 a) ∧ (E2 a b → T2 (N - a - b) ≤ T0 a) := by
    intro a b _ hc
    simp only [col] at hc
    split_ifs at hc with h1 h2
    · exact ⟨h1.1, fun he => h1.2.1.resolve_left (not_not.mpr he),
             fun he => h1.2.2.resolve_left (not_not.mpr he)⟩
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
  have hcol1 : ∀ a b, a + b ≤ N → col a b = 1 →
      E1 a b ∧ (E0 a b → T0 a ≤ T1 b) ∧ (E2 a b → T2 (N - a - b) ≤ T1 b) := by
    intro a b _ hc
    simp only [col] at hc
    split_ifs at hc with h1 h2
    · exact absurd hc (by decide)
    · refine ⟨h2.1, fun he0 => ?_, fun he2 => h2.2.resolve_left (not_not.mpr he2)⟩
      by_contra hlt; push Not at hlt
      apply h1
      refine ⟨he0, Or.inr (le_of_lt hlt), ?_⟩
      by_cases he2 : E2 a b
      · exact Or.inr (le_trans (h2.2.resolve_left (not_not.mpr he2)) (le_of_lt hlt))
      · exact Or.inl he2
    · exact absurd hc (by decide)
  have hcol2 : ∀ a b, a + b ≤ N → col a b = 2 →
      E2 a b ∧ (E0 a b → T0 a ≤ T2 (N - a - b)) ∧ (E1 a b → T1 b ≤ T2 (N - a - b)) := by
    intro a b hab hc
    simp only [col] at hc
    split_ifs at hc with h1 h2
    · exact absurd hc (by decide)
    · exact absurd hc (by decide)
    · have he2 : E2 a b := by
        by_contra hne2
        rcases hall a b hab with he0 | he1 | he2'
        · by_cases he1 : E1 a b
          · by_cases hle : T1 b ≤ T0 a
            · exact h1 ⟨he0, Or.inr hle, Or.inl hne2⟩
            · exact h2 ⟨he1, Or.inl hne2⟩
          · exact h1 ⟨he0, Or.inl he1, Or.inl hne2⟩
        · exact h2 ⟨he1, Or.inl hne2⟩
        · exact hne2 he2'
      refine ⟨he2, fun he0 => ?_, fun he1 => ?_⟩
      · by_contra hlt; push Not at hlt
        by_cases he1 : E1 a b
        · by_cases hle : T1 b ≤ T0 a
          · exact h1 ⟨he0, Or.inr hle, Or.inr (le_of_lt hlt)⟩
          · exact h2 ⟨he1, Or.inr (by linarith only [hlt, hle])⟩
        · exact h1 ⟨he0, Or.inl he1, Or.inr (le_of_lt hlt)⟩
      · by_contra hlt; push Not at hlt
        exact h2 ⟨he1, Or.inr (le_of_lt hlt)⟩
  -- Verify Sperner boundary conditions automatically from tildeTau_zero!
  have hb0 : ∀ b ≤ N, col 0 b ≠ 0 := by
    intro b hb hc
    have he := (hcol0 0 b (by omega) hc).1
    dsimp only [E0, T0] at he; rw [tildeTau_zero] at he
    have hnn : (0 : ℝ) ≤ min (M1 b : ℝ) (M2 (N - 0 - b) : ℝ) :=
      le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith only [he, hnn]
  have hb1 : ∀ a ≤ N, col a 0 ≠ 1 := by
    intro a ha hc
    have he := (hcol1 a 0 (by omega) hc).1
    dsimp only [E1, T1] at he; rw [tildeTau_zero] at he
    have hnn : (0 : ℝ) ≤ min (M0 a : ℝ) (M2 (N - a - 0) : ℝ) :=
      le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith only [he, hnn]
  have hb2 : ∀ a b, a + b = N → col a b ≠ 2 := by
    intro a b hab hc
    have he := (hcol2 a b (by omega) hc).1
    dsimp only [E2, T2] at he
    have hsub : N - a - b = 0 := by omega
    rw [hsub, tildeTau_zero] at he
    have hnn : (0 : ℝ) ≤ min (M0 a : ℝ) (M1 b : ℝ) :=
      le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith only [he, hnn]
  -- Apply 2D Discrete Sperner's Lemma!
  rcases sperner_2d hN_pos col hb0 hb1 hb2 with ⟨a, b, hab, hrain⟩ | ⟨a, b, hab, hrain⟩
  · -- RAINBOW UP-TRIANGLE: v0 = (a+1, b, c), v1 = (a, b+1, c), v2 = (a, b, c+1) where c = N - 1 - a - b!
    set c := N - 1 - a - b
    have hsum_abc : a + b + c + 1 = N := by omega
    have hsub0 : N - (a + 1) - b = c := by omega
    have hsub1 : N - a - (b + 1) = c := by omega
    have hsub2 : N - a - b = c + 1 := by omega
    -- Shortcuts for tildeTau bounds on (a, b, c)
    have hT0_le : T0 a ≤ (M0 a : ℝ) := tildeTau_le_minM ht0 hr0 hK02 hK0_lo hK0_hi
    have hT0_les : T0 a ≤ (M0 (a + 1) : ℝ) := tildeTau_le_minM_succ ht0 hr0 hK02 hK0_lo hK0_hi
    have hT0_lt : T0 (a + 1) < (M0 a : ℝ) + 1 := tildeTau_succ_lt ht0 hr0 hK02 hK0_lo hK0_hi
    have hT1_le : T1 b ≤ (M1 b : ℝ) := tildeTau_le_minM ht1 hr1 hK12 hK1_lo hK1_hi
    have hT1_les : T1 b ≤ (M1 (b + 1) : ℝ) := tildeTau_le_minM_succ ht1 hr1 hK12 hK1_lo hK1_hi
    have hT1_lt : T1 (b + 1) < (M1 b : ℝ) + 1 := tildeTau_succ_lt ht1 hr1 hK12 hK1_lo hK1_hi
    have hT2_le : T2 c ≤ (M2 c : ℝ) := tildeTau_le_minM ht2 hr2 hK22 hK2_lo hK2_hi
    have hT2_les : T2 c ≤ (M2 (c + 1) : ℝ) := tildeTau_le_minM_succ ht2 hr2 hK22 hK2_lo hK2_hi
    have hT2_lt : T2 (c + 1) < (M2 c : ℝ) + 1 := tildeTau_succ_lt ht2 hr2 hK22 hK2_lo hK2_hi
    -- Helper: extract E-inequality from col at each of the 3 vertices!
    generalize hc0 : col (a + 1) b = k0 at hrain
    generalize hc1 : col a (b + 1) = k1 at hrain
    generalize hc2 : col a b = k2 at hrain
    -- Rule out all 5 non-identity permutations and solve identity (0, 1, 2)!
    fin_cases k0 <;> fin_cases k1 <;> fin_cases k2
    all_goals try (exfalso; revert hrain; decide)
    · -- IDENTITY (0, 1, 2)!
      have h0 := hcol0 (a + 1) b (by omega) hc0
      have h1 := hcol1 a (b + 1) (by omega) hc1
      have h2 := hcol2 a b (by omega) hc2
      have h0e : min (M1 b : ℝ) (M2 c : ℝ) < T0 (a + 1) := by simpa [E0, hsub0] using h0.1
      have h1e : min (M0 a : ℝ) (M2 c : ℝ) < T1 (b + 1) := by simpa [E1, hsub1] using h1.1
      have h2e : min (M0 a : ℝ) (M1 b : ℝ) < T2 (c + 1) := by simpa [E2, hsub2] using h2.1
      -- Helper: if M_i = min(M0, M1, M2) = M*, then type i must be in Case A!
      have hcaseA0 : M0 a ≤ M1 b → M0 a ≤ M2 c → nB0 ≤ a := by
        intro hle1 hle2; by_contra hlt
        have h := tildeTau_succ_le_of_lt (t := t0) (nB := nB0) (K := K0) (m := a) (r := r0) ht0 hr0 hK02 (by omega)
        have h1R : (M0 a : ℝ) ≤ (M1 b : ℝ) := by exact_mod_cast hle1
        have h2R : (M0 a : ℝ) ≤ (M2 c : ℝ) := by exact_mod_cast hle2
        have hmin : (M0 a : ℝ) ≤ min (M1 b : ℝ) (M2 c : ℝ) := le_min h1R h2R
        linarith only [h, h0e, hmin]
      have hcaseA1 : M1 b ≤ M0 a → M1 b ≤ M2 c → nB1 ≤ b := by
        intro hle0 hle2; by_contra hlt
        have h := tildeTau_succ_le_of_lt (t := t1) (nB := nB1) (K := K1) (m := b) (r := r1) ht1 hr1 hK12 (by omega)
        have h0R : (M1 b : ℝ) ≤ (M0 a : ℝ) := by exact_mod_cast hle0
        have h2R : (M1 b : ℝ) ≤ (M2 c : ℝ) := by exact_mod_cast hle2
        have hmin : (M1 b : ℝ) ≤ min (M0 a : ℝ) (M2 c : ℝ) := le_min h0R h2R
        linarith only [h, h1e, hmin]
      have hcaseA2 : M2 c ≤ M0 a → M2 c ≤ M1 b → nB2 ≤ c := by
        intro hle0 hle1; by_contra hlt
        have h := tildeTau_succ_le_of_lt (t := t2) (nB := nB2) (K := K2) (m := c) (r := r2) ht2 hr2 hK22 (by omega)
        have h0R : (M2 c : ℝ) ≤ (M0 a : ℝ) := by exact_mod_cast hle0
        have h1R : (M2 c : ℝ) ≤ (M1 b : ℝ) := by exact_mod_cast hle1
        have hmin : (M2 c : ℝ) ≤ min (M0 a : ℝ) (M1 b : ℝ) := le_min h0R h1R
        linarith only [h, h2e, hmin]
      -- Helper: at least two of (M0 a, M1 b, M2 c) equal the minimum!
      have hmin_pair : (M0 a = M1 b ∧ M0 a ≤ M2 c) ∨ (M1 b = M2 c ∧ M1 b ≤ M0 a) ∨ (M2 c = M0 a ∧ M2 c ≤ M1 b) := by
        -- From h0e & hT0_lt: min(M1, M2) < M0 + 1 → min(M1, M2) ≤ M0
        have hm0 : min (M1 b) (M2 c) ≤ M0 a := by
          have : (min (M1 b) (M2 c) : ℝ) < (M0 a : ℝ) + 1 := by
            linarith only [h0e, hT0_lt]
          have : min (M1 b) (M2 c) < M0 a + 1 := by exact_mod_cast this
          omega
        have hm1 : min (M0 a) (M2 c) ≤ M1 b := by
          have : (min (M0 a) (M2 c) : ℝ) < (M1 b : ℝ) + 1 := by
            linarith only [h1e, hT1_lt]
          have : min (M0 a) (M2 c) < M1 b + 1 := by exact_mod_cast this
          omega
        have hm2 : min (M0 a) (M1 b) ≤ M2 c := by
          have : (min (M0 a) (M1 b) : ℝ) < (M2 c : ℝ) + 1 := by
            linarith only [h2e, hT2_lt]
          have : min (M0 a) (M1 b) < M2 c + 1 := by exact_mod_cast this
          omega
        omega
      rcases hmin_pair with ⟨heq01, hle02⟩ | ⟨heq12, hle10⟩ | ⟨heq20, hle21⟩
      · -- M0 a = M1 b ≤ M2 c!
        have hA0 := hcaseA0 (le_of_eq heq01) hle02
        have hA1 := hcaseA1 (le_of_eq heq01.symm) (by omega)
        have h0gt : (M0 a : ℝ) < T0 (a + 1) := by
          have h1R : (M0 a : ℝ) ≤ (M1 b : ℝ) := by exact_mod_cast (le_of_eq heq01)
          have h2R : (M0 a : ℝ) ≤ (M2 c : ℝ) := by exact_mod_cast hle02
          exact lt_of_le_of_lt (le_min h1R h2R) h0e
        have h1gt : (M0 a : ℝ) < T1 (b + 1) := by
          have h2R : (M0 a : ℝ) ≤ (M2 c : ℝ) := by exact_mod_cast hle02
          exact lt_of_le_of_lt (le_min (le_refl _) h2R) h1e
        by_cases hlt02 : M0 a < M2 c
        · -- Subcase 4a: M0 = M1 < M2! Tie-breaking at v0 gives T2 c < M0 a + 1!
          have h2lt : T2 c < (M0 a : ℝ) + 1 := by
            by_cases he2v0 : E2 (a + 1) b
            · have hle := h0.2.2 he2v0
              rw [hsub0] at hle; linarith only [hle, hT0_lt]
            · dsimp only [E2] at he2v0; rw [hsub0] at he2v0; push Not at he2v0
              have hle : T2 c ≤ (M1 b : ℝ) := le_trans he2v0 (min_le_right _ _)
              have h1R : (M1 b : ℝ) = (M0 a : ℝ) := by exact_mod_cast heq01.symm
              linarith only [hle, h1R]
          exact threeTypeSpec_of_subcase4a ht0 ht1 ht2 hr0 hr1 hr2
            hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi
            hsum_abc hA0 hA1 heq01 hlt02 h0gt h1gt h2lt
        · -- Subcase 4b: M0 = M1 = M2!
          have heq02 : M0 a = M2 c := by omega
          have hA2 := hcaseA2 (le_of_eq heq02.symm) (by omega)
          have h2gt : (M0 a : ℝ) < T2 (c + 1) := by
            have h1R : (M0 a : ℝ) ≤ (M1 b : ℝ) := by exact_mod_cast (le_of_eq heq01)
            exact lt_of_le_of_lt (le_min (le_refl _) h1R) h2e
          exact threeTypeSpec_of_subcase4b ht0 ht1 ht2 hr0 hr1 hr2
            hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi
            hsum_abc hA0 hA1 hA2 heq01 heq02 h0gt h1gt h2gt
      · -- M1 b = M2 c ≤ M0 a → rotate via `rot`!
        have hA1 := hcaseA1 hle10 (le_of_eq heq12)
        have hA2 := hcaseA2 (by omega) (le_of_eq heq12.symm)
        have h1gt : (M1 b : ℝ) < T1 (b + 1) := by
          have h0R : (M1 b : ℝ) ≤ (M0 a : ℝ) := by exact_mod_cast hle10
          have h2R : (M1 b : ℝ) ≤ (M2 c : ℝ) := by exact_mod_cast (le_of_eq heq12)
          exact lt_of_le_of_lt (le_min h0R h2R) h1e
        have h2gt : (M1 b : ℝ) < T2 (c + 1) := by
          have h0R : (M1 b : ℝ) ≤ (M0 a : ℝ) := by exact_mod_cast hle10
          exact lt_of_le_of_lt (le_min h0R (le_refl _)) h2e
        by_cases hlt10 : M1 b < M0 a
        · have h0lt : T0 a < (M1 b : ℝ) + 1 := by
            by_cases he0v1 : E0 a (b + 1)
            · have hle := h1.2.1 he0v1; linarith only [hle, hT1_lt]
            · dsimp only [E0] at he0v1; rw [hsub1] at he0v1; push Not at he0v1
              have hle : T0 a ≤ (M2 c : ℝ) := le_trans he0v1 (min_le_right _ _)
              have h2R : (M2 c : ℝ) = (M1 b : ℝ) := by exact_mod_cast heq12.symm
              linarith only [hle, h2R]
          obtain ⟨S⟩ := threeTypeSpec_of_subcase4a (nA := nA) (nB0 := nB1) (nB1 := nB2) (nB2 := nB0)
            ht1 ht2 ht0 hr1 hr2 hr0
            hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi hK02 hK0_lo hK0_hi
            (by omega) hA1 hA2 heq12 hlt10 h1gt h2gt h0lt
          exact ⟨S.rot⟩
        · have heq10 : M1 b = M0 a := by omega
          have hA0 := hcaseA0 (le_of_eq heq10.symm) (by omega)
          have h0gt : (M1 b : ℝ) < T0 (a + 1) := by
            have h2R : (M1 b : ℝ) ≤ (M2 c : ℝ) := by exact_mod_cast (le_of_eq heq12)
            exact lt_of_le_of_lt (le_min (le_refl _) h2R) h0e
          obtain ⟨S⟩ := threeTypeSpec_of_subcase4b (nA := nA) (nB0 := nB1) (nB1 := nB2) (nB2 := nB0)
            ht1 ht2 ht0 hr1 hr2 hr0
            hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi hK02 hK0_lo hK0_hi
            (by omega) hA1 hA2 hA0 heq12 heq10 h1gt h2gt h0gt
          exact ⟨S.rot⟩
      · -- M2 c = M0 a ≤ M1 b → rotate via `rot.rot`!
        have hA2 := hcaseA2 (le_of_eq heq20) hle21
        have hA0 := hcaseA0 (by omega) (le_of_eq heq20.symm)
        have h2gt : (M2 c : ℝ) < T2 (c + 1) := by
          have h0R : (M2 c : ℝ) ≤ (M0 a : ℝ) := by exact_mod_cast (le_of_eq heq20)
          have h1R : (M2 c : ℝ) ≤ (M1 b : ℝ) := by exact_mod_cast hle21
          exact lt_of_le_of_lt (le_min h0R h1R) h2e
        have h0gt : (M2 c : ℝ) < T0 (a + 1) := by
          have h1R : (M2 c : ℝ) ≤ (M1 b : ℝ) := by exact_mod_cast hle21
          exact lt_of_le_of_lt (le_min h1R (le_refl _)) h0e
        by_cases hlt21 : M2 c < M1 b
        · have h1lt : T1 b < (M2 c : ℝ) + 1 := by
            by_cases he1v2 : E1 a b
            · have hle := h2.2.2 he1v2; rw [hsub2] at hle; linarith only [hle, hT2_lt]
            · dsimp only [E1] at he1v2; rw [hsub2] at he1v2; push Not at he1v2
              have hle : T1 b ≤ (M0 a : ℝ) := le_trans he1v2 (min_le_left _ _)
              have h0R : (M0 a : ℝ) = (M2 c : ℝ) := by exact_mod_cast heq20.symm
              linarith only [hle, h0R]
          obtain ⟨S⟩ := threeTypeSpec_of_subcase4a (nA := nA) (nB0 := nB2) (nB1 := nB0) (nB2 := nB1)
            ht2 ht0 ht1 hr2 hr0 hr1
            hK22 hK2_lo hK2_hi hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi
            (by omega) hA2 hA0 heq20 hlt21 h2gt h0gt h1lt
          exact ⟨S.rot.rot⟩
        · have heq21 : M2 c = M1 b := by omega
          have hA1 := hcaseA1 (by omega) (le_of_eq heq21.symm)
          have h1gt : (M2 c : ℝ) < T1 (b + 1) := by
            have h0R : (M2 c : ℝ) ≤ (M0 a : ℝ) := by exact_mod_cast (le_of_eq heq20)
            exact lt_of_le_of_lt (le_min h0R (le_refl _)) h1e
          obtain ⟨S⟩ := threeTypeSpec_of_subcase4b (nA := nA) (nB0 := nB2) (nB1 := nB0) (nB2 := nB1)
            ht2 ht0 ht1 hr2 hr0 hr1
            hK22 hK2_lo hK2_hi hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi
            (by omega) hA2 hA0 hA1 heq20 heq21 h2gt h0gt h1gt
          exact ⟨S.rot.rot⟩
    · -- Transposition (0, 2, 1): v0=(a+1,b,c) col 0, v1=(a,b+1,c) col 2, v2=(a,b,c+1) col 1!
      exfalso
      have h0e : min (M1 b : ℝ) (M2 c : ℝ) < T0 (a + 1) := by simpa [E0, hsub0] using (hcol0 (a+1) b (by omega) hc0).1
      have h1e : min (M0 a : ℝ) (M1 (b + 1) : ℝ) < T2 c := by simpa [E2, hsub1] using (hcol2 a (b+1) (by omega) hc1).1
      have h2e : min (M0 a : ℝ) (M2 (c + 1) : ℝ) < T1 b := by simpa [E1, hsub2] using (hcol1 a b (by omega) hc2).1
      have hM0_lt_M2 : M0 a < M2 c ∨ M1 (b + 1) < M2 c := by
        have hlt := lt_of_lt_of_le h1e hT2_le
        rcases le_total (M0 a : ℝ) (M1 (b + 1) : ℝ) with h | h
        · rw [min_eq_left h] at hlt; left; exact_mod_cast hlt
        · rw [min_eq_right h] at hlt; right; exact_mod_cast hlt
      have hM0_lt_M1 : M0 a < M1 b ∨ M2 (c + 1) < M1 b := by
        have hlt := lt_of_lt_of_le h2e hT1_le
        rcases le_total (M0 a : ℝ) (M2 (c + 1) : ℝ) with h | h
        · rw [min_eq_left h] at hlt; left; exact_mod_cast hlt
        · rw [min_eq_right h] at hlt; right; exact_mod_cast hlt
      have h1s : (min (M0 a : ℝ) (M1 (b + 1) : ℝ)) < (M2 (c + 1) : ℝ) := lt_of_lt_of_le h1e hT2_les
      have h2s : (min (M0 a : ℝ) (M2 (c + 1) : ℝ)) < (M1 (b + 1) : ℝ) := lt_of_lt_of_le h2e hT1_les
      have hM0_strict : M0 a < M1 b ∧ M0 a < M2 c := by
        have h0lt1 : (M0 a : ℝ) < (M1 b : ℝ) := by
          by_contra hge; push Not at hge
          have hlt2 : (M2 (c + 1) : ℝ) < (M1 b : ℝ) := by
            rcases lt_or_ge (M0 a : ℝ) (M2 (c + 1) : ℝ) with h | h
            · linarith only [h, hge, h2e, hT1_le, min_eq_left (le_of_lt h)]
            · rw [min_eq_right h] at h2e; exact lt_of_lt_of_le h2e hT1_le
          have hlt2' : (M2 (c + 1) : ℝ) < (M1 (b + 1) : ℝ) := by
            rcases le_total (M0 a : ℝ) (M2 (c + 1) : ℝ) with h | h
            · linarith only [h, hge, h2e, hT1_le, min_eq_left h]
            · rw [min_eq_right h] at h2s; exact h2s
          rcases le_total (M0 a : ℝ) (M1 (b + 1) : ℝ) with h | h
          · rw [min_eq_left h] at h1s; linarith only [h1s, hge, hlt2]
          · rw [min_eq_right h] at h1s; linarith only [h1s, hlt2']
        have h0lt2 : (M0 a : ℝ) < (M2 c : ℝ) := by
          by_contra hge; push Not at hge
          have hlt1 : (M1 (b + 1) : ℝ) < (M2 c : ℝ) := by
            rcases le_total (M0 a : ℝ) (M1 (b + 1) : ℝ) with h | h
            · linarith only [h, hge, h1e, hT2_le, min_eq_left h]
            · rw [min_eq_right h] at h1e; exact lt_of_lt_of_le h1e hT2_le
          have hlt1' : (M1 (b + 1) : ℝ) < (M2 (c + 1) : ℝ) := by
            rcases le_total (M0 a : ℝ) (M1 (b + 1) : ℝ) with h | h
            · linarith only [h, hge, h1e, hT2_le, min_eq_left h]
            · rw [min_eq_right h] at h1s; exact h1s
          rcases le_total (M0 a : ℝ) (M2 (c + 1) : ℝ) with h | h
          · rw [min_eq_left h] at h2s; linarith only [h2s, hge, hlt1]
          · rw [min_eq_right h] at h2s; linarith only [h2s, hlt1']
        exact ⟨by exact_mod_cast h0lt1, by exact_mod_cast h0lt2⟩
      have hmin_ge : (M0 a : ℝ) + 1 ≤ min (M1 b : ℝ) (M2 c : ℝ) := by
        have : M0 a + 1 ≤ min (M1 b) (M2 c) := by omega
        have hR : ((M0 a + 1 : ℕ) : ℝ) ≤ (min (M1 b) (M2 c) : ℝ) := by exact_mod_cast this
        push_cast at hR; exact hR
      linarith only [hmin_ge, h0e, hT0_lt]
    · -- Transposition (1, 0, 2): v0=(a+1,b,c) col 1, v1=(a,b+1,c) col 0, v2=(a,b,c+1) col 2!
      exfalso
      have h0e : min (M0 (a + 1) : ℝ) (M2 c : ℝ) < T1 b := by simpa [E1, hsub0] using (hcol1 (a+1) b (by omega) hc0).1
      have h1e : min (M1 (b + 1) : ℝ) (M2 c : ℝ) < T0 a := by simpa [E0, hsub1] using (hcol0 a (b+1) (by omega) hc1).1
      have h2e : min (M0 a : ℝ) (M1 b : ℝ) < T2 (c + 1) := by simpa [E2, hsub2] using (hcol2 a b (by omega) hc2).1
      have h0s : min (M0 (a + 1) : ℝ) (M2 c : ℝ) < (M1 (b + 1) : ℝ) := lt_of_lt_of_le h0e hT1_les
      have h1s : min (M1 (b + 1) : ℝ) (M2 c : ℝ) < (M0 (a + 1) : ℝ) := lt_of_lt_of_le h1e hT0_les
      have hM2_lt : M2 c < M0 a ∧ M2 c < M1 b := by
        have h2lt0 : (M2 c : ℝ) < (M0 a : ℝ) := by
          by_contra hge; push Not at hge
          have hlt1 : (M1 (b + 1) : ℝ) < (M0 a : ℝ) := by
            rcases le_total (M1 (b + 1) : ℝ) (M2 c : ℝ) with h | h
            · rw [min_eq_left h] at h1e; exact lt_of_lt_of_le h1e hT0_le
            · linarith only [h, hge, h1e, hT0_le, min_eq_right h]
          have hlt1' : (M1 (b + 1) : ℝ) < (M0 (a + 1) : ℝ) := by
            rcases le_total (M1 (b + 1) : ℝ) (M2 c : ℝ) with h | h
            · rw [min_eq_left h] at h1s; exact h1s
            · linarith only [h, hge, h1e, hT0_le, min_eq_right h]
          rcases le_total (M0 (a + 1) : ℝ) (M2 c : ℝ) with h | h
          · rw [min_eq_left h] at h0s; linarith only [h0s, hlt1']
          · rw [min_eq_right h] at h0s; linarith only [h0s, hge, hlt1]
        have h2lt1 : (M2 c : ℝ) < (M1 b : ℝ) := by
          by_contra hge; push Not at hge
          have hlt0 : (M0 (a + 1) : ℝ) < (M1 b : ℝ) := by
            rcases le_total (M0 (a + 1) : ℝ) (M2 c : ℝ) with h | h
            · rw [min_eq_left h] at h0e; exact lt_of_lt_of_le h0e hT1_le
            · linarith only [h, hge, h0e, hT1_le, min_eq_right h]
          have hlt0' : (M0 (a + 1) : ℝ) < (M1 (b + 1) : ℝ) := by
            rcases le_total (M0 (a + 1) : ℝ) (M2 c : ℝ) with h | h
            · rw [min_eq_left h] at h0s; exact h0s
            · linarith only [h, hge, h0e, hT1_le, min_eq_right h]
          rcases le_total (M1 (b + 1) : ℝ) (M2 c : ℝ) with h | h
          · rw [min_eq_left h] at h1s; linarith only [h1s, hlt0']
          · rw [min_eq_right h] at h1s; linarith only [h1s, hge, hlt0]
        exact ⟨by exact_mod_cast h2lt0, by exact_mod_cast h2lt1⟩
      have hmin_ge : (M2 c : ℝ) + 1 ≤ min (M0 a : ℝ) (M1 b : ℝ) := by
        have : M2 c + 1 ≤ min (M0 a) (M1 b) := by omega
        have hR : ((M2 c + 1 : ℕ) : ℝ) ≤ (min (M0 a) (M1 b) : ℝ) := by exact_mod_cast this
        push_cast at hR; exact hR
      linarith only [hmin_ge, h2e, hT2_lt]
    · -- 3-cycle (1, 2, 0): v0 col 1, v1 col 2, v2 col 0!
      exfalso
      have h0e : min (M0 (a + 1) : ℝ) (M2 c : ℝ) < T1 b := by simpa [E1, hsub0] using (hcol1 (a+1) b (by omega) hc0).1
      have h1e : min (M0 a : ℝ) (M1 (b + 1) : ℝ) < T2 c := by simpa [E2, hsub1] using (hcol2 a (b+1) (by omega) hc1).1
      have h2e : min (M1 b : ℝ) (M2 (c + 1) : ℝ) < T0 a := by simpa [E0, hsub2] using (hcol0 a b (by omega) hc2).1
      set x0 : ℝ := min (M0 a : ℝ) (M0 (a + 1) : ℝ)
      set x1 : ℝ := min (M1 b : ℝ) (M1 (b + 1) : ℝ)
      set x2 : ℝ := min (M2 c : ℝ) (M2 (c + 1) : ℝ)
      have hx0_ge : T0 a ≤ x0 := le_min hT0_le hT0_les
      have hx1_ge : T1 b ≤ x1 := le_min hT1_le hT1_les
      have hx2_ge : T2 c ≤ x2 := le_min hT2_le hT2_les
      have hA : min x0 x2 < x1 := lt_of_le_of_lt (min_le_min (min_le_right _ _) (min_le_left _ _)) (lt_of_lt_of_le h0e hx1_ge)
      have hB : min x0 x1 < x2 := lt_of_le_of_lt (min_le_min (min_le_left _ _) (min_le_right _ _)) (lt_of_lt_of_le h1e hx2_ge)
      have hC : min x1 x2 < x0 := lt_of_le_of_lt (min_le_min (min_le_left _ _) (min_le_right _ _)) (lt_of_lt_of_le h2e hx0_ge)
      rcases le_total x0 x1 with h01 | h10
      · rcases le_total x0 x2 with h02 | h20
        · rw [min_eq_left h02] at hA; rw [min_eq_left h01] at hB
          rcases le_total x1 x2 with h12 | h21
          · rw [min_eq_left h12] at hC; linarith only [hA, hC]
          · rw [min_eq_right h21] at hC; linarith only [hB, hC]
        · rw [min_eq_right h20] at hA; rw [min_eq_right (le_trans h20 h01)] at hC
          rw [min_eq_left h01] at hB; linarith only [h20, hB]
      · rcases le_total x1 x2 with h12 | h21
        · rw [min_eq_right h10] at hB; rw [min_eq_left h12] at hC
          rcases le_total x0 x2 with h02 | h20
          · rw [min_eq_left h02] at hA; linarith only [hC, hA]
          · rw [min_eq_right h20] at hA; linarith only [hB, hA]
        · rw [min_eq_right h21] at hC; rw [min_eq_right (le_trans h21 h10)] at hA
          rw [min_eq_right h10] at hB; linarith only [h21, hB]
    · -- 3-cycle (2, 0, 1): v0 col 2, v1 col 0, v2 col 1!
      exfalso
      have h0e : min (M0 (a + 1) : ℝ) (M1 b : ℝ) < T2 c := by simpa [E2, hsub0] using (hcol2 (a+1) b (by omega) hc0).1
      have h1e : min (M1 (b + 1) : ℝ) (M2 c : ℝ) < T0 a := by simpa [E0, hsub1] using (hcol0 a (b+1) (by omega) hc1).1
      have h2e : min (M0 a : ℝ) (M2 (c + 1) : ℝ) < T1 b := by simpa [E1, hsub2] using (hcol1 a b (by omega) hc2).1
      set x0 : ℝ := min (M0 a : ℝ) (M0 (a + 1) : ℝ)
      set x1 : ℝ := min (M1 b : ℝ) (M1 (b + 1) : ℝ)
      set x2 : ℝ := min (M2 c : ℝ) (M2 (c + 1) : ℝ)
      have hx0_ge : T0 a ≤ x0 := le_min hT0_le hT0_les
      have hx1_ge : T1 b ≤ x1 := le_min hT1_le hT1_les
      have hx2_ge : T2 c ≤ x2 := le_min hT2_le hT2_les
      have hA : min x0 x1 < x2 := lt_of_le_of_lt (min_le_min (min_le_right _ _) (min_le_left _ _)) (lt_of_lt_of_le h0e hx2_ge)
      have hB : min x1 x2 < x0 := lt_of_le_of_lt (min_le_min (min_le_right _ _) (min_le_left _ _)) (lt_of_lt_of_le h1e hx0_ge)
      have hC : min x0 x2 < x1 := lt_of_le_of_lt (min_le_min (min_le_left _ _) (min_le_right _ _)) (lt_of_lt_of_le h2e hx1_ge)
      rcases le_total x0 x1 with h01 | h10
      · rcases le_total x0 x2 with h02 | h20
        · rw [min_eq_left h01] at hA; rw [min_eq_left h02] at hC
          rcases le_total x1 x2 with h12 | h21
          · rw [min_eq_left h12] at hB; linarith only [hC, hB]
          · rw [min_eq_right h21] at hB; linarith only [hA, hB]
        · rw [min_eq_right h20] at hC; rw [min_eq_right (le_trans h20 h01)] at hB
          rw [min_eq_left h01] at hA; linarith only [h20, hA]
      · rcases le_total x1 x2 with h12 | h21
        · rw [min_eq_right h10] at hA; rw [min_eq_left h12] at hB
          rcases le_total x0 x2 with h02 | h20
          · rw [min_eq_left h02] at hC; linarith only [hB, hC]
          · rw [min_eq_right h20] at hC; linarith only [hA, hC]
        · rw [min_eq_right h21] at hB; rw [min_eq_right (le_trans h21 h10)] at hC
          rw [min_eq_right h10] at hA; linarith only [h21, hA]
    · -- Transposition (2, 1, 0): v0=(a+1,b,c) col 2, v1=(a,b+1,c) col 1, v2=(a,b,c+1) col 0!
      exfalso
      have h0e : min (M0 (a + 1) : ℝ) (M1 b : ℝ) < T2 c := by simpa [E2, hsub0] using (hcol2 (a+1) b (by omega) hc0).1
      have h1e : min (M0 a : ℝ) (M2 c : ℝ) < T1 (b + 1) := by simpa [E1, hsub1] using (hcol1 a (b+1) (by omega) hc1).1
      have h2e : min (M1 b : ℝ) (M2 (c + 1) : ℝ) < T0 a := by simpa [E0, hsub2] using (hcol0 a b (by omega) hc2).1
      have h0s : min (M0 (a + 1) : ℝ) (M1 b : ℝ) < (M2 (c + 1) : ℝ) := lt_of_lt_of_le h0e hT2_les
      have h2s : min (M1 b : ℝ) (M2 (c + 1) : ℝ) < (M0 (a + 1) : ℝ) := lt_of_lt_of_le h2e hT0_les
      have hM1_lt : M1 b < M0 a ∧ M1 b < M2 c := by
        have h1lt0 : (M1 b : ℝ) < (M0 a : ℝ) := by
          by_contra hge; push Not at hge
          have hlt2 : (M2 (c + 1) : ℝ) < (M0 a : ℝ) := by
            rcases le_total (M1 b : ℝ) (M2 (c + 1) : ℝ) with h | h
            · linarith only [h, hge, h2e, hT0_le, min_eq_left h]
            · rw [min_eq_right h] at h2e; exact lt_of_lt_of_le h2e hT0_le
          have hlt2' : (M2 (c + 1) : ℝ) < (M0 (a + 1) : ℝ) := by
            rcases le_total (M1 b : ℝ) (M2 (c + 1) : ℝ) with h | h
            · linarith only [h, hge, h2e, hT0_le, min_eq_left h]
            · rw [min_eq_right h] at h2s; exact h2s
          rcases le_total (M0 (a + 1) : ℝ) (M1 b : ℝ) with h | h
          · rw [min_eq_left h] at h0s; linarith only [h0s, hlt2']
          · rw [min_eq_right h] at h0s; linarith only [h0s, hge, hlt2]
        have h1lt2 : (M1 b : ℝ) < (M2 c : ℝ) := by
          by_contra hge; push Not at hge
          have hlt0 : (M0 (a + 1) : ℝ) < (M2 c : ℝ) := by
            rcases le_total (M0 (a + 1) : ℝ) (M1 b : ℝ) with h | h
            · rw [min_eq_left h] at h0e; exact lt_of_lt_of_le h0e hT2_le
            · linarith only [h, hge, h0e, hT2_le, min_eq_right h]
          have hlt0' : (M0 (a + 1) : ℝ) < (M2 (c + 1) : ℝ) := by
            rcases le_total (M0 (a + 1) : ℝ) (M1 b : ℝ) with h | h
            · rw [min_eq_left h] at h0s; exact h0s
            · linarith only [h, hge, h0e, hT2_le, min_eq_right h]
          rcases le_total (M1 b : ℝ) (M2 (c + 1) : ℝ) with h | h
          · rw [min_eq_left h] at h2s; linarith only [h2s, hge, hlt0]
          · rw [min_eq_right h] at h2s; linarith only [h2s, hlt0']
        exact ⟨by exact_mod_cast h1lt0, by exact_mod_cast h1lt2⟩
      have hmin_ge : (M1 b : ℝ) + 1 ≤ min (M0 a : ℝ) (M2 c : ℝ) := by
        have : M1 b + 1 ≤ min (M0 a) (M2 c) := by omega
        have hR : ((M1 b + 1 : ℕ) : ℝ) ≤ (min (M0 a) (M2 c) : ℝ) := by exact_mod_cast this
        push_cast at hR; exact hR
      linarith only [hmin_ge, h1e, hT1_lt]
  · -- RAINBOW DOWN-TRIANGLE:
    -- Vertices: u0 = (a, b+1, c+1), u1 = (a+1, b, c+1), u2 = (a+1, b+1, c) where c = N - 2 - a - b!
    set c := N - 2 - a - b
    have hsum_abc : a + b + c + 2 = N := by omega
    have hsub0 : N - a - (b + 1) = c + 1 := by omega
    have hsub1 : N - (a + 1) - b = c + 1 := by omega
    have hsub2 : N - (a + 1) - (b + 1) = c := by omega
    have hT0_le : T0 a ≤ (M0 a : ℝ) := tildeTau_le_minM ht0 hr0 hK02 hK0_lo hK0_hi
    have hT0_les : T0 a ≤ (M0 (a + 1) : ℝ) := tildeTau_le_minM_succ ht0 hr0 hK02 hK0_lo hK0_hi
    have hT0_le1 : T0 (a + 1) ≤ (M0 (a + 1) : ℝ) := tildeTau_le_minM ht0 hr0 hK02 hK0_lo hK0_hi
    have hT0_lt : T0 (a + 1) < (M0 a : ℝ) + 1 := tildeTau_succ_lt ht0 hr0 hK02 hK0_lo hK0_hi
    have hT1_le : T1 b ≤ (M1 b : ℝ) := tildeTau_le_minM ht1 hr1 hK12 hK1_lo hK1_hi
    have hT1_les : T1 b ≤ (M1 (b + 1) : ℝ) := tildeTau_le_minM_succ ht1 hr1 hK12 hK1_lo hK1_hi
    have hT1_le1 : T1 (b + 1) ≤ (M1 (b + 1) : ℝ) := tildeTau_le_minM ht1 hr1 hK12 hK1_lo hK1_hi
    have hT1_lt : T1 (b + 1) < (M1 b : ℝ) + 1 := tildeTau_succ_lt ht1 hr1 hK12 hK1_lo hK1_hi
    have hT2_le : T2 c ≤ (M2 c : ℝ) := tildeTau_le_minM ht2 hr2 hK22 hK2_lo hK2_hi
    have hT2_les : T2 c ≤ (M2 (c + 1) : ℝ) := tildeTau_le_minM_succ ht2 hr2 hK22 hK2_lo hK2_hi
    have hT2_le1 : T2 (c + 1) ≤ (M2 (c + 1) : ℝ) := tildeTau_le_minM ht2 hr2 hK22 hK2_lo hK2_hi
    have hT2_lt : T2 (c + 1) < (M2 c : ℝ) + 1 := tildeTau_succ_lt ht2 hr2 hK22 hK2_lo hK2_hi
    -- Helper: strict inequality M_i m < T_i (m+1) implies Case A (nB_i ≤ m)
    have hA0_of : (M0 a : ℝ) < T0 (a + 1) → nB0 ≤ a := by
      intro hlt; by_contra h; have := tildeTau_succ_le_of_lt (t := t0) (nB := nB0) (K := K0) (m := a) (r := r0) ht0 hr0 hK02 (by omega); linarith only [hlt, this]
    have hA1_of : (M1 b : ℝ) < T1 (b + 1) → nB1 ≤ b := by
      intro hlt; by_contra h; have := tildeTau_succ_le_of_lt (t := t1) (nB := nB1) (K := K1) (m := b) (r := r1) ht1 hr1 hK12 (by omega); linarith only [hlt, this]
    have hA2_of : (M2 c : ℝ) < T2 (c + 1) → nB2 ≤ c := by
      intro hlt; by_contra h; have := tildeTau_succ_le_of_lt (t := t2) (nB := nB2) (K := K2) (m := c) (r := r2) ht2 hr2 hK22 (by omega); linarith only [hlt, this]
    -- Global minimum W = min(M0 a, M0(a+1), M1 b, M1(b+1), M2 c, M2(c+1))
    set W := min (min (M0 a) (M0 (a + 1))) (min (min (M1 b) (M1 (b + 1))) (min (M2 c) (M2 (c + 1))))
    have hW0 : W ≤ M0 a := le_trans (min_le_left _ _) (min_le_left _ _)
    have hW0s : W ≤ M0 (a + 1) := le_trans (min_le_left _ _) (min_le_right _ _)
    have hW1 : W ≤ M1 b := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
    have hW1s : W ≤ M1 (b + 1) := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
    have hW2 : W ≤ M2 c := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hW2s : W ≤ M2 (c + 1) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    generalize hc0 : col a (b + 1) = k0 at hrain
    generalize hc1 : col (a + 1) b = k1 at hrain
    generalize hc2 : col (a + 1) (b + 1) = k2 at hrain
    fin_cases k0 <;> fin_cases k1 <;> fin_cases k2
    all_goals try (exfalso; revert hrain; decide)
    · -- (0, 1, 2): impossible at min(n0, n1, n2)
      exfalso
      have h0e : min (M1 (b + 1) : ℝ) (M2 (c + 1) : ℝ) < (M0 (a + 1) : ℝ) :=
        lt_of_lt_of_le (by simpa [E0, hsub0] using (hcol0 a (b + 1) (by omega) hc0).1) hT0_les
      have h1e : min (M0 (a + 1) : ℝ) (M2 (c + 1) : ℝ) < (M1 (b + 1) : ℝ) :=
        lt_of_lt_of_le (by simpa [E1, hsub1] using (hcol1 (a + 1) b (by omega) hc1).1) hT1_les
      have h2e : min (M0 (a + 1) : ℝ) (M1 (b + 1) : ℝ) < (M2 (c + 1) : ℝ) :=
        lt_of_lt_of_le (by simpa [E2, hsub2] using (hcol2 (a + 1) (b + 1) (by omega) hc2).1) hT2_les
      rcases le_total (M0 (a + 1) : ℝ) (M1 (b + 1) : ℝ) with h01 | h10
      · rcases le_total (M0 (a + 1) : ℝ) (M2 (c + 1) : ℝ) with h02 | h20
        · rw [min_eq_left h02] at h1e; rw [min_eq_left h01] at h2e
          rcases le_total (M1 (b + 1) : ℝ) (M2 (c + 1) : ℝ) with h12 | h21
          · rw [min_eq_left h12] at h0e; linarith only [h1e, h0e]
          · rw [min_eq_right h21] at h0e; linarith only [h2e, h0e]
        · rw [min_eq_right h20] at h1e; rw [min_eq_right (le_trans h20 h01)] at h0e
          rw [min_eq_left h01] at h2e; linarith only [h20, h2e]
      · rcases le_total (M1 (b + 1) : ℝ) (M2 (c + 1) : ℝ) with h12 | h21
        · rw [min_eq_right h10] at h2e; rw [min_eq_left h12] at h0e
          rcases le_total (M0 (a + 1) : ℝ) (M2 (c + 1) : ℝ) with h02 | h20
          · rw [min_eq_left h02] at h1e; linarith only [h0e, h1e]
          · rw [min_eq_right h20] at h1e; linarith only [h2e, h1e]
        · rw [min_eq_right h21] at h0e; rw [min_eq_right (le_trans h21 h10)] at h1e
          rw [min_eq_right h10] at h2e; linarith only [h21, h2e]
    · -- (0, 2, 1): u0 col 0, u1 col 2, u2 col 1 → Subcase 4a at (b, c, a + 1)!
      have h0 := hcol0 a (b + 1) (by omega) hc0
      have h1 := hcol2 (a + 1) b (by omega) hc1
      have h2 := hcol1 (a + 1) (b + 1) (by omega) hc2
      have h0e : min (M1 (b + 1) : ℝ) (M2 (c + 1) : ℝ) < T0 a := by simpa [E0, hsub0] using h0.1
      have h1e : min (M0 (a + 1) : ℝ) (M1 b : ℝ) < T2 (c + 1) := by simpa [E2, hsub1] using h1.1
      have h2e : min (M0 (a + 1) : ℝ) (M2 c : ℝ) < T1 (b + 1) := by simpa [E1, hsub2] using h2.1
      have hW_lt_n0 : W < M0 (a + 1) := by
        have hWR : (W : ℝ) < (M0 (a + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW1s) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h0e hT0_les)
        exact_mod_cast hWR
      have hW_lt_a0 : W < M0 a := by
        have hWR : (W : ℝ) < (M0 a : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW1s) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h0e hT0_le)
        exact_mod_cast hWR
      have hW_lt_n1 : W < M1 (b + 1) := by
        have hWR : (W : ℝ) < (M1 (b + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW2)) (lt_of_lt_of_le h2e hT1_le1)
        exact_mod_cast hWR
      have hW_lt_n2 : W < M2 (c + 1) := by
        have hWR : (W : ℝ) < (M2 (c + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW1)) (lt_of_lt_of_le h1e hT2_le1)
        exact_mod_cast hWR
      have h12_eq : M1 b = W ∧ M2 c = W := by
        have hmin12 : M1 b = W ∨ M2 c = W := by omega
        rcases hmin12 with hbW | hcW
        · refine ⟨hbW, ?_⟩
          have hlt : min (M0 (a + 1) : ℝ) (M2 c : ℝ) < (W : ℝ) + 1 := by
            have : (M1 b : ℝ) = (W : ℝ) := by exact_mod_cast hbW
            linarith only [h2e, hT1_lt, this]
          have h0R : (W : ℝ) + 1 ≤ (M0 (a + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M0 (a + 1))
          have hcR : (M2 c : ℝ) < (W : ℝ) + 1 := by
            rcases le_total (M0 (a + 1) : ℝ) (M2 c : ℝ) with h | h
            · rw [min_eq_left h] at hlt; linarith only [hlt, h0R]
            · rw [min_eq_right h] at hlt; exact hlt
          have : M2 c < W + 1 := by exact_mod_cast hcR
          omega
        · refine ⟨?_, hcW⟩
          have hlt : min (M0 (a + 1) : ℝ) (M1 b : ℝ) < (W : ℝ) + 1 := by
            have : (M2 c : ℝ) = (W : ℝ) := by exact_mod_cast hcW
            linarith only [h1e, hT2_lt, this]
          have h0R : (W : ℝ) + 1 ≤ (M0 (a + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M0 (a + 1))
          have hbR : (M1 b : ℝ) < (W : ℝ) + 1 := by
            rcases le_total (M0 (a + 1) : ℝ) (M1 b : ℝ) with h | h
            · rw [min_eq_left h] at hlt; linarith only [hlt, h0R]
            · rw [min_eq_right h] at hlt; exact hlt
          have : M1 b < W + 1 := by exact_mod_cast hbR
          omega
      have h1gt : (M1 b : ℝ) < T1 (b + 1) := by
        have hmin : (M1 b : ℝ) ≤ min (M0 (a + 1) : ℝ) (M2 c : ℝ) :=
          le_min (by exact_mod_cast (by omega : M1 b ≤ M0 (a + 1))) (by exact_mod_cast (by omega : M1 b ≤ M2 c))
        exact lt_of_le_of_lt hmin h2e
      have h2gt : (M1 b : ℝ) < T2 (c + 1) := by
        have hmin : (M1 b : ℝ) ≤ min (M0 (a + 1) : ℝ) (M1 b : ℝ) :=
          le_min (by exact_mod_cast (by omega : M1 b ≤ M0 (a + 1))) (le_refl _)
        exact lt_of_le_of_lt hmin h1e
      have h2gt' : (M2 c : ℝ) < T2 (c + 1) := by
        have : (M2 c : ℝ) = (M1 b : ℝ) := by exact_mod_cast (by omega : M2 c = M1 b)
        linarith only [h2gt, this]
      have h0lt : T0 (a + 1) < (M1 b : ℝ) + 1 := by
        by_cases he0 : E0 (a + 1) b
        · have hle := h1.2.1 he0; rw [hsub1] at hle
          have : (M2 c : ℝ) = (M1 b : ℝ) := by exact_mod_cast (by omega : M2 c = M1 b)
          linarith only [hle, hT2_lt, this]
        · dsimp only [E0] at he0; push Not at he0
          have hle : T0 (a + 1) ≤ (M1 b : ℝ) := le_trans he0 (min_le_left _ _)
          linarith only [hle]
      obtain ⟨S⟩ := threeTypeSpec_of_subcase4a (nA := nA) (nB0 := nB1) (nB1 := nB2) (nB2 := nB0)
        ht1 ht2 ht0 hr1 hr2 hr0
        hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi hK02 hK0_lo hK0_hi
        (by omega : b + c + (a + 1) + 1 = nA + nB1 + nB2 + nB0) (hA1_of h1gt) (hA2_of h2gt')
        (by omega : M1 b = M2 c) (by omega : M1 b < M0 (a + 1)) h1gt h2gt h0lt
      exact ⟨S.rot⟩
    · -- (1, 0, 2): u0 col 1, u1 col 0, u2 col 2 → Subcase 4a at (a, b, c + 1)!
      have h0 := hcol1 a (b + 1) (by omega) hc0
      have h1 := hcol0 (a + 1) b (by omega) hc1
      have h2 := hcol2 (a + 1) (b + 1) (by omega) hc2
      have h0e : min (M0 a : ℝ) (M2 (c + 1) : ℝ) < T1 (b + 1) := by simpa [E1, hsub0] using h0.1
      have h1e : min (M1 b : ℝ) (M2 (c + 1) : ℝ) < T0 (a + 1) := by simpa [E0, hsub1] using h1.1
      have h2e : min (M0 (a + 1) : ℝ) (M1 (b + 1) : ℝ) < T2 c := by simpa [E2, hsub2] using h2.1
      have hW_lt_n2 : W < M2 (c + 1) := by
        have hWR : (W : ℝ) < (M2 (c + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW1s)) (lt_of_lt_of_le h2e hT2_les)
        exact_mod_cast hWR
      have hW_lt_c2 : W < M2 c := by
        have hWR : (W : ℝ) < (M2 c : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW1s)) (lt_of_lt_of_le h2e hT2_le)
        exact_mod_cast hWR
      have hW_lt_n0 : W < M0 (a + 1) := by
        have hWR : (W : ℝ) < (M0 (a + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW1) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h1e hT0_le1)
        exact_mod_cast hWR
      have hW_lt_n1 : W < M1 (b + 1) := by
        have hWR : (W : ℝ) < (M1 (b + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h0e hT1_le1)
        exact_mod_cast hWR
      have h01_eq : M0 a = W ∧ M1 b = W := by
        have hmin01 : M0 a = W ∨ M1 b = W := by omega
        rcases hmin01 with haW | hbW
        · refine ⟨haW, ?_⟩
          have hlt : min (M1 b : ℝ) (M2 (c + 1) : ℝ) < (W : ℝ) + 1 := by
            have : (M0 a : ℝ) = (W : ℝ) := by exact_mod_cast haW
            linarith only [h1e, hT0_lt, this]
          have h2R : (W : ℝ) + 1 ≤ (M2 (c + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M2 (c + 1))
          have hbR : (M1 b : ℝ) < (W : ℝ) + 1 := by
            rcases le_total (M1 b : ℝ) (M2 (c + 1) : ℝ) with h | h
            · rw [min_eq_left h] at hlt; exact hlt
            · rw [min_eq_right h] at hlt; linarith only [hlt, h2R]
          have : M1 b < W + 1 := by exact_mod_cast hbR
          omega
        · refine ⟨?_, hbW⟩
          have hlt : min (M0 a : ℝ) (M2 (c + 1) : ℝ) < (W : ℝ) + 1 := by
            have : (M1 b : ℝ) = (W : ℝ) := by exact_mod_cast hbW
            linarith only [h0e, hT1_lt, this]
          have h2R : (W : ℝ) + 1 ≤ (M2 (c + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M2 (c + 1))
          have haR : (M0 a : ℝ) < (W : ℝ) + 1 := by
            rcases le_total (M0 a : ℝ) (M2 (c + 1) : ℝ) with h | h
            · rw [min_eq_left h] at hlt; exact hlt
            · rw [min_eq_right h] at hlt; linarith only [hlt, h2R]
          have : M0 a < W + 1 := by exact_mod_cast haR
          omega
      have h0gt : (M0 a : ℝ) < T0 (a + 1) := by
        have hmin : (M0 a : ℝ) ≤ min (M1 b : ℝ) (M2 (c + 1) : ℝ) :=
          le_min (by exact_mod_cast (by omega : M0 a ≤ M1 b)) (by exact_mod_cast (by omega : M0 a ≤ M2 (c + 1)))
        exact lt_of_le_of_lt hmin h1e
      have h1gt : (M0 a : ℝ) < T1 (b + 1) := by
        have hmin : (M0 a : ℝ) ≤ min (M0 a : ℝ) (M2 (c + 1) : ℝ) :=
          le_min (le_refl _) (by exact_mod_cast (by omega : M0 a ≤ M2 (c + 1)))
        exact lt_of_le_of_lt hmin h0e
      have h1gt' : (M1 b : ℝ) < T1 (b + 1) := by
        have : (M1 b : ℝ) = (M0 a : ℝ) := by exact_mod_cast (by omega : M1 b = M0 a)
        linarith only [h1gt, this]
      have h2lt : T2 (c + 1) < (M0 a : ℝ) + 1 := by
        by_cases he2 : E2 (a + 1) b
        · have hle := h1.2.2 he2; rw [hsub1] at hle
          linarith only [hle, hT0_lt]
        · dsimp only [E2] at he2; rw [hsub1] at he2; push Not at he2
          have hle : T2 (c + 1) ≤ (M1 b : ℝ) := le_trans he2 (min_le_right _ _)
          have : (M1 b : ℝ) = (M0 a : ℝ) := by exact_mod_cast (by omega : M1 b = M0 a)
          linarith only [hle, this]
      exact threeTypeSpec_of_subcase4a ht0 ht1 ht2 hr0 hr1 hr2
        hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi
        (by omega : a + b + (c + 1) + 1 = N) (hA0_of h0gt) (hA1_of h1gt')
        (by omega : M0 a = M1 b) (by omega : M0 a < M2 (c + 1)) h0gt h1gt h2lt
    · -- (1, 2, 0): 3-cycle → M0 a = M1 b = M2 c = W < n0, n1, n2 → Subcase 4a at (a, b, c + 1)!
      have h0e : min (M0 a : ℝ) (M2 (c + 1) : ℝ) < T1 (b + 1) := by simpa [E1, hsub0] using (hcol1 a (b + 1) (by omega) hc0).1
      have h1e : min (M0 (a + 1) : ℝ) (M1 b : ℝ) < T2 (c + 1) := by simpa [E2, hsub1] using (hcol2 (a + 1) b (by omega) hc1).1
      have h2e : min (M1 (b + 1) : ℝ) (M2 c : ℝ) < T0 (a + 1) := by simpa [E0, hsub2] using (hcol0 (a + 1) (b + 1) (by omega) hc2).1
      have hW_lt_n0 : W < M0 (a + 1) := by
        have hWR : (W : ℝ) < (M0 (a + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW1s) (by exact_mod_cast hW2)) (lt_of_lt_of_le h2e hT0_le1)
        exact_mod_cast hWR
      have hW_lt_n1 : W < M1 (b + 1) := by
        have hWR : (W : ℝ) < (M1 (b + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h0e hT1_le1)
        exact_mod_cast hWR
      have hW_lt_n2 : W < M2 (c + 1) := by
        have hWR : (W : ℝ) < (M2 (c + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW1)) (lt_of_lt_of_le h1e hT2_le1)
        exact_mod_cast hWR
      have hstep_0_2 : M0 a = W → M2 c = W := fun h => by
        have hlt : min (M1 (b + 1) : ℝ) (M2 c : ℝ) < (W : ℝ) + 1 := by
          have : (M0 a : ℝ) = (W : ℝ) := by exact_mod_cast h
          linarith only [h2e, hT0_lt, this]
        have h1R : (W : ℝ) + 1 ≤ (M1 (b + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M1 (b + 1))
        have hcR : (M2 c : ℝ) < (W : ℝ) + 1 := by
          rcases le_total (M1 (b + 1) : ℝ) (M2 c : ℝ) with hl | hl
          · rw [min_eq_left hl] at hlt; linarith only [hlt, h1R]
          · rw [min_eq_right hl] at hlt; exact hlt
        have : M2 c < W + 1 := by exact_mod_cast hcR
        omega
      have hstep_2_1 : M2 c = W → M1 b = W := fun h => by
        have hlt : min (M0 (a + 1) : ℝ) (M1 b : ℝ) < (W : ℝ) + 1 := by
          have : (M2 c : ℝ) = (W : ℝ) := by exact_mod_cast h
          linarith only [h1e, hT2_lt, this]
        have h0R : (W : ℝ) + 1 ≤ (M0 (a + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M0 (a + 1))
        have hbR : (M1 b : ℝ) < (W : ℝ) + 1 := by
          rcases le_total (M0 (a + 1) : ℝ) (M1 b : ℝ) with hl | hl
          · rw [min_eq_left hl] at hlt; linarith only [hlt, h0R]
          · rw [min_eq_right hl] at hlt; exact hlt
        have : M1 b < W + 1 := by exact_mod_cast hbR
        omega
      have hstep_1_0 : M1 b = W → M0 a = W := fun h => by
        have hlt : min (M0 a : ℝ) (M2 (c + 1) : ℝ) < (W : ℝ) + 1 := by
          have : (M1 b : ℝ) = (W : ℝ) := by exact_mod_cast h
          linarith only [h0e, hT1_lt, this]
        have h2R : (W : ℝ) + 1 ≤ (M2 (c + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M2 (c + 1))
        have haR : (M0 a : ℝ) < (W : ℝ) + 1 := by
          rcases le_total (M0 a : ℝ) (M2 (c + 1) : ℝ) with hl | hl
          · rw [min_eq_left hl] at hlt; exact hlt
          · rw [min_eq_right hl] at hlt; linarith only [hlt, h2R]
        have : M0 a < W + 1 := by exact_mod_cast haR
        omega
      have hallW : M0 a = W ∧ M1 b = W ∧ M2 c = W := by
        have : M0 a = W ∨ M1 b = W ∨ M2 c = W := by omega
        rcases this with h | h | h
        · exact ⟨h, hstep_2_1 (hstep_0_2 h), hstep_0_2 h⟩
        · exact ⟨hstep_1_0 h, h, hstep_0_2 (hstep_1_0 h)⟩
        · exact ⟨hstep_1_0 (hstep_2_1 h), hstep_2_1 h, h⟩
      have h0gt : (M0 a : ℝ) < T0 (a + 1) :=
        lt_of_le_of_lt (le_min (by exact_mod_cast (by omega : M0 a ≤ M1 (b + 1))) (by exact_mod_cast (by omega : M0 a ≤ M2 c))) h2e
      have h1gt : (M0 a : ℝ) < T1 (b + 1) :=
        lt_of_le_of_lt (le_min (le_refl _) (by exact_mod_cast (by omega : M0 a ≤ M2 (c + 1)))) h0e
      have h1gt' : (M1 b : ℝ) < T1 (b + 1) := by
        have : (M1 b : ℝ) = (M0 a : ℝ) := by exact_mod_cast (by omega : M1 b = M0 a)
        linarith only [h1gt, this]
      have h2lt : T2 (c + 1) < (M0 a : ℝ) + 1 := by
        have : (M2 c : ℝ) = (M0 a : ℝ) := by exact_mod_cast (by omega : M2 c = M0 a)
        linarith only [hT2_lt, this]
      exact threeTypeSpec_of_subcase4a ht0 ht1 ht2 hr0 hr1 hr2
        hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi
        (by omega : a + b + (c + 1) + 1 = N) (hA0_of h0gt) (hA1_of h1gt')
        (by omega : M0 a = M1 b) (by omega : M0 a < M2 (c + 1)) h0gt h1gt h2lt
    · -- (2, 0, 1): 3-cycle → M0 a = M1 b = M2 c = W < n0, n1, n2 → Subcase 4a at (a, b, c + 1)!
      have h0e : min (M0 a : ℝ) (M1 (b + 1) : ℝ) < T2 (c + 1) := by simpa [E2, hsub0] using (hcol2 a (b + 1) (by omega) hc0).1
      have h1e : min (M1 b : ℝ) (M2 (c + 1) : ℝ) < T0 (a + 1) := by simpa [E0, hsub1] using (hcol0 (a + 1) b (by omega) hc1).1
      have h2e : min (M0 (a + 1) : ℝ) (M2 c : ℝ) < T1 (b + 1) := by simpa [E1, hsub2] using (hcol1 (a + 1) (b + 1) (by omega) hc2).1
      have hW_lt_n0 : W < M0 (a + 1) := by
        have hWR : (W : ℝ) < (M0 (a + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW1) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h1e hT0_le1)
        exact_mod_cast hWR
      have hW_lt_n1 : W < M1 (b + 1) := by
        have hWR : (W : ℝ) < (M1 (b + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW2)) (lt_of_lt_of_le h2e hT1_le1)
        exact_mod_cast hWR
      have hW_lt_n2 : W < M2 (c + 1) := by
        have hWR : (W : ℝ) < (M2 (c + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0) (by exact_mod_cast hW1s)) (lt_of_lt_of_le h0e hT2_le1)
        exact_mod_cast hWR
      have hstep_0_1 : M0 a = W → M1 b = W := fun h => by
        have hlt : min (M1 b : ℝ) (M2 (c + 1) : ℝ) < (W : ℝ) + 1 := by
          have : (M0 a : ℝ) = (W : ℝ) := by exact_mod_cast h
          linarith only [h1e, hT0_lt, this]
        have h2R : (W : ℝ) + 1 ≤ (M2 (c + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M2 (c + 1))
        have hbR : (M1 b : ℝ) < (W : ℝ) + 1 := by
          rcases le_total (M1 b : ℝ) (M2 (c + 1) : ℝ) with hl | hl
          · rw [min_eq_left hl] at hlt; exact hlt
          · rw [min_eq_right hl] at hlt; linarith only [hlt, h2R]
        have : M1 b < W + 1 := by exact_mod_cast hbR
        omega
      have hstep_1_2 : M1 b = W → M2 c = W := fun h => by
        have hlt : min (M0 (a + 1) : ℝ) (M2 c : ℝ) < (W : ℝ) + 1 := by
          have : (M1 b : ℝ) = (W : ℝ) := by exact_mod_cast h
          linarith only [h2e, hT1_lt, this]
        have h0R : (W : ℝ) + 1 ≤ (M0 (a + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M0 (a + 1))
        have hcR : (M2 c : ℝ) < (W : ℝ) + 1 := by
          rcases le_total (M0 (a + 1) : ℝ) (M2 c : ℝ) with hl | hl
          · rw [min_eq_left hl] at hlt; linarith only [hlt, h0R]
          · rw [min_eq_right hl] at hlt; exact hlt
        have : M2 c < W + 1 := by exact_mod_cast hcR
        omega
      have hstep_2_0 : M2 c = W → M0 a = W := fun h => by
        have hlt : min (M0 a : ℝ) (M1 (b + 1) : ℝ) < (W : ℝ) + 1 := by
          have : (M2 c : ℝ) = (W : ℝ) := by exact_mod_cast h
          linarith only [h0e, hT2_lt, this]
        have h1R : (W : ℝ) + 1 ≤ (M1 (b + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M1 (b + 1))
        have haR : (M0 a : ℝ) < (W : ℝ) + 1 := by
          rcases le_total (M0 a : ℝ) (M1 (b + 1) : ℝ) with hl | hl
          · rw [min_eq_left hl] at hlt; exact hlt
          · rw [min_eq_right hl] at hlt; linarith only [hlt, h1R]
        have : M0 a < W + 1 := by exact_mod_cast haR
        omega
      have hallW : M0 a = W ∧ M1 b = W ∧ M2 c = W := by
        have : M0 a = W ∨ M1 b = W ∨ M2 c = W := by omega
        rcases this with h | h | h
        · exact ⟨h, hstep_0_1 h, hstep_1_2 (hstep_0_1 h)⟩
        · exact ⟨hstep_2_0 (hstep_1_2 h), h, hstep_1_2 h⟩
        · exact ⟨hstep_2_0 h, hstep_0_1 (hstep_2_0 h), h⟩
      have h0gt : (M0 a : ℝ) < T0 (a + 1) :=
        lt_of_le_of_lt (le_min (by exact_mod_cast (by omega : M0 a ≤ M1 b)) (by exact_mod_cast (by omega : M0 a ≤ M2 (c + 1)))) h1e
      have h1gt : (M0 a : ℝ) < T1 (b + 1) :=
        lt_of_le_of_lt (le_min (by exact_mod_cast (by omega : M0 a ≤ M0 (a + 1))) (by exact_mod_cast (by omega : M0 a ≤ M2 c))) h2e
      have h1gt' : (M1 b : ℝ) < T1 (b + 1) := by
        have : (M1 b : ℝ) = (M0 a : ℝ) := by exact_mod_cast (by omega : M1 b = M0 a)
        linarith only [h1gt, this]
      have h2lt : T2 (c + 1) < (M0 a : ℝ) + 1 := by
        have : (M2 c : ℝ) = (M0 a : ℝ) := by exact_mod_cast (by omega : M2 c = M0 a)
        linarith only [hT2_lt, this]
      exact threeTypeSpec_of_subcase4a ht0 ht1 ht2 hr0 hr1 hr2
        hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi hK22 hK2_lo hK2_hi
        (by omega : a + b + (c + 1) + 1 = N) (hA0_of h0gt) (hA1_of h1gt')
        (by omega : M0 a = M1 b) (by omega : M0 a < M2 (c + 1)) h0gt h1gt h2lt
    · -- (2, 1, 0): u0 col 2, u1 col 1, u2 col 0 → Subcase 4a at (c, a, b + 1)!
      have h0 := hcol2 a (b + 1) (by omega) hc0
      have h1 := hcol1 (a + 1) b (by omega) hc1
      have h2 := hcol0 (a + 1) (b + 1) (by omega) hc2
      have h0e : min (M0 a : ℝ) (M1 (b + 1) : ℝ) < T2 (c + 1) := by simpa [E2, hsub0] using h0.1
      have h1e : min (M0 (a + 1) : ℝ) (M2 (c + 1) : ℝ) < T1 b := by simpa [E1, hsub1] using h1.1
      have h2e : min (M1 (b + 1) : ℝ) (M2 c : ℝ) < T0 (a + 1) := by simpa [E0, hsub2] using h2.1
      have hW_lt_n1 : W < M1 (b + 1) := by
        have hWR : (W : ℝ) < (M1 (b + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h1e hT1_les)
        exact_mod_cast hWR
      have hW_lt_b1 : W < M1 b := by
        have hWR : (W : ℝ) < (M1 b : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0s) (by exact_mod_cast hW2s)) (lt_of_lt_of_le h1e hT1_le)
        exact_mod_cast hWR
      have hW_lt_n0 : W < M0 (a + 1) := by
        have hWR : (W : ℝ) < (M0 (a + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW1s) (by exact_mod_cast hW2)) (lt_of_lt_of_le h2e hT0_le1)
        exact_mod_cast hWR
      have hW_lt_n2 : W < M2 (c + 1) := by
        have hWR : (W : ℝ) < (M2 (c + 1) : ℝ) :=
          lt_of_le_of_lt (le_min (by exact_mod_cast hW0) (by exact_mod_cast hW1s)) (lt_of_lt_of_le h0e hT2_le1)
        exact_mod_cast hWR
      have h20_eq : M2 c = W ∧ M0 a = W := by
        have hmin20 : M2 c = W ∨ M0 a = W := by omega
        rcases hmin20 with hcW | haW
        · refine ⟨hcW, ?_⟩
          have hlt : min (M0 a : ℝ) (M1 (b + 1) : ℝ) < (W : ℝ) + 1 := by
            have : (M2 c : ℝ) = (W : ℝ) := by exact_mod_cast hcW
            linarith only [h0e, hT2_lt, this]
          have h1R : (W : ℝ) + 1 ≤ (M1 (b + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M1 (b + 1))
          have haR : (M0 a : ℝ) < (W : ℝ) + 1 := by
            rcases le_total (M0 a : ℝ) (M1 (b + 1) : ℝ) with h | h
            · rw [min_eq_left h] at hlt; exact hlt
            · rw [min_eq_right h] at hlt; linarith only [hlt, h1R]
          have : M0 a < W + 1 := by exact_mod_cast haR
          omega
        · refine ⟨?_, haW⟩
          have hlt : min (M1 (b + 1) : ℝ) (M2 c : ℝ) < (W : ℝ) + 1 := by
            have : (M0 a : ℝ) = (W : ℝ) := by exact_mod_cast haW
            linarith only [h2e, hT0_lt, this]
          have h1R : (W : ℝ) + 1 ≤ (M1 (b + 1) : ℝ) := by exact_mod_cast (by omega : W + 1 ≤ M1 (b + 1))
          have hcR : (M2 c : ℝ) < (W : ℝ) + 1 := by
            rcases le_total (M1 (b + 1) : ℝ) (M2 c : ℝ) with h | h
            · rw [min_eq_left h] at hlt; linarith only [hlt, h1R]
            · rw [min_eq_right h] at hlt; exact hlt
          have : M2 c < W + 1 := by exact_mod_cast hcR
          omega
      have h2gt : (M2 c : ℝ) < T2 (c + 1) :=
        lt_of_le_of_lt (le_min (by exact_mod_cast (by omega : M2 c ≤ M0 a)) (by exact_mod_cast (by omega : M2 c ≤ M1 (b + 1)))) h0e
      have h0gt : (M2 c : ℝ) < T0 (a + 1) :=
        lt_of_le_of_lt (le_min (by exact_mod_cast (by omega : M2 c ≤ M1 (b + 1))) (le_refl _)) h2e
      have h0gt' : (M0 a : ℝ) < T0 (a + 1) := by
        have : (M0 a : ℝ) = (M2 c : ℝ) := by exact_mod_cast (by omega : M0 a = M2 c)
        linarith only [h0gt, this]
      have h1lt : T1 (b + 1) < (M2 c : ℝ) + 1 := by
        by_cases he1 : E1 a (b + 1)
        · have hle := h0.2.2 he1; rw [hsub0] at hle
          linarith only [hle, hT2_lt]
        · dsimp only [E1] at he1; push Not at he1
          have hle : T1 (b + 1) ≤ (M0 a : ℝ) := le_trans he1 (min_le_left _ _)
          have : (M0 a : ℝ) = (M2 c : ℝ) := by exact_mod_cast (by omega : M0 a = M2 c)
          linarith only [hle, this]
      obtain ⟨S⟩ := threeTypeSpec_of_subcase4a (nA := nA) (nB0 := nB2) (nB1 := nB0) (nB2 := nB1)
        ht2 ht0 ht1 hr2 hr0 hr1
        hK22 hK2_lo hK2_hi hK02 hK0_lo hK0_hi hK12 hK1_lo hK1_hi
        (by omega : c + a + (b + 1) + 1 = nA + nB2 + nB0 + nB1) (hA2_of h2gt) (hA0_of h0gt')
        (by omega : M2 c = M0 a) (by omega : M2 c < M1 (b + 1)) h2gt h0gt h1lt
      exact ⟨S.rot.rot⟩

/-! ### Part 6: Concrete Realization and Top-Level Three-Agent-Type Theorem -/

/-- Realize a `ThreeTypeSpec` as a concrete EFX allocation on `Fin ((t0 + t1) + t2)` agents
and `Fin (((nA + nB0) + nB1) + nB2)` chores ordered `A, B0, B1, B2`. -/
lemma realize_threeTypeSpec {t0 t1 t2 nA nB0 nB1 nB2 : ℕ} {r0 r1 r2 : ℝ}
    (hr0 : 1 < r0) (hr1 : 1 < r1) (hr2 : 1 < r2)
    (cost : Fin ((t0 + t1) + t2) → Fin (((nA + nB0) + nB1) + nB2) → ℝ)
    (hA0 : ∀ (i : Fin t0) (g : Fin nA),
      cost (Fin.castAdd t2 (Fin.castAdd t1 i)) (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.castAdd nB0 g))) = r0)
    (hA1 : ∀ (i : Fin t1) (g : Fin nA),
      cost (Fin.castAdd t2 (Fin.natAdd t0 i)) (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.castAdd nB0 g))) = r1)
    (hA2 : ∀ (i : Fin t2) (g : Fin nA),
      cost (Fin.natAdd (t0 + t1) i) (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.castAdd nB0 g))) = r2)
    (hB00 : ∀ (i : Fin t0) (g : Fin nB0),
      cost (Fin.castAdd t2 (Fin.castAdd t1 i)) (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.natAdd nA g))) = 1)
    (hB01 : ∀ (i : Fin t1) (g : Fin nB0),
      cost (Fin.castAdd t2 (Fin.natAdd t0 i)) (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.natAdd nA g))) = r1)
    (hB02 : ∀ (i : Fin t2) (g : Fin nB0),
      cost (Fin.natAdd (t0 + t1) i) (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.natAdd nA g))) = r2)
    (hB10 : ∀ (i : Fin t0) (g : Fin nB1),
      cost (Fin.castAdd t2 (Fin.castAdd t1 i)) (Fin.castAdd nB2 (Fin.natAdd (nA + nB0) g)) = r0)
    (hB11 : ∀ (i : Fin t1) (g : Fin nB1),
      cost (Fin.castAdd t2 (Fin.natAdd t0 i)) (Fin.castAdd nB2 (Fin.natAdd (nA + nB0) g)) = 1)
    (hB12 : ∀ (i : Fin t2) (g : Fin nB1),
      cost (Fin.natAdd (t0 + t1) i) (Fin.castAdd nB2 (Fin.natAdd (nA + nB0) g)) = r2)
    (hB20 : ∀ (i : Fin t0) (g : Fin nB2),
      cost (Fin.castAdd t2 (Fin.castAdd t1 i)) (Fin.natAdd ((nA + nB0) + nB1) g) = r0)
    (hB21 : ∀ (i : Fin t1) (g : Fin nB2),
      cost (Fin.castAdd t2 (Fin.natAdd t0 i)) (Fin.natAdd ((nA + nB0) + nB1) g) = r1)
    (hB22 : ∀ (i : Fin t2) (g : Fin nB2),
      cost (Fin.natAdd (t0 + t1) i) (Fin.natAdd ((nA + nB0) + nB1) g) = 1)
    (S : ThreeTypeSpec t0 t1 t2 nA nB0 nB1 nB2 r0 r1 r2) :
    ∃ alloc : Fin (((nA + nB0) + nB1) + nB2) → Fin ((t0 + t1) + t2), IsEFX cost alloc := by
  let cntA : Fin ((t0 + t1) + t2) → ℕ := Fin.addCases (Fin.addCases S.A0 S.A1) S.A2
  let cntB0 : Fin ((t0 + t1) + t2) → ℕ := Fin.addCases (Fin.addCases S.B00 S.B01) S.B02
  let cntB1 : Fin ((t0 + t1) + t2) → ℕ := Fin.addCases (Fin.addCases S.B10 S.B11) S.B12
  let cntB2 : Fin ((t0 + t1) + t2) → ℕ := Fin.addCases (Fin.addCases S.B20 S.B21) S.B22
  have hsumA : ∑ k, cntA k = nA := by simp [cntA, Fin.sum_univ_add, S.sumA]
  have hsumB0 : ∑ k, cntB0 k = nB0 := by simp [cntB0, Fin.sum_univ_add, S.sumB0]
  have hsumB1 : ∑ k, cntB1 k = nB1 := by simp [cntB1, Fin.sum_univ_add, S.sumB1]
  have hsumB2 : ∑ k, cntB2 k = nB2 := by simp [cntB2, Fin.sum_univ_add, S.sumB2]
  obtain ⟨fA, hfA⟩ := exists_assignment_with_counts cntA hsumA
  obtain ⟨fB0, hfB0⟩ := exists_assignment_with_counts cntB0 hsumB0
  obtain ⟨fB1, hfB1⟩ := exists_assignment_with_counts cntB1 hsumB1
  obtain ⟨fB2, hfB2⟩ := exists_assignment_with_counts cntB2 hsumB2
  let alloc : Fin (((nA + nB0) + nB1) + nB2) → Fin ((t0 + t1) + t2) :=
    Fin.addCases (Fin.addCases (Fin.addCases fA fB0) fB1) fB2
  have hcost_split : ∀ (k i : Fin ((t0 + t1) + t2)),
      bundleCost cost (bundle alloc k) i =
        (∑ g ∈ Finset.univ.filter (fun x : Fin nA => fA x = k),
            cost i (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.castAdd nB0 g)))) +
        (∑ g ∈ Finset.univ.filter (fun x : Fin nB0 => fB0 x = k),
            cost i (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.natAdd nA g)))) +
        (∑ g ∈ Finset.univ.filter (fun x : Fin nB1 => fB1 x = k),
            cost i (Fin.castAdd nB2 (Fin.natAdd (nA + nB0) g))) +
        (∑ g ∈ Finset.univ.filter (fun x : Fin nB2 => fB2 x = k),
            cost i (Fin.natAdd ((nA + nB0) + nB1) g)) := by
    intro k i
    unfold bundleCost bundle
    rw [Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [alloc, Fin.addCases_left, Fin.addCases_right, ← Finset.sum_filter]
  have hcost0 : ∀ (i : Fin t0) (k : Fin ((t0 + t1) + t2)),
      bundleCost cost (bundle alloc k) (Fin.castAdd t2 (Fin.castAdd t1 i)) =
        ownCost r0 (cntA k + cntB1 k + cntB2 k) (cntB0 k) := by
    intro i k
    rw [hcost_split k (Fin.castAdd t2 (Fin.castAdd t1 i))]
    simp only [hA0, hB00, hB10, hB20, Finset.sum_const, nsmul_eq_mul,
      hfA k, hfB0 k, hfB1 k, hfB2 k, ownCost]
    push_cast; ring
  have hcost1 : ∀ (i : Fin t1) (k : Fin ((t0 + t1) + t2)),
      bundleCost cost (bundle alloc k) (Fin.castAdd t2 (Fin.natAdd t0 i)) =
        ownCost r1 (cntA k + cntB0 k + cntB2 k) (cntB1 k) := by
    intro i k
    rw [hcost_split k (Fin.castAdd t2 (Fin.natAdd t0 i))]
    simp only [hA1, hB01, hB11, hB21, Finset.sum_const, nsmul_eq_mul,
      hfA k, hfB0 k, hfB1 k, hfB2 k, ownCost]
    push_cast; ring
  have hcost2 : ∀ (i : Fin t2) (k : Fin ((t0 + t1) + t2)),
      bundleCost cost (bundle alloc k) (Fin.natAdd (t0 + t1) i) =
        ownCost r2 (cntA k + cntB0 k + cntB1 k) (cntB2 k) := by
    intro i k
    rw [hcost_split k (Fin.natAdd (t0 + t1) i)]
    simp only [hA2, hB02, hB12, hB22, Finset.sum_const, nsmul_eq_mul,
      hfA k, hfB0 k, hfB1 k, hfB2 k, ownCost]
    push_cast; ring
  refine ⟨alloc, fun i j g hg => ?_⟩
  rw [bundleCost_sdiff_singleton cost hg]
  revert hg
  refine Fin.addCases (fun i01 => ?_) (fun i2 hg => ?_) i
  · refine Fin.addCases (fun i0 hg => ?_) (fun i1 hg => ?_) i01
    · -- Group 0
      rw [hcost0 i0 (Fin.castAdd t2 (Fin.castAdd t1 i0))]
      have hcA : cntA (Fin.castAdd t2 (Fin.castAdd t1 i0)) = S.A0 i0 := by simp [cntA]
      have hcB0 : cntB0 (Fin.castAdd t2 (Fin.castAdd t1 i0)) = S.B00 i0 := by simp [cntB0]
      have hcB1 : cntB1 (Fin.castAdd t2 (Fin.castAdd t1 i0)) = S.B10 i0 := by simp [cntB1]
      have hcB2 : cntB2 (Fin.castAdd t2 (Fin.castAdd t1 i0)) = S.B20 i0 := by simp [cntB2]
      rw [hcA, hcB0, hcB1, hcB2]
      have htau_ge : ownCost r0 (S.A0 i0 + S.B10 i0 + S.B20 i0) (S.B00 i0) -
          cost (Fin.castAdd t2 (Fin.castAdd t1 i0)) g ≤
          ownTau r0 (S.A0 i0 + S.B10 i0 + S.B20 i0) (S.B00 i0) := by
        have hg_eq : alloc g = Fin.castAdd t2 (Fin.castAdd t1 i0) := mem_bundle.mp hg
        revert hg_eq
        refine Fin.addCases (fun gAB1 => ?_) (fun gB2 hg_eq => ?_) g
        · refine Fin.addCases (fun gAB0 => ?_) (fun gB1 hg_eq => ?_) gAB1
          · refine Fin.addCases (fun gA hg_eq => ?_) (fun gB0 hg_eq => ?_) gAB0
            · have hgA : fA gA = Fin.castAdd t2 (Fin.castAdd t1 i0) := by simpa [alloc] using hg_eq
              have hpos : 0 < S.A0 i0 := by rw [← hcA, ← hfA]; exact Finset.card_pos.mpr ⟨gA, by simp [hgA]⟩
              rw [hA0 i0 gA]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
            · have hgB : fB0 gB0 = Fin.castAdd t2 (Fin.castAdd t1 i0) := by simpa [alloc] using hg_eq
              have hpos : 0 < S.B00 i0 := by rw [← hcB0, ← hfB0]; exact Finset.card_pos.mpr ⟨gB0, by simp [hgB]⟩
              rw [hB00 i0 gB0]; unfold ownTau; rw [ite_eq_right (by omega), ite_eq_left hpos]
          · have hgB : fB1 gB1 = Fin.castAdd t2 (Fin.castAdd t1 i0) := by simpa [alloc] using hg_eq
            have hpos : 0 < S.B10 i0 := by rw [← hcB1, ← hfB1]; exact Finset.card_pos.mpr ⟨gB1, by simp [hgB]⟩
            rw [hB10 i0 gB1]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
        · have hgB : fB2 gB2 = Fin.castAdd t2 (Fin.castAdd t1 i0) := by simpa [alloc] using hg_eq
          have hpos : 0 < S.B20 i0 := by rw [← hcB2, ← hfB2]; exact Finset.card_pos.mpr ⟨gB2, by simp [hgB]⟩
          rw [hB20 i0 gB2]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
      refine le_trans htau_ge ?_
      refine Fin.addCases (fun j01 => ?_) (fun j2 => ?_) j
      · refine Fin.addCases (fun j0 => ?_) (fun j1 => ?_) j01
        · rw [hcost0 i0]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_left]; exact S.efx00 i0 j0
        · rw [hcost0 i0]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_left, Fin.addCases_right]; exact S.efx01 i0 j1
      · rw [hcost0 i0]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_right]; exact S.efx02 i0 j2
    · -- Group 1
      rw [hcost1 i1 (Fin.castAdd t2 (Fin.natAdd t0 i1))]
      have hcA : cntA (Fin.castAdd t2 (Fin.natAdd t0 i1)) = S.A1 i1 := by simp [cntA]
      have hcB0 : cntB0 (Fin.castAdd t2 (Fin.natAdd t0 i1)) = S.B01 i1 := by simp [cntB0]
      have hcB1 : cntB1 (Fin.castAdd t2 (Fin.natAdd t0 i1)) = S.B11 i1 := by simp [cntB1]
      have hcB2 : cntB2 (Fin.castAdd t2 (Fin.natAdd t0 i1)) = S.B21 i1 := by simp [cntB2]
      rw [hcA, hcB0, hcB1, hcB2]
      have htau_ge : ownCost r1 (S.A1 i1 + S.B01 i1 + S.B21 i1) (S.B11 i1) -
          cost (Fin.castAdd t2 (Fin.natAdd t0 i1)) g ≤
          ownTau r1 (S.A1 i1 + S.B01 i1 + S.B21 i1) (S.B11 i1) := by
        have hg_eq : alloc g = Fin.castAdd t2 (Fin.natAdd t0 i1) := mem_bundle.mp hg
        revert hg_eq
        refine Fin.addCases (fun gAB1 => ?_) (fun gB2 hg_eq => ?_) g
        · refine Fin.addCases (fun gAB0 => ?_) (fun gB1 hg_eq => ?_) gAB1
          · refine Fin.addCases (fun gA hg_eq => ?_) (fun gB0 hg_eq => ?_) gAB0
            · have hgA : fA gA = Fin.castAdd t2 (Fin.natAdd t0 i1) := by simpa [alloc] using hg_eq
              have hpos : 0 < S.A1 i1 := by rw [← hcA, ← hfA]; exact Finset.card_pos.mpr ⟨gA, by simp [hgA]⟩
              rw [hA1 i1 gA]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
            · have hgB : fB0 gB0 = Fin.castAdd t2 (Fin.natAdd t0 i1) := by simpa [alloc] using hg_eq
              have hpos : 0 < S.B01 i1 := by rw [← hcB0, ← hfB0]; exact Finset.card_pos.mpr ⟨gB0, by simp [hgB]⟩
              rw [hB01 i1 gB0]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
          · have hgB : fB1 gB1 = Fin.castAdd t2 (Fin.natAdd t0 i1) := by simpa [alloc] using hg_eq
            have hpos : 0 < S.B11 i1 := by rw [← hcB1, ← hfB1]; exact Finset.card_pos.mpr ⟨gB1, by simp [hgB]⟩
            rw [hB11 i1 gB1]; unfold ownTau; rw [ite_eq_right (by omega), ite_eq_left hpos]
        · have hgB : fB2 gB2 = Fin.castAdd t2 (Fin.natAdd t0 i1) := by simpa [alloc] using hg_eq
          have hpos : 0 < S.B21 i1 := by rw [← hcB2, ← hfB2]; exact Finset.card_pos.mpr ⟨gB2, by simp [hgB]⟩
          rw [hB21 i1 gB2]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
      refine le_trans htau_ge ?_
      refine Fin.addCases (fun j01 => ?_) (fun j2 => ?_) j
      · refine Fin.addCases (fun j0 => ?_) (fun j1 => ?_) j01
        · rw [hcost1 i1]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_left]; exact S.efx10 i1 j0
        · rw [hcost1 i1]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_left, Fin.addCases_right]; exact S.efx11 i1 j1
      · rw [hcost1 i1]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_right]; exact S.efx12 i1 j2
  · -- Group 2
    rw [hcost2 i2 (Fin.natAdd (t0 + t1) i2)]
    have hcA : cntA (Fin.natAdd (t0 + t1) i2) = S.A2 i2 := by simp [cntA]
    have hcB0 : cntB0 (Fin.natAdd (t0 + t1) i2) = S.B02 i2 := by simp [cntB0]
    have hcB1 : cntB1 (Fin.natAdd (t0 + t1) i2) = S.B12 i2 := by simp [cntB1]
    have hcB2 : cntB2 (Fin.natAdd (t0 + t1) i2) = S.B22 i2 := by simp [cntB2]
    rw [hcA, hcB0, hcB1, hcB2]
    have htau_ge : ownCost r2 (S.A2 i2 + S.B02 i2 + S.B12 i2) (S.B22 i2) -
        cost (Fin.natAdd (t0 + t1) i2) g ≤
        ownTau r2 (S.A2 i2 + S.B02 i2 + S.B12 i2) (S.B22 i2) := by
      have hg_eq : alloc g = Fin.natAdd (t0 + t1) i2 := mem_bundle.mp hg
      revert hg_eq
      refine Fin.addCases (fun gAB1 => ?_) (fun gB2 hg_eq => ?_) g
      · refine Fin.addCases (fun gAB0 => ?_) (fun gB1 hg_eq => ?_) gAB1
        · refine Fin.addCases (fun gA hg_eq => ?_) (fun gB0 hg_eq => ?_) gAB0
          · have hgA : fA gA = Fin.natAdd (t0 + t1) i2 := by simpa [alloc] using hg_eq
            have hpos : 0 < S.A2 i2 := by rw [← hcA, ← hfA]; exact Finset.card_pos.mpr ⟨gA, by simp [hgA]⟩
            rw [hA2 i2 gA]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
          · have hgB : fB0 gB0 = Fin.natAdd (t0 + t1) i2 := by simpa [alloc] using hg_eq
            have hpos : 0 < S.B02 i2 := by rw [← hcB0, ← hfB0]; exact Finset.card_pos.mpr ⟨gB0, by simp [hgB]⟩
            rw [hB02 i2 gB0]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
        · have hgB : fB1 gB1 = Fin.natAdd (t0 + t1) i2 := by simpa [alloc] using hg_eq
          have hpos : 0 < S.B12 i2 := by rw [← hcB1, ← hfB1]; exact Finset.card_pos.mpr ⟨gB1, by simp [hgB]⟩
          rw [hB12 i2 gB1]; unfold ownTau; rw [ite_eq_right (by omega)]; split_ifs <;> linarith
      · have hgB : fB2 gB2 = Fin.natAdd (t0 + t1) i2 := by simpa [alloc] using hg_eq
        have hpos : 0 < S.B22 i2 := by rw [← hcB2, ← hfB2]; exact Finset.card_pos.mpr ⟨gB2, by simp [hgB]⟩
        rw [hB22 i2 gB2]; unfold ownTau; rw [ite_eq_right (by omega), ite_eq_left hpos]
    refine le_trans htau_ge ?_
    refine Fin.addCases (fun j01 => ?_) (fun j2 => ?_) j
    · refine Fin.addCases (fun j0 => ?_) (fun j1 => ?_) j01
      · rw [hcost2 i2]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_left]; exact S.efx20 i2 j0
      · rw [hcost2 i2]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_left, Fin.addCases_right]; exact S.efx21 i2 j1
    · rw [hcost2 i2]; simp only [cntA, cntB0, cntB1, cntB2, Fin.addCases_right]; exact S.efx22 i2 j2

/-- **Theorem C2 (EFX Existence for Personalized Bi-Valued Chores with Three Agent Types)**:
For every `n ≥ 1`, every `m ≥ 0`, every 3-type agent partition `cls : Fin n → Fin 3`,
and every personalized bi-valued additive chores instance `cost i g = v (cls i) g ∈ {p b, q b}`
(`0 < p b ≤ q b`) in which each chore has cost `p b` for zero, one, or all three types,
there exists a complete exact EFX allocation. -/
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
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc := by
  classical
  -- Step 1: Normalize each type by dividing by p b > 0
  let r : Fin 3 → ℝ := fun b => if p b < q b then q b / p b else 2
  have hr : ∀ b, 1 < r b := by
    intro b; simp only [r]
    split_ifs with hlt
    · exact (one_lt_div (hp b)).mpr hlt
    · norm_num
  let vN : Fin 3 → Fin m → ℝ := fun b g => v b g / p b
  let costN : Fin n → Fin m → ℝ := fun i g => vN (cls i) g
  have hvN_biv : ∀ b g, vN b g = 1 ∨ vN b g = r b := by
    intro b g
    rcases hbiv b g with h1 | h2
    · left; simp [vN, h1, ne_of_gt (hp b)]
    · by_cases hlt : p b < q b
      · right; simp [vN, r, hlt, h2]
      · left
        have heq : q b = p b := le_antisymm (not_lt.mp hlt) (hpq b)
        simp [vN, h2, heq, ne_of_gt (hp b)]
  have hvN_one_iff : ∀ b g, vN b g = 1 ↔ v b g = p b := by
    intro b g
    simp only [vN, div_eq_one_iff_eq (ne_of_gt (hp b))]
  have hscale : ∀ i g, cost i g = p (cls i) * costN i g := by
    intro i g
    simp only [h_types, costN, vN]
    exact (mul_div_cancel₀ _ (ne_of_gt (hp (cls i)))).symm
  suffices hexN : ∃ alloc : Fin m → Fin n, IsEFX costN alloc by
    rcases hexN with ⟨alloc, hefxN⟩
    exact ⟨alloc, (isEFX_scale (fun i => p (cls i)) (fun i => hp (cls i)) hscale).mpr hefxN⟩
  -- Step 2: Handle degenerate ≤2-type cases directly via `exists_efx_two_agent_types_bivalued`!
  by_cases hno0 : ∀ i, cls i ≠ 0
  · refine exists_efx_two_agent_types_bivalued hn costN
      (fun i => decide (cls i = 2)) (fun b g => if b then vN 2 g else vN 1 g) ?_
      (fun _ => 1) (fun b => if b then r 2 else r 1) (fun _ => zero_lt_one) ?_ ?_
    · intro i g; simp only [costN]
      have h0 := hno0 i
      generalize hci : cls i = ci at h0 ⊢
      fin_cases ci
      · exact absurd rfl h0
      · simp
      · simp
    · intro b; cases b <;> simp [le_of_lt (hr _)]
    · intro b g; cases b <;> simp [hvN_biv]
  by_cases hno1 : ∀ i, cls i ≠ 1
  · refine exists_efx_two_agent_types_bivalued hn costN
      (fun i => decide (cls i = 2)) (fun b g => if b then vN 2 g else vN 0 g) ?_
      (fun _ => 1) (fun b => if b then r 2 else r 0) (fun _ => zero_lt_one) ?_ ?_
    · intro i g; simp only [costN]
      have h1 := hno1 i
      generalize hci : cls i = ci at h1 ⊢
      fin_cases ci
      · simp
      · exact absurd rfl h1
      · simp
    · intro b; cases b <;> simp [le_of_lt (hr _)]
    · intro b g; cases b <;> simp [hvN_biv]
  by_cases hno2 : ∀ i, cls i ≠ 2
  · refine exists_efx_two_agent_types_bivalued hn costN
      (fun i => decide (cls i = 1)) (fun b g => if b then vN 1 g else vN 0 g) ?_
      (fun _ => 1) (fun b => if b then r 1 else r 0) (fun _ => zero_lt_one) ?_ ?_
    · intro i g; simp only [costN]
      have h2 := hno2 i
      generalize hci : cls i = ci at h2 ⊢
      fin_cases ci
      · simp
      · simp
      · exact absurd rfl h2
    · intro b; cases b <;> simp [le_of_lt (hr _)]
    · intro b g; cases b <;> simp [hvN_biv]
  push Not at hno0 hno1 hno2
  -- Step 3: Partition agents into Fin ((t0 + t1) + t2) with 0 < t0, 0 < t1, 0 < t2
  obtain ⟨t01, t2, eAg2, hAg01, hAg2⟩ := equiv_partition_fin (fun i : Fin n => cls i ≠ 2)
  obtain ⟨t0, t1, eAg01, hAg0, hAg1⟩ :=
    equiv_partition_fin (fun i : Fin t01 => cls (eAg2.symm (Fin.castAdd t2 i)) = 0)
  let eAg : Fin n ≃ Fin ((t0 + t1) + t2) :=
    eAg2.trans ((finSumFinEquiv.symm.trans (eAg01.sumCongr (Equiv.refl (Fin t2)))).trans finSumFinEquiv)
  let costAg : Fin ((t0 + t1) + t2) → Fin m → ℝ := fun i' g => costN (eAg.symm i') g
  suffices hexAg : ∃ alloc' : Fin m → Fin ((t0 + t1) + t2), IsEFX costAg alloc' by
    rcases hexAg with ⟨alloc', hefx'⟩
    exact ⟨fun g => eAg.symm (alloc' g), isEFX_reindex_agents eAg costN hefx'⟩
  have heAg0 : ∀ i : Fin t0,
      eAg.symm (Fin.castAdd t2 (Fin.castAdd t1 i)) = eAg2.symm (Fin.castAdd t2 (eAg01.symm (Fin.castAdd t1 i))) := by
    intro i
    have hL : (finSumFinEquiv : Fin (t0 + t1) ⊕ Fin t2 ≃ Fin ((t0 + t1) + t2)).symm
        (Fin.castAdd t2 (Fin.castAdd t1 i)) = Sum.inl (Fin.castAdd t1 i) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eAg, hL]
  have heAg1 : ∀ i : Fin t1,
      eAg.symm (Fin.castAdd t2 (Fin.natAdd t0 i)) = eAg2.symm (Fin.castAdd t2 (eAg01.symm (Fin.natAdd t0 i))) := by
    intro i
    have hL : (finSumFinEquiv : Fin (t0 + t1) ⊕ Fin t2 ≃ Fin ((t0 + t1) + t2)).symm
        (Fin.castAdd t2 (Fin.natAdd t0 i)) = Sum.inl (Fin.natAdd t0 i) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eAg, hL]
  have heAg2 : ∀ i : Fin t2,
      eAg.symm (Fin.natAdd (t0 + t1) i) = eAg2.symm (Fin.natAdd t01 i) := by
    intro i
    have hR : (finSumFinEquiv : Fin (t0 + t1) ⊕ Fin t2 ≃ Fin ((t0 + t1) + t2)).symm
        (Fin.natAdd (t0 + t1) i) = Sum.inr i :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eAg, hR]
  have hAg0_cls : ∀ i : Fin t0, cls (eAg.symm (Fin.castAdd t2 (Fin.castAdd t1 i))) = 0 := fun i => by
    rw [heAg0]; exact hAg0 i
  have hAg1_cls : ∀ i : Fin t1, cls (eAg.symm (Fin.castAdd t2 (Fin.natAdd t0 i))) = 1 := fun i => by
    rw [heAg1]
    have hne0 := hAg1 i
    have hne2 := hAg01 (eAg01.symm (Fin.natAdd t0 i))
    generalize hc : cls (eAg2.symm (Fin.castAdd t2 (eAg01.symm (Fin.natAdd t0 i)))) = c at hne0 hne2 ⊢
    fin_cases c
    · exact absurd rfl hne0
    · rfl
    · exact absurd rfl hne2
  have hAg2_cls : ∀ i : Fin t2, cls (eAg.symm (Fin.natAdd (t0 + t1) i)) = 2 := fun i => by
    rw [heAg2]; have h := hAg2 i; push Not at h; exact h
  have ht0_pos : 0 < t0 := by
    rcases hno0 with ⟨i, hi⟩
    by_contra h0; have ht0z : t0 = 0 := by omega
    generalize hmem : eAg i = x
    revert hi hmem
    refine Fin.addCases (fun j01 => ?_) (fun j2 hi hmem => ?_) x
    · refine Fin.addCases (fun j0 _ _ => ?_) (fun j1 hi hmem => ?_) j01
      · exact absurd j0.2 (by omega)
      · have heq : i = eAg.symm (Fin.castAdd t2 (Fin.natAdd t0 j1)) := by rw [← hmem, Equiv.symm_apply_apply]
        rw [heq, hAg1_cls] at hi; exact absurd hi (by decide)
    · have heq : i = eAg.symm (Fin.natAdd (t0 + t1) j2) := by rw [← hmem, Equiv.symm_apply_apply]
      rw [heq, hAg2_cls] at hi; exact absurd hi (by decide)
  have ht1_pos : 0 < t1 := by
    rcases hno1 with ⟨i, hi⟩
    by_contra h0; have ht1z : t1 = 0 := by omega
    generalize hmem : eAg i = x
    revert hi hmem
    refine Fin.addCases (fun j01 => ?_) (fun j2 hi hmem => ?_) x
    · refine Fin.addCases (fun j0 hi hmem => ?_) (fun j1 _ _ => ?_) j01
      · have heq : i = eAg.symm (Fin.castAdd t2 (Fin.castAdd t1 j0)) := by rw [← hmem, Equiv.symm_apply_apply]
        rw [heq, hAg0_cls] at hi; exact absurd hi (by decide)
      · exact absurd j1.2 (by omega)
    · have heq : i = eAg.symm (Fin.natAdd (t0 + t1) j2) := by rw [← hmem, Equiv.symm_apply_apply]
      rw [heq, hAg2_cls] at hi; exact absurd hi (by decide)
  have ht2_pos : 0 < t2 := by
    rcases hno2 with ⟨i, hi⟩
    by_contra h0; have ht2z : t2 = 0 := by omega
    generalize hmem : eAg i = x
    revert hi hmem
    refine Fin.addCases (fun j01 => ?_) (fun j2 _ _ => ?_) x
    · refine Fin.addCases (fun j0 hi hmem => ?_) (fun j1 hi hmem => ?_) j01
      · have heq : i = eAg.symm (Fin.castAdd t2 (Fin.castAdd t1 j0)) := by rw [← hmem, Equiv.symm_apply_apply]
        rw [heq, hAg0_cls] at hi; exact absurd hi (by decide)
      · have heq : i = eAg.symm (Fin.castAdd t2 (Fin.natAdd t0 j1)) := by rw [← hmem, Equiv.symm_apply_apply]
        rw [heq, hAg1_cls] at hi; exact absurd hi (by decide)
    · exact absurd j2.2 (by omega)
  have hAg0_cost : ∀ (i : Fin t0) g, costAg (Fin.castAdd t2 (Fin.castAdd t1 i)) g = vN 0 g := fun i g => by
    simp [costAg, costN, hAg0_cls i]
  have hAg1_cost : ∀ (i : Fin t1) g, costAg (Fin.castAdd t2 (Fin.natAdd t0 i)) g = vN 1 g := fun i g => by
    simp [costAg, costN, hAg1_cls i]
  have hAg2_cost : ∀ (i : Fin t2) g, costAg (Fin.natAdd (t0 + t1) i) g = vN 2 g := fun i g => by
    simp [costAg, costN, hAg2_cls i]
  -- Step 4: Strip all-small chores D = {g | vN 0 g = 1 ∧ vN 1 g = 1 ∧ vN 2 g = 1}!
  obtain ⟨mAB, mD, eD, hNotD, hD⟩ :=
    equiv_partition_fin (fun g : Fin m => ¬ (vN 0 g = 1 ∧ vN 1 g = 1 ∧ vN 2 g = 1))
  let costD : Fin ((t0 + t1) + t2) → Fin (mAB + mD) → ℝ := fun i g' => costAg i (eD.symm g')
  suffices hexD : ∃ allocD : Fin (mAB + mD) → Fin ((t0 + t1) + t2), IsEFX costD allocD by
    rcases hexD with ⟨allocD, hefxD⟩
    exact ⟨fun g => allocD (eD g), isEFX_reindex_items eD costAg hefxD⟩
  have hcostD_ge1 : ∀ i g', 1 ≤ costD i g' := by
    intro i g'
    simp only [costD, costAg, costN]
    rcases hvN_biv (cls (eAg.symm i)) (eD.symm g') with h1 | hr'
    · linarith
    · linarith [hr (cls (eAg.symm i))]
  have hcostD_nn : ∀ i g', 0 ≤ costD i g' := fun i g' => by linarith [hcostD_ge1 i g']
  have hcostD_small : ∀ i (k : Fin mD) g', costD i (Fin.natAdd mAB k) ≤ costD i g' := by
    intro i k g'
    have hDk := hD k; push Not at hDk
    have hval1 : costD i (Fin.natAdd mAB k) = 1 := by
      simp only [costD, costAg, costN]
      generalize hc : cls (eAg.symm i) = c
      fin_cases c
      · exact hDk.1
      · exact hDk.2.1
      · exact hDk.2.2
    rw [hval1]; exact hcostD_ge1 i g'
  apply exists_efx_extend_all_small (by omega : 0 < (t0 + t1) + t2) costD hcostD_nn hcostD_small
  -- Step 5: Partition Fin mAB into A, B0, B1, B2!
  let costAB : Fin ((t0 + t1) + t2) → Fin mAB → ℝ := fun i g => costD i (Fin.castAdd mD g)
  let orig : Fin mAB → Fin m := fun g => eD.symm (Fin.castAdd mD g)
  obtain ⟨mAB01, nB2, e2, hNot2, hIs2⟩ := equiv_partition_fin (fun g : Fin mAB => vN 2 (orig g) ≠ 1)
  obtain ⟨mAB0, nB1, e1, hNot1, hIs1⟩ :=
    equiv_partition_fin (fun g : Fin mAB01 => vN 1 (orig (e2.symm (Fin.castAdd nB2 g))) ≠ 1)
  obtain ⟨nA, nB0, e0, hNot0, hIs0⟩ :=
    equiv_partition_fin (fun g : Fin mAB0 => vN 0 (orig (e2.symm (Fin.castAdd nB2 (e1.symm (Fin.castAdd nB1 g))))) ≠ 1)
  let e01 : Fin mAB01 ≃ Fin ((nA + nB0) + nB1) :=
    e1.trans ((finSumFinEquiv.symm.trans (e0.sumCongr (Equiv.refl (Fin nB1)))).trans finSumFinEquiv)
  let eAll : Fin mAB ≃ Fin (((nA + nB0) + nB1) + nB2) :=
    e2.trans ((finSumFinEquiv.symm.trans (e01.sumCongr (Equiv.refl (Fin nB2)))).trans finSumFinEquiv)
  let costNorm : Fin ((t0 + t1) + t2) → Fin (((nA + nB0) + nB1) + nB2) → ℝ :=
    fun i g => costAB i (eAll.symm g)
  suffices hexNorm : ∃ allocN : Fin (((nA + nB0) + nB1) + nB2) → Fin ((t0 + t1) + t2), IsEFX costNorm allocN by
    rcases hexNorm with ⟨allocN, hefxN⟩
    exact ⟨fun g => allocN (eAll g), isEFX_reindex_items eAll costAB hefxN⟩
  have heAll_A : ∀ g : Fin nA,
      eAll.symm (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.castAdd nB0 g))) =
        e2.symm (Fin.castAdd nB2 (e1.symm (Fin.castAdd nB1 (e0.symm (Fin.castAdd nB0 g))))) := by
    intro g
    have hL2 : (finSumFinEquiv : Fin ((nA + nB0) + nB1) ⊕ Fin nB2 ≃ Fin (((nA + nB0) + nB1) + nB2)).symm
        (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.castAdd nB0 g))) = Sum.inl (Fin.castAdd nB1 (Fin.castAdd nB0 g)) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    have hL1 : (finSumFinEquiv : Fin (nA + nB0) ⊕ Fin nB1 ≃ Fin ((nA + nB0) + nB1)).symm
        (Fin.castAdd nB1 (Fin.castAdd nB0 g)) = Sum.inl (Fin.castAdd nB0 g) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eAll, e01, hL2, hL1]
  have heAll_B0 : ∀ g : Fin nB0,
      eAll.symm (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.natAdd nA g))) =
        e2.symm (Fin.castAdd nB2 (e1.symm (Fin.castAdd nB1 (e0.symm (Fin.natAdd nA g))))) := by
    intro g
    have hL2 : (finSumFinEquiv : Fin ((nA + nB0) + nB1) ⊕ Fin nB2 ≃ Fin (((nA + nB0) + nB1) + nB2)).symm
        (Fin.castAdd nB2 (Fin.castAdd nB1 (Fin.natAdd nA g))) = Sum.inl (Fin.castAdd nB1 (Fin.natAdd nA g)) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    have hL1 : (finSumFinEquiv : Fin (nA + nB0) ⊕ Fin nB1 ≃ Fin ((nA + nB0) + nB1)).symm
        (Fin.castAdd nB1 (Fin.natAdd nA g)) = Sum.inl (Fin.natAdd nA g) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eAll, e01, hL2, hL1]
  have heAll_B1 : ∀ g : Fin nB1,
      eAll.symm (Fin.castAdd nB2 (Fin.natAdd (nA + nB0) g)) =
        e2.symm (Fin.castAdd nB2 (e1.symm (Fin.natAdd mAB0 g))) := by
    intro g
    have hL2 : (finSumFinEquiv : Fin ((nA + nB0) + nB1) ⊕ Fin nB2 ≃ Fin (((nA + nB0) + nB1) + nB2)).symm
        (Fin.castAdd nB2 (Fin.natAdd (nA + nB0) g)) = Sum.inl (Fin.natAdd (nA + nB0) g) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    have hR1 : (finSumFinEquiv : Fin (nA + nB0) ⊕ Fin nB1 ≃ Fin ((nA + nB0) + nB1)).symm
        (Fin.natAdd (nA + nB0) g) = Sum.inr g :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eAll, e01, hL2, hR1]
  have heAll_B2 : ∀ g : Fin nB2,
      eAll.symm (Fin.natAdd ((nA + nB0) + nB1) g) = e2.symm (Fin.natAdd mAB01 g) := by
    intro g
    have hR2 : (finSumFinEquiv : Fin ((nA + nB0) + nB1) ⊕ Fin nB2 ≃ Fin (((nA + nB0) + nB1) + nB2)).symm
        (Fin.natAdd ((nA + nB0) + nB1) g) = Sum.inr g :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eAll, hR2]
  -- Helper: from ¬ D and h_no_two_light, if vN b (orig g) = 1 then vN b' (orig g) = r b' for b' ≠ b!
  have huniq_light : ∀ (g : Fin mAB) (b b' : Fin 3), b ≠ b' → vN b (orig g) = 1 → vN b' (orig g) = r b' := by
    intro g b b' hne h1
    rcases hvN_biv b' (orig g) with h1' | hr'
    · exfalso
      have hND := hNotD g
      have hnt := h_no_two_light (orig g)
      have hp0 := (hvN_one_iff 0 (orig g)).mp
      have hp1 := (hvN_one_iff 1 (orig g)).mp
      have hp2 := (hvN_one_iff 2 (orig g)).mp
      have hq0 := (hvN_one_iff 0 (orig g)).mpr
      have hq1 := (hvN_one_iff 1 (orig g)).mpr
      have hq2 := (hvN_one_iff 2 (orig g)).mpr
      fin_cases b <;> fin_cases b'
      · exact hne rfl
      · exact hND ⟨h1, h1', hq2 (hnt.1 ⟨hp0 h1, hp1 h1'⟩)⟩
      · exact hND ⟨h1, hq1 (hnt.2.1 ⟨hp0 h1, hp2 h1'⟩), h1'⟩
      · exact hND ⟨h1', h1, hq2 (hnt.1 ⟨hp0 h1', hp1 h1⟩)⟩
      · exact hne rfl
      · exact hND ⟨hq0 (hnt.2.2 ⟨hp1 h1, hp2 h1'⟩), h1, h1'⟩
      · exact hND ⟨h1', hq1 (hnt.2.1 ⟨hp0 h1', hp2 h1⟩), h1⟩
      · exact hND ⟨hq0 (hnt.2.2 ⟨hp1 h1', hp2 h1⟩), h1', h1⟩
      · exact hne rfl
    · exact hr'
  obtain ⟨S⟩ := exists_threeTypeSpec (nA := nA) (nB0 := nB0) (nB1 := nB1) (nB2 := nB2)
    ht0_pos ht1_pos ht2_pos (hr 0) (hr 1) (hr 2)
  refine realize_threeTypeSpec (hr 0) (hr 1) (hr 2) costNorm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ S
  · intro i g; simp only [costNorm, costAB, costD, hAg0_cost, heAll_A]
    exact (hvN_biv 0 _).resolve_left (hNot0 g)
  · intro i g; simp only [costNorm, costAB, costD, hAg1_cost, heAll_A]
    exact (hvN_biv 1 _).resolve_left (hNot1 (e0.symm (Fin.castAdd nB0 g)))
  · intro i g; simp only [costNorm, costAB, costD, hAg2_cost, heAll_A]
    exact (hvN_biv 2 _).resolve_left (hNot2 (e1.symm (Fin.castAdd nB1 (e0.symm (Fin.castAdd nB0 g)))))
  · intro i g; simp only [costNorm, costAB, costD, hAg0_cost, heAll_B0]
    have h := hIs0 g; push Not at h; exact h
  · intro i g; simp only [costNorm, costAB, costD, hAg1_cost, heAll_B0]
    have h := hIs0 g; push Not at h
    exact huniq_light (e2.symm (Fin.castAdd nB2 (e1.symm (Fin.castAdd nB1 (e0.symm (Fin.natAdd nA g)))))) 0 1 (by decide) h
  · intro i g; simp only [costNorm, costAB, costD, hAg2_cost, heAll_B0]
    have h := hIs0 g; push Not at h
    exact huniq_light (e2.symm (Fin.castAdd nB2 (e1.symm (Fin.castAdd nB1 (e0.symm (Fin.natAdd nA g)))))) 0 2 (by decide) h
  · intro i g; simp only [costNorm, costAB, costD, hAg0_cost, heAll_B1]
    have h := hIs1 g; push Not at h
    exact huniq_light (e2.symm (Fin.castAdd nB2 (e1.symm (Fin.natAdd mAB0 g)))) 1 0 (by decide) h
  · intro i g; simp only [costNorm, costAB, costD, hAg1_cost, heAll_B1]
    have h := hIs1 g; push Not at h; exact h
  · intro i g; simp only [costNorm, costAB, costD, hAg2_cost, heAll_B1]
    have h := hIs1 g; push Not at h
    exact huniq_light (e2.symm (Fin.castAdd nB2 (e1.symm (Fin.natAdd mAB0 g)))) 1 2 (by decide) h
  · intro i g; simp only [costNorm, costAB, costD, hAg0_cost, heAll_B2]
    have h := hIs2 g; push Not at h
    exact huniq_light (e2.symm (Fin.natAdd mAB01 g)) 2 0 (by decide) h
  · intro i g; simp only [costNorm, costAB, costD, hAg1_cost, heAll_B2]
    have h := hIs2 g; push Not at h
    exact huniq_light (e2.symm (Fin.natAdd mAB01 g)) 2 1 (by decide) h
  · intro i g; simp only [costNorm, costAB, costD, hAg2_cost, heAll_B2]
    have h := hIs2 g; push Not at h; exact h

end BivaluedChoresEFX
