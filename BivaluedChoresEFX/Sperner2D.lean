module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic

/-!
# 2D Discrete Sperner's Lemma on the Triangular Simplex Grid

This module provides a self-contained, elementary `ZMod 2` parity proof of the **2D Discrete
Sperner's Lemma** (`sperner_2d`) on the simplex
`Δ_N = {(a, b, c) ∈ ℕ³ : a + b + c = N}` (parameterized by `(a, b)` with `a + b ≤ N` and
`c = N - a - b`).

Given any 3-coloring `col : ℕ → ℕ → Fin 3` satisfying the Sperner boundary conditions:
* `a = 0 → col 0 b ≠ 0`
* `b = 0 → col a 0 ≠ 1`
* `a + b = N → col a b ≠ 2`

there exists either:
* a **rainbow up-triangle** `(a + 1, b), (a, b + 1), (a, b)` (`a + b < N`), or
* a **rainbow down-triangle** `(a, b + 1), (a + 1, b), (a + 1, b + 1)` (`a + b + 1 < N`).
-/

@[expose] public section

namespace BivaluedChoresEFX

open scoped BigOperators

/-- Predicate that three colors in `Fin 3` are pairwise distinct (a rainbow triple). -/
def IsRainbow (x y z : Fin 3) : Prop :=
  x ≠ y ∧ y ≠ z ∧ z ≠ x

instance (x y z : Fin 3) : Decidable (IsRainbow x y z) := by
  unfold IsRainbow; infer_instance

/-- Door indicator in `ZMod 2`: `1` iff the edge has endpoints colored `{0, 1}`. -/
private def isDoor (u v : Fin 3) : ZMod 2 :=
  if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) then 1 else 0

/-- Parity indicator of color `0` in `ZMod 2`. -/
private def isZeroColor (u : Fin 3) : ZMod 2 :=
  if u = 0 then 1 else 0

private lemma isDoor_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma door_sum_eq_rainbow (x y z : Fin 3) :
    isDoor x y + isDoor y z + isDoor z x = if IsRainbow x y z then (1 : ZMod 2) else 0 := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

private lemma isDoor_eq_zero_of_ne_zero {u v : Fin 3} (hu : u ≠ 0) (hv : v ≠ 0) :
    isDoor u v = 0 := by
  fin_cases u <;> fin_cases v <;> simp_all [isDoor]

private lemma isDoor_eq_zero_of_ne_one {u v : Fin 3} (hu : u ≠ 1) (hv : v ≠ 1) :
    isDoor u v = 0 := by
  fin_cases u <;> fin_cases v <;> simp_all [isDoor]

private lemma isDoor_eq_xor_of_ne_two {u v : Fin 3} (hu : u ≠ 2) (hv : v ≠ 2) :
    isDoor u v = isZeroColor u + isZeroColor v := by
  fin_cases u <;> fin_cases v <;> first | exact absurd rfl hu | exact absurd rfl hv | decide

private lemma color_eq_zero_of_ne_one_two {u : Fin 3} (h1 : u ≠ 1) (h2 : u ≠ 2) : u = 0 := by
  fin_cases u <;> simp_all

/-- Row-wise triangular index set `{(a, b) | a + b < K}` expressed as a `Finset (ℕ × ℕ)`. -/
private def triGrid (K : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range K ×ˢ Finset.range K).filter (fun p => p.1 + p.2 < K)

private lemma mem_triGrid {K : ℕ} {p : ℕ × ℕ} : p ∈ triGrid K ↔ p.1 + p.2 < K := by
  simp only [triGrid, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- Telescoping identity in `ZMod 2` over `Finset.range N`. -/
private lemma sum_range_add_zmod2 (f : ℕ → ZMod 2) (N : ℕ) :
    ∑ k ∈ Finset.range N, (f (k + 1) + f k) = f N + f 0 := by
  induction N with
  | zero => simp [isDoor_add_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hself : f N + f N = 0 := isDoor_add_self (f N)
    calc (f N + f 0) + (f (N + 1) + f N)
        = (f N + f N) + (f (N + 1) + f 0) := by ring
      _ = f (N + 1) + f 0 := by rw [hself, zero_add]

/-- **2D Discrete Sperner's Lemma**: any Sperner-compliant 3-coloring of the grid
`{(a, b) : a + b ≤ N}` (`N ≥ 1`) contains either a rainbow up-triangle or a rainbow
down-triangle. -/
theorem sperner_2d {N : ℕ} (hN : 1 ≤ N)
    (col : ℕ → ℕ → Fin 3)
    (h0 : ∀ b ≤ N, col 0 b ≠ 0)
    (h1 : ∀ a ≤ N, col a 0 ≠ 1)
    (h2 : ∀ a b, a + b = N → col a b ≠ 2) :
    (∃ a b, a + b < N ∧ IsRainbow (col (a + 1) b) (col a (b + 1)) (col a b)) ∨
    (∃ a b, a + b + 1 < N ∧ IsRainbow (col a (b + 1)) (col (a + 1) b) (col (a + 1) (b + 1))) := by
  -- Edge door indicators
  let H : ℕ × ℕ → ZMod 2 := fun p => isDoor (col p.1 p.2) (col (p.1 + 1) p.2)
  let V : ℕ × ℕ → ZMod 2 := fun p => isDoor (col p.1 p.2) (col p.1 (p.2 + 1))
  let S : ℕ × ℕ → ZMod 2 := fun p => isDoor (col (p.1 + 1) p.2) (col p.1 (p.2 + 1))
  -- Sum of rainbow indicators over all up-triangles and down-triangles
  let sumUp : ZMod 2 :=
    ∑ p ∈ triGrid N, if IsRainbow (col (p.1 + 1) p.2) (col p.1 (p.2 + 1)) (col p.1 p.2) then 1 else 0
  let sumDown : ZMod 2 :=
    ∑ p ∈ triGrid (N - 1),
      if IsRainbow (col p.1 (p.2 + 1)) (col (p.1 + 1) p.2) (col (p.1 + 1) (p.2 + 1)) then 1 else 0
  -- Express sumUp in terms of H, V, S
  have hUp_eq : sumUp = (∑ p ∈ triGrid N, S p) + (∑ p ∈ triGrid N, V p) + (∑ p ∈ triGrid N, H p) := by
    simp only [sumUp]
    have hpt : ∀ p ∈ triGrid N,
        (if IsRainbow (col (p.1 + 1) p.2) (col p.1 (p.2 + 1)) (col p.1 p.2) then (1 : ZMod 2) else 0) =
          S p + V p + H p := by
      intro p _
      rw [← door_sum_eq_rainbow (col (p.1 + 1) p.2) (col p.1 (p.2 + 1)) (col p.1 p.2)]
      simp only [S, V, H, isDoor]
      -- Symmetry of isDoor in its arguments
      have hsym : ∀ u v : Fin 3,
          (if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) then (1 : ZMod 2) else 0) =
          (if (v = 0 ∧ u = 1) ∨ (v = 1 ∧ u = 0) then (1 : ZMod 2) else 0) := by
        intro u v; fin_cases u <;> fin_cases v <;> decide
      rw [hsym (col p.1 (p.2 + 1)) (col p.1 p.2), hsym (col p.1 p.2) (col (p.1 + 1) p.2)]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Express sumDown in terms of S, shifted H, shifted V
  have hDown_eq : sumDown =
      (∑ p ∈ triGrid (N - 1), S p) +
      (∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2)) +
      (∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1)) := by
    simp only [sumDown]
    have hpt : ∀ p ∈ triGrid (N - 1),
        (if IsRainbow (col p.1 (p.2 + 1)) (col (p.1 + 1) p.2) (col (p.1 + 1) (p.2 + 1))
          then (1 : ZMod 2) else 0) =
          S p + V (p.1 + 1, p.2) + H (p.1, p.2 + 1) := by
      intro p _
      rw [← door_sum_eq_rainbow (col p.1 (p.2 + 1)) (col (p.1 + 1) p.2) (col (p.1 + 1) (p.2 + 1))]
      simp only [S, V, H, isDoor]
      have hsym : ∀ u v : Fin 3,
          (if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) then (1 : ZMod 2) else 0) =
          (if (v = 0 ∧ u = 1) ∨ (v = 1 ∧ u = 0) then (1 : ZMod 2) else 0) := by
        intro u v; fin_cases u <;> fin_cases v <;> decide
      rw [hsym (col p.1 (p.2 + 1)) (col (p.1 + 1) p.2),
          hsym (col (p.1 + 1) p.2) (col (p.1 + 1) (p.2 + 1)),
          hsym (col (p.1 + 1) (p.2 + 1)) (col p.1 (p.2 + 1))]
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Cancel H on interior (b ≥ 1) and show H = 0 on boundary b = 0!
  have hH_eq : ∑ p ∈ triGrid N, H p = ∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1) := by
    rw [← Finset.sum_filter_add_sum_filter_not (triGrid N) (fun p => p.2 = 0)]
    have hHb0 : ∑ p ∈ (triGrid N).filter (fun p => p.2 = 0), H p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [Finset.mem_filter, mem_triGrid] at hp
      have hb0 : p.2 = 0 := hp.2
      simp only [H, hb0]
      exact isDoor_eq_zero_of_ne_one (h1 p.1 (by omega)) (h1 (p.1 + 1) (by omega))
    rw [hHb0, zero_add]
    refine Finset.sum_nbij (fun p => (p.1, p.2 - 1)) ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, mem_triGrid] at hp ⊢; omega
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, mem_triGrid] at hp₁ hp₂
      dsimp only at heq
      rcases Prod.mk.inj heq with ⟨h1', h2'⟩
      exact Prod.ext h1' (by omega)
    · intro q hq
      simp only [Finset.mem_coe, mem_triGrid] at hq
      refine ⟨(q.1, q.2 + 1), ?_, by simp⟩
      simp only [Finset.mem_coe, Finset.mem_filter, mem_triGrid]; omega
    · intro p hp
      simp only [Finset.mem_filter, mem_triGrid] at hp
      have : p.2 - 1 + 1 = p.2 := by omega
      simp [this]
  -- Cancel V on interior (a ≥ 1) and show V = 0 on boundary a = 0!
  have hV_eq : ∑ p ∈ triGrid N, V p = ∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2) := by
    rw [← Finset.sum_filter_add_sum_filter_not (triGrid N) (fun p => p.1 = 0)]
    have hVa0 : ∑ p ∈ (triGrid N).filter (fun p => p.1 = 0), V p = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      simp only [Finset.mem_filter, mem_triGrid] at hp
      have ha0 : p.1 = 0 := hp.2
      simp only [V, ha0]
      exact isDoor_eq_zero_of_ne_zero (h0 p.2 (by omega)) (h0 (p.2 + 1) (by omega))
    rw [hVa0, zero_add]
    refine Finset.sum_nbij (fun p => (p.1 - 1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, mem_triGrid] at hp ⊢; omega
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, mem_triGrid] at hp₁ hp₂
      dsimp only at heq
      rcases Prod.mk.inj heq with ⟨h1', h2'⟩
      exact Prod.ext (by omega) h2'
    · intro q hq
      simp only [Finset.mem_coe, mem_triGrid] at hq
      refine ⟨(q.1 + 1, q.2), ?_, by simp⟩
      simp only [Finset.mem_coe, Finset.mem_filter, mem_triGrid]; omega
    · intro p hp
      simp only [Finset.mem_filter, mem_triGrid] at hp
      have : p.1 - 1 + 1 = p.1 := by omega
      simp [this]
  -- Split S on triGrid N into triGrid (N - 1) + diagonal a + b = N - 1!
  have hS_split : ∑ p ∈ triGrid N, S p =
      (∑ p ∈ triGrid (N - 1), S p) + ∑ a ∈ Finset.range N, S (a, N - 1 - a) := by
    rw [← Finset.sum_filter_add_sum_filter_not (triGrid N) (fun p => p.1 + p.2 < N - 1)]
    have hleft : (triGrid N).filter (fun p => p.1 + p.2 < N - 1) = triGrid (N - 1) := by
      ext p; simp only [Finset.mem_filter, mem_triGrid]; omega
    rw [hleft]
    congr 1
    refine Finset.sum_nbij (fun p => p.1) ?_ ?_ ?_ ?_
    · intro p hp; simp only [Finset.mem_filter, mem_triGrid, Finset.mem_range] at hp ⊢; omega
    · intro p₁ hp₁ p₂ hp₂ heq
      simp only [Finset.mem_coe, Finset.mem_filter, mem_triGrid] at hp₁ hp₂
      dsimp only at heq
      exact Prod.ext heq (by omega)
    · intro a ha
      simp only [Finset.mem_coe, Finset.mem_range] at ha
      refine ⟨(a, N - 1 - a), ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_filter, mem_triGrid]; omega
    · intro p hp
      simp only [Finset.mem_filter, mem_triGrid] at hp
      have : N - 1 - p.1 = p.2 := by omega
      rw [this]
  -- Evaluate the diagonal sum of S by telescoping in ZMod 2!
  have hdiag : ∑ a ∈ Finset.range N, S (a, N - 1 - a) = 1 := by
    let f : ℕ → ZMod 2 := fun k => isZeroColor (col k (N - k))
    have hterm : ∀ a ∈ Finset.range N, S (a, N - 1 - a) = f (a + 1) + f a := by
      intro a ha
      rw [Finset.mem_range] at ha
      simp only [S, f]
      have hsub1 : N - (a + 1) = N - 1 - a := by omega
      have hsub2 : N - a = N - 1 - a + 1 := by omega
      rw [hsub1, hsub2]
      exact isDoor_eq_xor_of_ne_two
        (h2 (a + 1) (N - 1 - a) (by omega))
        (h2 a (N - 1 - a + 1) (by omega))
    rw [Finset.sum_congr rfl hterm, sum_range_add_zmod2 f N]
    have hcolN : col N 0 = 0 := color_eq_zero_of_ne_one_two (h1 N (le_refl N)) (h2 N 0 (by omega))
    have hcol0 : col 0 N ≠ 0 := h0 N (le_refl N)
    simp only [f, Nat.sub_self, Nat.sub_zero, hcolN, isZeroColor, ↓reduceIte, ite_eq_right hcol0, add_zero]
  -- Combine: sumUp + sumDown = 1 in ZMod 2!
  have htot : sumUp + sumDown = 1 := by
    rw [hUp_eq, hDown_eq, hH_eq, hV_eq, hS_split]
    have hS0 : (∑ p ∈ triGrid (N - 1), S p) + (∑ p ∈ triGrid (N - 1), S p) = 0 := isDoor_add_self _
    have hV0 : (∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2)) + (∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2)) = 0 :=
      isDoor_add_self _
    have hH0 : (∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1)) + (∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1)) = 0 :=
      isDoor_add_self _
    calc ((∑ p ∈ triGrid (N - 1), S p) + ∑ a ∈ Finset.range N, S (a, N - 1 - a)) +
          (∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2)) +
          (∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1)) +
          ((∑ p ∈ triGrid (N - 1), S p) +
          (∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2)) +
          (∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1)))
        = ((∑ p ∈ triGrid (N - 1), S p) + (∑ p ∈ triGrid (N - 1), S p)) +
          ((∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2)) + (∑ p ∈ triGrid (N - 1), V (p.1 + 1, p.2))) +
          ((∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1)) + (∑ p ∈ triGrid (N - 1), H (p.1, p.2 + 1))) +
          ∑ a ∈ Finset.range N, S (a, N - 1 - a) := by ring
      _ = 0 + 0 + 0 + 1 := by rw [hS0, hV0, hH0, hdiag]
      _ = 1 := by simp
  -- Conclude: at least one of sumUp or sumDown is nonzero!
  by_contra hno
  push Not at hno
  rcases hno with ⟨hnoUp, hnoDown⟩
  have hUp0 : sumUp = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [mem_triGrid] at hp
    exact ite_eq_right (hnoUp p.1 p.2 hp)
  have hDown0 : sumDown = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [mem_triGrid] at hp
    exact ite_eq_right (hnoDown p.1 p.2 (by omega))
  rw [hUp0, hDown0, add_zero] at htot
  exact absurd htot (by decide)

end BivaluedChoresEFX
