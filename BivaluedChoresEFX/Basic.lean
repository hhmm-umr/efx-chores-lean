module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Basic Definitions for Additive Chores and EFX Allocations

This module defines:
* `bundle alloc i`: the set of chores assigned to agent `i` under a complete allocation
  `alloc : Fin m → Fin n`.
* `bundleCost cost S i`: agent `i`'s additive disutility for a bundle `S : Finset (Fin m)`.
* `IsEFX cost alloc`: envy-freeness up to any chore (EFX).
* Invariance lemmas under positive agent-wise scaling, agent reindexing, and item reindexing.
* `TwoTypeBundle`: abstract `(nA, nB, nC)` count representation and its realization into a
  concrete allocation `Fin m → Fin n` for normalized two-agent-type instances without all-small
  chores.
-/

@[expose] public section

namespace BivaluedChoresEFX

open scoped BigOperators

/-- The bundle of chores assigned to agent `i` under complete allocation `alloc`. -/
def bundle {n m : ℕ} (alloc : Fin m → Fin n) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun g => alloc g = i)

/-- Agent `i`'s additive disutility for a bundle `S` of chores. -/
def bundleCost {n m : ℕ} (cost : Fin n → Fin m → ℝ) (S : Finset (Fin m)) (i : Fin n) : ℝ :=
  ∑ g ∈ S, cost i g

/-- An allocation `alloc : Fin m → Fin n` is EFX (envy-free up to any chore) if for every pair
of agents `i, j` and every chore `g` in `i`'s bundle, removing `g` from `i`'s bundle makes its
disutility at most `i`'s disutility for `j`'s bundle. -/
def IsEFX {n m : ℕ} (cost : Fin n → Fin m → ℝ) (alloc : Fin m → Fin n) : Prop :=
  ∀ (i j : Fin n) (g : Fin m), g ∈ bundle alloc i →
    bundleCost cost (bundle alloc i \ {g}) i ≤ bundleCost cost (bundle alloc j) i

@[simp]
lemma mem_bundle {n m : ℕ} {alloc : Fin m → Fin n} {i : Fin n} {g : Fin m} :
    g ∈ bundle alloc i ↔ alloc g = i := by
  simp [bundle]

lemma bundleCost_empty {n m : ℕ} (cost : Fin n → Fin m → ℝ) (i : Fin n) :
    bundleCost cost ∅ i = 0 := by
  simp [bundleCost]

lemma bundleCost_sdiff_singleton {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    {S : Finset (Fin m)} {g : Fin m} (hg : g ∈ S) (i : Fin n) :
    bundleCost cost (S \ {g}) i = bundleCost cost S i - cost i g := by
  unfold bundleCost
  have h := Finset.add_sum_erase S (fun x => cost i x) hg
  have hs : S \ {g} = S.erase g := by
    ext x
    simp [Finset.mem_erase, and_comm]
  rw [hs]
  linarith

lemma bundleCost_insert {n m : ℕ} (cost : Fin n → Fin m → ℝ)
    {S : Finset (Fin m)} {g : Fin m} (hg : g ∉ S) (i : Fin n) :
    bundleCost cost (insert g S) i = bundleCost cost S i + cost i g := by
  unfold bundleCost
  rw [Finset.sum_insert hg, add_comm]

lemma bundleCost_nonneg {n m : ℕ} {cost : Fin n → Fin m → ℝ} {i : Fin n}
    (hpos : ∀ g, 0 ≤ cost i g) (S : Finset (Fin m)) :
    0 ≤ bundleCost cost S i :=
  Finset.sum_nonneg (fun g _ => hpos g)

lemma bundleCost_mono {n m : ℕ} {cost : Fin n → Fin m → ℝ} {i : Fin n}
    (hpos : ∀ g, 0 ≤ cost i g) {S T : Finset (Fin m)} (hST : S ⊆ T) :
    bundleCost cost S i ≤ bundleCost cost T i :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun g _ _ => hpos g)

/-- Positive agent-wise scaling of disutilities preserves EFX. -/
lemma isEFX_scale {n m : ℕ} {cost cost' : Fin n → Fin m → ℝ}
    (s : Fin n → ℝ) (hs : ∀ i, 0 < s i)
    (hrel : ∀ i g, cost' i g = s i * cost i g)
    {alloc : Fin m → Fin n} :
    IsEFX cost' alloc ↔ IsEFX cost alloc := by
  have hsum : ∀ (S : Finset (Fin m)) (i : Fin n),
      bundleCost cost' S i = s i * bundleCost cost S i := by
    intro S i
    simp [bundleCost, hrel, Finset.mul_sum]
  constructor
  · intro h i j g hg
    have hij := h i j g hg
    rw [hsum, hsum] at hij
    exact le_of_mul_le_mul_left hij (hs i)
  · intro h i j g hg
    rw [hsum, hsum]
    exact mul_le_mul_of_nonneg_left (h i j g hg) (le_of_lt (hs i))

/-- Reindexing agents along an equivalence preserves EFX. -/
lemma isEFX_reindex_agents {n n' m : ℕ} (e : Fin n ≃ Fin n')
    (cost : Fin n → Fin m → ℝ) {alloc' : Fin m → Fin n'}
    (h : IsEFX (fun i' g => cost (e.symm i') g) alloc') :
    IsEFX cost (fun g => e.symm (alloc' g)) := by
  intro i j g hg
  have hb : ∀ k : Fin n, bundle (fun g => e.symm (alloc' g)) k = bundle alloc' (e k) := by
    intro k
    ext x
    simp [bundle, e.symm_apply_eq]
  rw [hb i] at hg ⊢
  rw [hb j]
  have hij := h (e i) (e j) g hg
  simpa [bundleCost] using hij

/-- Reindexing items along an equivalence preserves EFX. -/
lemma isEFX_reindex_items {n m m' : ℕ} (e : Fin m ≃ Fin m')
    (cost : Fin n → Fin m → ℝ) {alloc' : Fin m' → Fin n}
    (h : IsEFX (fun i g' => cost i (e.symm g')) alloc') :
    IsEFX cost (fun g => alloc' (e g)) := by
  intro i j g hg
  have hg' : e g ∈ bundle alloc' i := by
    simpa [bundle] using hg
  have hij := h i j (e g) hg'
  have hmap_bundle : ∀ k : Fin n,
      bundleCost cost (bundle (fun x => alloc' (e x)) k) i =
      bundleCost (fun a x' => cost a (e.symm x')) (bundle alloc' k) i := by
    intro k
    unfold bundleCost
    refine Finset.sum_nbij (fun x => e x) ?_ ?_ ?_ ?_
    · intro x hx
      simpa [bundle] using hx
    · intro x _ y _ hxy
      exact e.injective hxy
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      simpa [bundle] using hy
    · intro x _
      simp
  rw [bundleCost_sdiff_singleton cost hg]
  rw [bundleCost_sdiff_singleton (fun a x' => cost a (e.symm x')) hg'] at hij
  rw [hmap_bundle i, hmap_bundle j]
  simpa using hij

/-- If there are no chores, any allocation is vacuously EFX. -/
lemma isEFX_of_zero_items {n : ℕ} (cost : Fin n → Fin 0 → ℝ) (alloc : Fin 0 → Fin n) :
    IsEFX cost alloc := by
  intro _ _ g
  exact Fin.elim0 g

/-- If there is only one agent and disutilities are nonnegative, any allocation is EFX. -/
lemma isEFX_of_one_agent {m : ℕ} {cost : Fin 1 → Fin m → ℝ}
    (hnn : ∀ i g, 0 ≤ cost i g) (alloc : Fin m → Fin 1) :
    IsEFX cost alloc := by
  intro i j g hg
  have hij : i = j := Subsingleton.elim i j
  subst hij
  rw [bundleCost_sdiff_singleton cost hg]
  linarith [hnn i g]

/-- Helper: given nonnegative counts `cnt : Fin k → ℕ` summing to `M`, construct a surjective
assignment `f : Fin M → Fin k` whose fibers have exact cardinalities `cnt i`. -/
lemma exists_assignment_with_counts {k M : ℕ} (cnt : Fin k → ℕ)
    (hsum : ∑ i : Fin k, cnt i = M) :
    ∃ f : Fin M → Fin k, ∀ i : Fin k, (Finset.univ.filter (fun x => f x = i)).card = cnt i := by
  classical
  induction k generalizing M with
  | zero =>
    have hM : M = 0 := by simpa using hsum.symm
    subst hM
    exact ⟨fun x => Fin.elim0 x, fun i => Fin.elim0 i⟩
  | succ k ih =>
    let M' := ∑ i : Fin k, cnt i.castSucc
    have hsplit : M' + cnt (Fin.last k) = M := by
      simpa [M', Fin.sum_univ_castSucc] using hsum
    obtain ⟨f', hf'⟩ := ih (fun i => cnt i.castSucc) rfl
    let f : Fin M → Fin (k + 1) := fun x =>
      if hx : x.1 < M' then
        (f' ⟨x.1, hx⟩).castSucc
      else
        Fin.last k
    refine ⟨f, fun i => ?_⟩
    refine Fin.lastCases ?_ ?_ i
    · -- i = Fin.last k
      have hfilt : Finset.univ.filter (fun x : Fin M => f x = Fin.last k) =
          Finset.univ.filter (fun x : Fin M => ¬ x.1 < M') := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
        split_ifs with hx
        · simp [Fin.castSucc_ne_last, hx]
        · simp [hx]
      rw [hfilt]
      have hcard : (Finset.univ : Finset (Fin (cnt (Fin.last k)))).card =
          (Finset.univ.filter (fun x : Fin M => ¬ x.1 < M')).card := by
        refine Finset.card_nbij (fun y => ⟨M' + y.1, by omega⟩) ?_ ?_ ?_
        · intro y _; simp
        · intro y₁ _ y₂ _ hxy
          have hval : M' + y₁.1 = M' + y₂.1 := congrArg Fin.val hxy
          exact Fin.ext (by omega)
        · intro x hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
          refine ⟨⟨x.1 - M', by omega⟩, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
          ext; simp; omega
      simpa using hcard.symm
    · -- i = j.castSucc
      intro j
      have hfilt : Finset.univ.filter (fun x : Fin M => f x = j.castSucc) =
          (Finset.univ.filter (fun y : Fin M' => f' y = j)).map
            (Fin.castLEEmb (by omega : M' ≤ M)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
          Fin.castLEEmb_apply, f]
        constructor
        · intro hx
          split_ifs at hx with hlt
          · refine ⟨⟨x.1, hlt⟩, ?_, by ext; rfl⟩
            exact Fin.castSucc_inj.mp hx
          · exact absurd hx (Fin.castSucc_ne_last j).symm
        · rintro ⟨y, hy, rfl⟩
          simp [y.2, hy]
      rw [hfilt, Finset.card_map, hf' j]

end BivaluedChoresEFX
