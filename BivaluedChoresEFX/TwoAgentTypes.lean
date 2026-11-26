module

public import BivaluedChoresEFX.IdenticalAgents
public import BivaluedChoresEFX.Reductions
public import Mathlib.Data.Fintype.EquivFin

/-!
# EFX Existence for Personalized Bi-Valued Additive Chores with Two Agent Types

This module proves the main theorem (`exists_efx_two_agent_types_bivalued`):
for **every** `n ≥ 1`, **every** `m ≥ 0`, and **every** personalized bi-valued additive chores
instance with two types of agents (`T₁` with costs `{p₁, q₁}` and `T₂` with costs `{p₂, q₂}`,
`0 < p_b ≤ q_b`), there always exists a complete EFX allocation.

## Proof Architecture
1. **Normalization**: scale each type by `1 / p_b > 0` so costs lie in `{1, r_b}` with `1 < r_b`.
2. **Degenerate single-type cases** (`t₁ = 0` or `t₂ = 0`): solved directly by `IdenticalEFX`
   (`exists_efx_identical_bivalued`).
3. **Partitioning chores** into `A` (all-large), `B` (small for `T₁`, large for `T₂`),
   `C` (large for `T₁`, small for `T₂`), and `D` (all-small).
4. **Discrete Bolzano Walk + Phase-2 Single-Item Bridge** (`exists_twoTypeSpec`):
   * Phase 1 (`B` moves `0 → nB`) and Phase 3 (`C` moves `0 → nC`) admit no envy jump
     (`phase1_bundle_lower_bound` + symmetry `TwoTypeSpec.swap`).
   * At any Phase-2 envy jump `E₂(a₁) ∧ E₁(a₁ + 1)`, Lemmas A, B, and C pin
     `M₁(a₁) = M₂(a₂ - 1) = Mstar ≥ 1` and guarantee that at least one of the two single-item
     bridge states `B_moveB = (a₁ + 1, nB - 1, 0 | a₂ - 1, 1, nC)` or
     `B_moveC = (a₁, nB, 1 | a₂, 0, nC - 1)` is EFX.
5. **Realization & All-Small Insertion**: realize the `TwoTypeSpec` as a concrete allocation on
   `A ∪ B ∪ C` (`realize_twoTypeSpec`), then insert all `D`-chores via
   `exists_efx_extend_all_small`.
-/

@[expose] public section

namespace BivaluedChoresEFX

open scoped BigOperators

/-! ### Helper Combinatorial Lemmas -/

/-- **Discrete Bolzano Crossing Lemma**: if `¬ E₁ 0` and `¬ E₂ L`, then either there is an index
`k ≤ L` where both `¬ E₁ k` and `¬ E₂ k` hold, or there is a jump `k < L` with `E₂ k ∧ E₁ (k + 1)`. -/
lemma discrete_bolzano {L : ℕ} (E₁ E₂ : ℕ → Prop)
    (h0 : ¬ E₁ 0) (hL : ¬ E₂ L) :
    (∃ k ≤ L, ¬ E₁ k ∧ ¬ E₂ k) ∨ (∃ k < L, E₂ k ∧ E₁ (k + 1)) := by
  induction L with
  | zero => exact Or.inl ⟨0, le_refl 0, h0, hL⟩
  | succ L ih =>
    by_cases hE2 : E₂ L
    · by_cases hE1 : E₁ (L + 1)
      · exact Or.inr ⟨L, Nat.lt_succ_self L, hE2, hE1⟩
      · exact Or.inl ⟨L + 1, le_refl _, hE1, hL⟩
    · rcases ih hE2 with ⟨k, hk, h1, h2⟩ | ⟨k, hk, h2, h1⟩
      · exact Or.inl ⟨k, Nat.le_succ_of_le hk, h1, h2⟩
      · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, h2, h1⟩

/-- Given counts `L : Fin t → ℕ` summing to `a + x`, split each `L i = A i + X i` with
`∑ A = a` and `∑ X = x`. -/
lemma exists_split_counts {t : ℕ} (L : Fin t → ℕ) (a x : ℕ)
    (hsum : ∑ i : Fin t, L i = a + x) :
    ∃ A X : Fin t → ℕ, (∀ i, A i + X i = L i) ∧ (∑ i, A i = a) ∧ (∑ i, X i = x) := by
  induction t generalizing a x with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, by simp; omega, by simp; omega⟩
  | succ t ih =>
    rw [Fin.sum_univ_castSucc] at hsum
    let l := L (Fin.last t)
    let aL := min l a
    let xL := l - aL
    have haL_le_l : aL ≤ l := min_le_left l a
    have haL_le_a : aL ≤ a := min_le_right l a
    have haxL : aL + xL = l := by omega
    have hxL_le_x : xL ≤ x := by
      have : aL = l ∨ aL = a := min_choice l a
      omega
    have hsum' : ∑ i : Fin t, L i.castSucc = (a - aL) + (x - xL) := by omega
    obtain ⟨A', X', hAX', hA', hX'⟩ := ih (fun i => L i.castSucc) (a - aL) (x - xL) hsum'
    refine ⟨Fin.snoc A' aL, Fin.snoc X' xL, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using haxL
      · simpa using hAX' j
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hA']
      omega
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hX']
      omega

/-- Partition `Fin m` along a decidable predicate `P` into `Fin (m₁ + m₂)`. -/
lemma equiv_partition_fin {m : ℕ} (P : Fin m → Prop) [DecidablePred P] :
    ∃ (m₁ m₂ : ℕ) (e : Fin m ≃ Fin (m₁ + m₂)),
      (∀ x : Fin m₁, P (e.symm (Fin.castAdd m₂ x))) ∧
      (∀ y : Fin m₂, ¬ P (e.symm (Fin.natAdd m₁ y))) := by
  let m₁ := Fintype.card {g : Fin m // P g}
  let m₂ := Fintype.card {g : Fin m // ¬ P g}
  let e₁ : {g : Fin m // P g} ≃ Fin m₁ := Fintype.equivFin _
  let e₂ : {g : Fin m // ¬ P g} ≃ Fin m₂ := Fintype.equivFin _
  let e : Fin m ≃ Fin (m₁ + m₂) :=
    (Equiv.sumCompl P).symm.trans ((e₁.sumCongr e₂).trans finSumFinEquiv)
  refine ⟨m₁, m₂, e, ?_, ?_⟩
  · intro x
    have hL : (finSumFinEquiv : Fin m₁ ⊕ Fin m₂ ≃ Fin (m₁ + m₂)).symm (Fin.castAdd m₂ x) = Sum.inl x :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    have h : e.symm (Fin.castAdd m₂ x) = (e₁.symm x).1 := by
      simp [e, hL]
    rw [h]
    exact (e₁.symm x).2
  · intro y
    have hR : (finSumFinEquiv : Fin m₁ ⊕ Fin m₂ ≃ Fin (m₁ + m₂)).symm (Fin.natAdd m₁ y) = Sum.inr y :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    have h : e.symm (Fin.natAdd m₁ y) = (e₂.symm y).1 := by
      simp [e, hR]
    rw [h]
    exact (e₂.symm y).2

/-! ### Abstract Two-Type Specification and Its Concrete Realization -/

/-- A valid EFX bundle-count specification for `t₁` Group-1 agents, `t₂` Group-2 agents, and
`(nA, nB, nC)` chores of types `A, B, C` (normalized costs `{1, r₁}` and `{1, r₂}`). -/
structure TwoTypeSpec (t₁ t₂ nA nB nC : ℕ) (r₁ r₂ : ℝ) where
  A1 : Fin t₁ → ℕ
  B1 : Fin t₁ → ℕ
  C1 : Fin t₁ → ℕ
  A2 : Fin t₂ → ℕ
  B2 : Fin t₂ → ℕ
  C2 : Fin t₂ → ℕ
  sumA : ∑ i, A1 i + ∑ j, A2 j = nA
  sumB : ∑ i, B1 i + ∑ j, B2 j = nB
  sumC : ∑ i, C1 i + ∑ j, C2 j = nC
  efx11 : ∀ i j : Fin t₁, ownTau r₁ (A1 i + C1 i) (B1 i) ≤ ownCost r₁ (A1 j + C1 j) (B1 j)
  efx22 : ∀ i j : Fin t₂, ownTau r₂ (A2 i + B2 i) (C2 i) ≤ ownCost r₂ (A2 j + B2 j) (C2 j)
  efx12 : ∀ (i : Fin t₁) (j : Fin t₂), ownTau r₁ (A1 i + C1 i) (B1 i) ≤ ownCost r₁ (A2 j + C2 j) (B2 j)
  efx21 : ∀ (i : Fin t₂) (j : Fin t₁), ownTau r₂ (A2 i + B2 i) (C2 i) ≤ ownCost r₂ (A1 j + B1 j) (C1 j)

/-- Exact symmetry swapping Group 1 and Group 2 (`B ↔ C`, `r₁ ↔ r₂`). -/
def TwoTypeSpec.swap {t₁ t₂ nA nB nC : ℕ} {r₁ r₂ : ℝ}
    (S : TwoTypeSpec t₂ t₁ nA nC nB r₂ r₁) : TwoTypeSpec t₁ t₂ nA nB nC r₁ r₂ where
  A1 := S.A2
  B1 := S.C2
  C1 := S.B2
  A2 := S.A1
  B2 := S.C1
  C2 := S.B1
  sumA := by rw [add_comm]; exact S.sumA
  sumB := by rw [add_comm]; exact S.sumC
  sumC := by rw [add_comm]; exact S.sumB
  efx11 := S.efx22
  efx22 := S.efx11
  efx12 := S.efx21
  efx21 := S.efx12

/-- Helper: realize a `TwoTypeSpec` as a concrete EFX allocation on `Fin (t₁ + t₂)` agents and
`Fin ((nA + nB) + nC)` chores where items are ordered `A`, then `B`, then `C`. -/
lemma realize_twoTypeSpec {t₁ t₂ nA nB nC : ℕ} {r₁ r₂ : ℝ}
    (hr₁ : 1 < r₁) (hr₂ : 1 < r₂)
    (cost : Fin (t₁ + t₂) → Fin ((nA + nB) + nC) → ℝ)
    (hA1 : ∀ (i : Fin t₁) (g : Fin nA), cost (Fin.castAdd t₂ i) (Fin.castAdd nC (Fin.castAdd nB g)) = r₁)
    (hA2 : ∀ (i : Fin t₂) (g : Fin nA), cost (Fin.natAdd t₁ i) (Fin.castAdd nC (Fin.castAdd nB g)) = r₂)
    (hB1 : ∀ (i : Fin t₁) (g : Fin nB), cost (Fin.castAdd t₂ i) (Fin.castAdd nC (Fin.natAdd nA g)) = 1)
    (hB2 : ∀ (i : Fin t₂) (g : Fin nB), cost (Fin.natAdd t₁ i) (Fin.castAdd nC (Fin.natAdd nA g)) = r₂)
    (hC1 : ∀ (i : Fin t₁) (g : Fin nC), cost (Fin.castAdd t₂ i) (Fin.natAdd (nA + nB) g) = r₁)
    (hC2 : ∀ (i : Fin t₂) (g : Fin nC), cost (Fin.natAdd t₁ i) (Fin.natAdd (nA + nB) g) = 1)
    (S : TwoTypeSpec t₁ t₂ nA nB nC r₁ r₂) :
    ∃ alloc : Fin ((nA + nB) + nC) → Fin (t₁ + t₂), IsEFX cost alloc := by
  let cntA : Fin (t₁ + t₂) → ℕ := Fin.addCases S.A1 S.A2
  let cntB : Fin (t₁ + t₂) → ℕ := Fin.addCases S.B1 S.B2
  let cntC : Fin (t₁ + t₂) → ℕ := Fin.addCases S.C1 S.C2
  have hsumA : ∑ k, cntA k = nA := by simp [cntA, Fin.sum_univ_add, S.sumA]
  have hsumB : ∑ k, cntB k = nB := by simp [cntB, Fin.sum_univ_add, S.sumB]
  have hsumC : ∑ k, cntC k = nC := by simp [cntC, Fin.sum_univ_add, S.sumC]
  obtain ⟨fA, hfA⟩ := exists_assignment_with_counts cntA hsumA
  obtain ⟨fB, hfB⟩ := exists_assignment_with_counts cntB hsumB
  obtain ⟨fC, hfC⟩ := exists_assignment_with_counts cntC hsumC
  let alloc : Fin ((nA + nB) + nC) → Fin (t₁ + t₂) := Fin.addCases (Fin.addCases fA fB) fC
  -- Express bundleCost of any bundle k evaluated by Group-1 agent i or Group-2 agent i
  have hcost_split : ∀ (k : Fin (t₁ + t₂)) (i : Fin (t₁ + t₂)),
      bundleCost cost (bundle alloc k) i =
        (∑ g ∈ Finset.univ.filter (fun x : Fin nA => fA x = k),
            cost i (Fin.castAdd nC (Fin.castAdd nB g))) +
        (∑ g ∈ Finset.univ.filter (fun x : Fin nB => fB x = k),
            cost i (Fin.castAdd nC (Fin.natAdd nA g))) +
        (∑ g ∈ Finset.univ.filter (fun x : Fin nC => fC x = k),
            cost i (Fin.natAdd (nA + nB) g)) := by
    intro k i
    unfold bundleCost bundle
    rw [Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_add]
    simp only [alloc, Fin.addCases_left, Fin.addCases_right, ← Finset.sum_filter]
  have hcost1 : ∀ (i : Fin t₁) (k : Fin (t₁ + t₂)),
      bundleCost cost (bundle alloc k) (Fin.castAdd t₂ i) =
        ownCost r₁ (cntA k + cntC k) (cntB k) := by
    intro i k
    rw [hcost_split k (Fin.castAdd t₂ i)]
    simp only [hA1, hB1, hC1, Finset.sum_const, nsmul_eq_mul, hfA k, hfB k, hfC k, ownCost]
    push_cast; ring
  have hcost2 : ∀ (i : Fin t₂) (k : Fin (t₁ + t₂)),
      bundleCost cost (bundle alloc k) (Fin.natAdd t₁ i) =
        ownCost r₂ (cntA k + cntB k) (cntC k) := by
    intro i k
    rw [hcost_split k (Fin.natAdd t₁ i)]
    simp only [hA2, hB2, hC2, Finset.sum_const, nsmul_eq_mul, hfA k, hfB k, hfC k, ownCost]
    push_cast; ring
  refine ⟨alloc, fun i j g hg => ?_⟩
  rw [bundleCost_sdiff_singleton cost hg]
  revert hg
  refine Fin.addCases (fun i₁ hg => ?_) (fun i₂ hg => ?_) i
  · -- Agent i is in Group 1: Fin.castAdd t₂ i₁
    rw [hcost1 i₁ (Fin.castAdd t₂ i₁)]
    have hcntA : cntA (Fin.castAdd t₂ i₁) = S.A1 i₁ := by simp [cntA]
    have hcntB : cntB (Fin.castAdd t₂ i₁) = S.B1 i₁ := by simp [cntB]
    have hcntC : cntC (Fin.castAdd t₂ i₁) = S.C1 i₁ := by simp [cntC]
    rw [hcntA, hcntB, hcntC]
    -- Show cost (castAdd t₂ i₁) g ≥ if 0 < S.B1 i₁ then 1 else r₁, AND S.A1 i₁ + S.C1 i₁ + S.B1 i₁ ≠ 0!
    have htau_ge : ownCost r₁ (S.A1 i₁ + S.C1 i₁) (S.B1 i₁) - cost (Fin.castAdd t₂ i₁) g ≤
        ownTau r₁ (S.A1 i₁ + S.C1 i₁) (S.B1 i₁) := by
      have hg_eq : alloc g = Fin.castAdd t₂ i₁ := mem_bundle.mp hg
      revert hg_eq
      refine Fin.addCases (fun gAB => ?_) (fun gC hg_eq => ?_) g
      · refine Fin.addCases (fun gA hg_eq => ?_) (fun gB hg_eq => ?_) gAB
        · -- g is in A: cost = r₁, and S.A1 i₁ ≥ 1
          have hgA : fA gA = Fin.castAdd t₂ i₁ := by simpa [alloc] using hg_eq
          have hposA : 0 < S.A1 i₁ := by
            rw [← hcntA, ← hfA]; exact Finset.card_pos.mpr ⟨gA, by simp [hgA]⟩
          rw [hA1 i₁ gA]; unfold ownTau
          rw [ite_eq_right (by omega)]
          split_ifs <;> linarith
        · -- g is in B: cost = 1, and S.B1 i₁ ≥ 1
          have hgB : fB gB = Fin.castAdd t₂ i₁ := by simpa [alloc] using hg_eq
          have hposB : 0 < S.B1 i₁ := by
            rw [← hcntB, ← hfB]; exact Finset.card_pos.mpr ⟨gB, by simp [hgB]⟩
          rw [hB1 i₁ gB]; unfold ownTau
          rw [ite_eq_right (by omega), ite_eq_left (hposB)]
      · -- g is in C: cost = r₁, and S.C1 i₁ ≥ 1
        have hgC : fC gC = Fin.castAdd t₂ i₁ := by simpa [alloc] using hg_eq
        have hposC : 0 < S.C1 i₁ := by
          rw [← hcntC, ← hfC]; exact Finset.card_pos.mpr ⟨gC, by simp [hgC]⟩
        rw [hC1 i₁ gC]; unfold ownTau
        rw [ite_eq_right (by omega)]
        split_ifs <;> linarith
    refine le_trans htau_ge ?_
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · rw [hcost1 i₁ (Fin.castAdd t₂ j₁)]; simp only [cntA, cntB, cntC, Fin.addCases_left]
      exact S.efx11 i₁ j₁
    · rw [hcost1 i₁ (Fin.natAdd t₁ j₂)]; simp only [cntA, cntB, cntC, Fin.addCases_right]
      exact S.efx12 i₁ j₂
  · -- Agent i is in Group 2: Fin.natAdd t₁ i₂
    rw [hcost2 i₂ (Fin.natAdd t₁ i₂)]
    have hcntA : cntA (Fin.natAdd t₁ i₂) = S.A2 i₂ := by simp [cntA]
    have hcntB : cntB (Fin.natAdd t₁ i₂) = S.B2 i₂ := by simp [cntB]
    have hcntC : cntC (Fin.natAdd t₁ i₂) = S.C2 i₂ := by simp [cntC]
    rw [hcntA, hcntB, hcntC]
    have htau_ge : ownCost r₂ (S.A2 i₂ + S.B2 i₂) (S.C2 i₂) - cost (Fin.natAdd t₁ i₂) g ≤
        ownTau r₂ (S.A2 i₂ + S.B2 i₂) (S.C2 i₂) := by
      have hg_eq : alloc g = Fin.natAdd t₁ i₂ := mem_bundle.mp hg
      revert hg_eq
      refine Fin.addCases (fun gAB => ?_) (fun gC hg_eq => ?_) g
      · refine Fin.addCases (fun gA hg_eq => ?_) (fun gB hg_eq => ?_) gAB
        · have hgA : fA gA = Fin.natAdd t₁ i₂ := by simpa [alloc] using hg_eq
          have hposA : 0 < S.A2 i₂ := by
            rw [← hcntA, ← hfA]; exact Finset.card_pos.mpr ⟨gA, by simp [hgA]⟩
          rw [hA2 i₂ gA]; unfold ownTau
          rw [ite_eq_right (by omega)]
          split_ifs <;> linarith
        · have hgB : fB gB = Fin.natAdd t₁ i₂ := by simpa [alloc] using hg_eq
          have hposB : 0 < S.B2 i₂ := by
            rw [← hcntB, ← hfB]; exact Finset.card_pos.mpr ⟨gB, by simp [hgB]⟩
          rw [hB2 i₂ gB]; unfold ownTau
          rw [ite_eq_right (by omega)]
          split_ifs <;> linarith
      · have hgC : fC gC = Fin.natAdd t₁ i₂ := by simpa [alloc] using hg_eq
        have hposC : 0 < S.C2 i₂ := by
          rw [← hcntC, ← hfC]; exact Finset.card_pos.mpr ⟨gC, by simp [hgC]⟩
        rw [hC2 i₂ gC]; unfold ownTau
        rw [ite_eq_right (by omega), ite_eq_left (hposC)]
    refine le_trans htau_ge ?_
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · rw [hcost2 i₂ (Fin.castAdd t₂ j₁)]; simp only [cntA, cntB, cntC, Fin.addCases_left]
      exact S.efx21 i₂ j₁
    · rw [hcost2 i₂ (Fin.natAdd t₁ j₂)]; simp only [cntA, cntB, cntC, Fin.addCases_right]
      exact S.efx22 i₂ j₂

/-! ### Phase 1 Construction (handles both Phase 1 and, via `swap`, Phase 3) -/

/-- If `¬ E₂(0, nB, 0 | nA, 0, nC)`, then Phase 1 (`B` moving from Pile 2 to Pile 1) always
contains an EFX specification. -/
private lemma exists_twoTypeSpec_phase1 {t₁ t₂ nA nB nC K₁ K₂ : ℕ} {r₁ r₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hr₁ : 1 < r₁) (hr₂ : 1 < r₂)
    (hK₁2 : 2 ≤ K₁) (hK₁_lo : (K₁ : ℝ) - 1 < r₁) (hK₁_hi : r₁ ≤ (K₁ : ℝ))
    (hK₂_lo : (K₂ : ℝ) - 1 < r₂) (hK₂_hi : r₂ ≤ (K₂ : ℝ))
    (h_end : ¬ r₂ * (pileMinSize t₁ 0 nB K₁ : ℝ) < pileTau t₂ nA nC K₂ r₂) :
    Nonempty (TwoTypeSpec t₁ t₂ nA nB nC r₁ r₂) := by
  let E₁ : ℕ → Prop := fun b₁ =>
    ∃ j : Fin t₂,
      (pileLarge t₂ (nA + (nB - b₁)) j : ℝ) +
      (pileSmall t₂ (nA + (nB - b₁)) nC K₂ j : ℝ) * r₁ <
      pileTau t₁ 0 b₁ K₁ r₁
  let E₂ : ℕ → Prop := fun b₁ =>
    r₂ * (pileMinSize t₁ 0 b₁ K₁ : ℝ) < pileTau t₂ (nA + (nB - b₁)) nC K₂ r₂
  have hE1_0 : ¬ E₁ 0 := by
    rintro ⟨j, hj⟩
    have htau0 : pileTau t₁ 0 0 K₁ r₁ = 0 := by
      unfold pileTau pileTauAux; simp
    rw [htau0] at hj
    have hnn : (0 : ℝ) ≤ (pileLarge t₂ (nA + (nB - 0)) j : ℝ) +
        (pileSmall t₂ (nA + (nB - 0)) nC K₂ j : ℝ) * r₁ := by positivity
    linarith
  have hE2_end : ¬ E₂ nB := by
    simpa [E₂] using h_end
  rcases discrete_bolzano E₁ E₂ hE1_0 hE2_end with ⟨b₁, hb₁, h1, h2⟩ | ⟨b₁, hb₁, h2, h1⟩
  · -- Found b₁ ≤ nB with ¬ E₁ b₁ ∧ ¬ E₂ b₁: construct TwoTypeSpec!
    dsimp only [E₁, E₂] at h1 h2
    push Not at h1 h2
    have hsumL2 : ∑ j : Fin t₂, pileLarge t₂ (nA + (nB - b₁)) j = nA + (nB - b₁) :=
      sum_pileLarge ht₂
    obtain ⟨A2, B2, hAB2, hsumA2, hsumB2⟩ :=
      exists_split_counts (pileLarge t₂ (nA + (nB - b₁))) nA (nB - b₁) hsumL2
    have hL1_zero : ∀ i : Fin t₁, pileLarge t₁ 0 i = 0 := by
      intro i; unfold pileLarge pileLargeAux; simp
    refine ⟨{
      A1 := fun _ => 0
      B1 := pileSmall t₁ 0 b₁ K₁
      C1 := fun _ => 0
      A2 := A2
      B2 := B2
      C2 := pileSmall t₂ (nA + (nB - b₁)) nC K₂
      sumA := by simp [hsumA2]
      sumB := by rw [sum_pileSmall ht₁, hsumB2]; omega
      sumC := by simp [sum_pileSmall ht₂]
      efx11 := fun i j => by
        simpa [hL1_zero] using identicalPile_internal_efx ht₁ hr₁ hK₁_lo hK₁_hi (p := 0) (s := b₁) i j
      efx22 := fun i j => by
        rw [hAB2 i, hAB2 j]
        exact identicalPile_internal_efx ht₂ hr₂ hK₂_lo hK₂_hi i j
      efx12 := fun i j => by
        have htau_i : ownTau r₁ (0 + 0) (pileSmall t₁ 0 b₁ K₁ i) ≤ pileTau t₁ 0 b₁ K₁ r₁ := by
          simpa [hL1_zero] using ownTau_le_pileTau ht₁ hr₁ hK₁_lo hK₁_hi (p := 0) (s := b₁) i
        have hlow : pileTau t₁ 0 b₁ K₁ r₁ ≤
            (pileLarge t₂ (nA + (nB - b₁)) j : ℝ) +
            (pileSmall t₂ (nA + (nB - b₁)) nC K₂ j : ℝ) * r₁ := h1 j
        have hcost_j : (pileLarge t₂ (nA + (nB - b₁)) j : ℝ) +
            (pileSmall t₂ (nA + (nB - b₁)) nC K₂ j : ℝ) * r₁ ≤
            ownCost r₁ (A2 j + pileSmall t₂ (nA + (nB - b₁)) nC K₂ j) (B2 j) := by
          rw [← hAB2 j]; unfold ownCost; push_cast
          have hA2_nn : (0 : ℝ) ≤ (A2 j : ℝ) := Nat.cast_nonneg _
          nlinarith only [hA2_nn, hr₁]
        exact le_trans (le_trans htau_i hlow) hcost_j
      efx21 := fun i j => by
        rw [hAB2 i]
        have htau_i : ownTau r₂ (pileLarge t₂ (nA + (nB - b₁)) i)
            (pileSmall t₂ (nA + (nB - b₁)) nC K₂ i) ≤
            pileTau t₂ (nA + (nB - b₁)) nC K₂ r₂ :=
          ownTau_le_pileTau ht₂ hr₂ hK₂_lo hK₂_hi i
        have hmin_j : pileMinSize t₁ 0 b₁ K₁ ≤ 0 + pileSmall t₁ 0 b₁ K₁ j := by
          simpa [hL1_zero] using pileMinSize_le_size ht₁ hK₁2 (p := 0) (s := b₁) j
        have hminR : (pileMinSize t₁ 0 b₁ K₁ : ℝ) ≤ (pileSmall t₁ 0 b₁ K₁ j : ℝ) := by
          exact_mod_cast (by omega : pileMinSize t₁ 0 b₁ K₁ ≤ pileSmall t₁ 0 b₁ K₁ j)
        unfold ownCost
        simp only [zero_add, Nat.cast_zero, add_zero]
        nlinarith only [htau_i, h2, hminR, hr₂]
    }⟩
  · -- Impossible jump E₂ b₁ ∧ E₁ (b₁ + 1): contradiction with phase1_bundle_lower_bound!
    exfalso
    rcases h1 with ⟨j, hj⟩
    set q := b₁ / t₁
    have hmin1 : pileMinSize t₁ 0 b₁ K₁ = q := by
      unfold pileMinSize; simp only [Nat.zero_div, Nat.zero_mod]
      rw [pileMinSizeAux_u0 ht₁, zero_add]
    have htau1 : pileTau t₁ 0 (b₁ + 1) K₁ r₁ = (q : ℝ) := by
      unfold pileTau; simp only [Nat.zero_div, Nat.zero_mod]
      rw [pileTauAux_u0_pos ht₁ (Nat.succ_pos b₁) (by omega), ceilDiv_succ_sub_one ht₁]
      simp [q]
    set p := nA + (nB - (b₁ + 1))
    have hp_succ : nA + (nB - b₁) = p + 1 := by omega
    dsimp only [E₂] at h2
    rw [hmin1, hp_succ] at h2
    rw [htau1] at hj
    have hgt : (q : ℝ) * r₂ < pileTau t₂ (p + 1) nC K₂ r₂ := by linarith
    have hlb := phase1_bundle_lower_bound ht₂ hr₁ hr₂ hK₂_lo hK₂_hi hgt j
    linarith

/-! ### Phase 2 Single-Item Bridge Construction -/

/-- At any Phase-2 envy jump `E₂(a₁) ∧ E₁(a₁ + 1)`, Lemmas A, B, and C guarantee that at least
one of the two single-item bridge states `B_moveB` or `B_moveC` is EFX. -/
private lemma exists_twoTypeSpec_phase2_jump {t₁ t₂ nA nB nC K₁ K₂ a₁ : ℕ} {r₁ r₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (hr₁ : 1 < r₁) (hr₂ : 1 < r₂)
    (hK₁2 : 2 ≤ K₁) (hK₁_lo : (K₁ : ℝ) - 1 < r₁) (hK₁_hi : r₁ ≤ (K₁ : ℝ))
    (hK₂2 : 2 ≤ K₂) (hK₂_lo : (K₂ : ℝ) - 1 < r₂) (hK₂_hi : r₂ ≤ (K₂ : ℝ))
    (ha₁ : a₁ < nA)
    (h2 : r₂ * (pileMinSize t₁ a₁ nB K₁ : ℝ) < pileTau t₂ (nA - a₁) nC K₂ r₂)
    (h1 : r₁ * (pileMinSize t₂ (nA - (a₁ + 1)) nC K₂ : ℝ) < pileTau t₁ (a₁ + 1) nB K₁ r₁) :
    Nonempty (TwoTypeSpec t₁ t₂ nA nB nC r₁ r₂) := by
  set a₂ := nA - a₁
  have ha₂_pos : 1 ≤ a₂ := by omega
  have ha₂_sub : nA - (a₁ + 1) = a₂ - 1 := by omega
  have ha₂_succ : a₂ = (a₂ - 1) + 1 := by omega
  -- Pin M₁(a₁) = M₂(a₂ - 1) = Mstar via Lemma A!
  have hstep1 := pileTau_step_lt (t := t₁) (p := a₁) (s := nB) (K := K₁) ht₁ hr₁ hK₁_lo hK₁_hi
  have hstep2 : pileTau t₂ a₂ nC K₂ r₂ < r₂ * ((pileMinSize t₂ (a₂ - 1) nC K₂ : ℝ) + 1) := by
    rw [ha₂_succ]; exact pileTau_step_lt ht₂ hr₂ hK₂_lo hK₂_hi
  rw [ha₂_sub] at h1
  have hle12 : pileMinSize t₁ a₁ nB K₁ ≤ pileMinSize t₂ (a₂ - 1) nC K₂ := by
    have : (pileMinSize t₁ a₁ nB K₁ : ℝ) < (pileMinSize t₂ (a₂ - 1) nC K₂ : ℝ) + 1 := by
      nlinarith only [h2, hstep2, hr₂]
    have : pileMinSize t₁ a₁ nB K₁ < pileMinSize t₂ (a₂ - 1) nC K₂ + 1 := by exact_mod_cast this
    omega
  have hle21 : pileMinSize t₂ (a₂ - 1) nC K₂ ≤ pileMinSize t₁ a₁ nB K₁ := by
    have : (pileMinSize t₂ (a₂ - 1) nC K₂ : ℝ) < (pileMinSize t₁ a₁ nB K₁ : ℝ) + 1 := by
      nlinarith only [h1, hstep1, hr₁]
    have : pileMinSize t₂ (a₂ - 1) nC K₂ < pileMinSize t₁ a₁ nB K₁ + 1 := by exact_mod_cast this
    omega
  set Mstar := pileMinSize t₁ a₁ nB K₁
  have hM2_eq : pileMinSize t₂ (a₂ - 1) nC K₂ = Mstar := by omega
  rw [hM2_eq] at h1 hstep2
  -- Rule out nB = 0, t₁ = 1, a₁ % t₁ = 0 and nC = 0 via Tight Lemma A!
  have hnB_pos : 1 ≤ nB := by
    by_contra h0
    have hb0 : nB = 0 := by omega
    have ht := pileTau_step_le_tight (t := t₁) (p := a₁) (s := nB) (K := K₁) ht₁ hr₁ hK₁_lo hK₁_hi (Or.inl hb0)
    linarith only [h1, ht]
  have hnC_pos : 1 ≤ nC := by
    by_contra h0
    have hc0 : nC = 0 := by omega
    have ht : pileTau t₂ a₂ nC K₂ r₂ ≤ r₂ * (Mstar : ℝ) := by
      rw [ha₂_succ, ← hM2_eq]
      exact pileTau_step_le_tight ht₂ hr₂ hK₂_lo hK₂_hi (Or.inl hc0)
    linarith only [h2, ht]
  have hu1_ne0 : a₁ % t₁ ≠ 0 := by
    intro h0
    have ht := pileTau_step_le_tight (t := t₁) (p := a₁) (s := nB) (K := K₁) ht₁ hr₁ hK₁_lo hK₁_hi (Or.inr (Or.inr h0))
    linarith only [h1, ht]
  -- Rule out Mstar = 0!
  have hMstar_pos : 1 ≤ Mstar := by
    by_contra hM0
    have hMzero : pileMinSize t₁ a₁ nB K₁ = 0 := by omega
    have hu1_lt : a₁ % t₁ < t₁ := Nat.mod_lt a₁ ht₁
    unfold pileMinSize pileMinSizeAux at hMzero
    have hle_cap : nB ≤ (t₁ - a₁ % t₁) * K₁ := by
      by_contra hgt; rw [ite_eq_right hgt, ite_eq_right hu1_ne0] at hMzero
      split_ifs at hMzero
    rw [ite_eq_left hle_cap, ite_eq_right hu1_ne0] at hMzero
    have hnB_lt : nB < t₁ - a₁ % t₁ := by
      by_contra hge; rw [ite_eq_right hge] at hMzero; simp at hMzero
    rw [ite_eq_left hnB_lt] at hMzero
    have hell0 : a₁ / t₁ = 0 := hMzero
    have hdm1 := div_mod_succ_of_lt ht₁ (by omega : a₁ % t₁ + 1 < t₁)
    have htu1_pos : 0 < t₁ - (a₁ % t₁ + 1) := by omega
    have hnB_le_u1 : nB ≤ t₁ - (a₁ % t₁ + 1) := by omega
    have hnB_le1 : nB ≤ (t₁ - (a₁ % t₁ + 1)) * K₁ :=
      le_trans hnB_le_u1 (Nat.le_mul_of_pos_right _ (by omega))
    have hc1 : ceilDiv nB (t₁ - (a₁ % t₁ + 1)) = 1 := by
      have ha := ceilDiv_pos htu1_pos (by omega : 0 < nB)
      have hb := ceilDiv_le_of_le_mul htu1_pos (by omega : nB ≤ (t₁ - (a₁ % t₁ + 1)) * 1)
      omega
    have htau_zero : pileTau t₁ (a₁ + 1) nB K₁ r₁ = 0 := by
      unfold pileTau; rw [hdm1.1, hdm1.2, hell0]; unfold pileTauAux
      rw [ite_eq_left hnB_le1, ite_eq_right (by omega : nB ≠ 0), hc1]
      simp
    rw [htau_zero, show Mstar = 0 by omega] at h1
    simp at h1
  -- Fundamental bounds give M₁(a₁+1, nB) ≥ Mstar + 1 and M₂(a₂, nC) ≥ Mstar + 1
  have hM1_ge : Mstar + 1 ≤ pileMinSize t₁ (a₁ + 1) nB K₁ := by
    have hf := pileTau_le_r_mul_minSize (t := t₁) (p := a₁ + 1) (s := nB) (K := K₁) ht₁ hr₁ hK₁_lo hK₁_hi
    have : (Mstar : ℝ) < (pileMinSize t₁ (a₁ + 1) nB K₁ : ℝ) := by nlinarith only [h1, hf, hr₁]
    have : Mstar < pileMinSize t₁ (a₁ + 1) nB K₁ := by exact_mod_cast this
    omega
  have hM2_ge : Mstar + 1 ≤ pileMinSize t₂ a₂ nC K₂ := by
    have hf := pileTau_le_r_mul_minSize (t := t₂) (p := a₂) (s := nC) (K := K₂) ht₂ hr₂ hK₂_lo hK₂_hi
    have : (Mstar : ℝ) < (pileMinSize t₂ a₂ nC K₂ : ℝ) := by nlinarith only [h2, hf, hr₂]
    have : Mstar < pileMinSize t₂ a₂ nC K₂ := by exact_mod_cast this
    omega
  -- Lemma B (Zero-Drop Lemma) on BOTH piles!
  have hB1 : Mstar + 1 ≤ pileMinSize t₁ (a₁ + 1) (nB - 1) K₁ :=
    pileMinSize_sub_one_ge ht₁ hr₁ hK₁_lo hK₁_hi hnB_pos h1
  have hB2 : Mstar + 1 ≤ pileMinSize t₂ a₂ (nC - 1) K₂ :=
    pileMinSize_sub_one_ge ht₂ hr₂ hK₂_lo hK₂_hi hnC_pos h2
  -- Monotonicity of pileTau in s
  have hmono1 : pileTau t₁ (a₁ + 1) (nB - 1) K₁ r₁ ≤ pileTau t₁ (a₁ + 1) nB K₁ r₁ :=
    pileTau_mono_s ht₁ hr₁ hK₁_lo hK₁_hi (by omega)
  have hmono2 : pileTau t₂ a₂ (nC - 1) K₂ r₂ ≤ pileTau t₂ a₂ nC K₂ r₂ :=
    pileTau_mono_s ht₂ hr₂ hK₂_lo hK₂_hi (by omega)
  -- Split on whether B_moveB satisfies ¬ E₁ on the single cross bundle maxLargeIdx₂!
  let idx2 : Fin t₂ := maxLargeIdx t₂ a₂ nC K₂ ht₂
  have hidx2_pos : 0 < pileLarge t₂ a₂ idx2 := maxLargeIdx_large_pos ht₂ (by omega)
  by_cases hbridgeB :
      pileTau t₁ (a₁ + 1) (nB - 1) K₁ r₁ ≤
        r₁ * ((maxLargeSize t₂ a₂ nC K₂ ht₂ - 1 : ℕ) : ℝ) + 1
  · -- Construct B_moveB = (a₁ + 1, nB - 1, 0 | a₂ - 1, 1, nC)!
    let B2_fn : Fin t₂ → ℕ := fun j => if j = idx2 then 1 else 0
    let A2_fn : Fin t₂ → ℕ := fun j => if j = idx2 then pileLarge t₂ a₂ j - 1 else pileLarge t₂ a₂ j
    have hAB2 : ∀ j : Fin t₂, A2_fn j + B2_fn j = pileLarge t₂ a₂ j := by
      intro j; simp only [A2_fn, B2_fn]
      split_ifs with hj
      · subst hj; omega
      · omega
    have hsumB2 : ∑ j : Fin t₂, B2_fn j = 1 := by simp [B2_fn]
    have hsumA2 : ∑ j : Fin t₂, A2_fn j = a₂ - 1 := by
      have htot : ∑ j : Fin t₂, (A2_fn j + B2_fn j) = a₂ := by
        simp_rw [hAB2]; exact sum_pileLarge ht₂
      rw [Finset.sum_add_distrib, hsumB2] at htot; omega
    refine ⟨{
      A1 := pileLarge t₁ (a₁ + 1)
      B1 := pileSmall t₁ (a₁ + 1) (nB - 1) K₁
      C1 := fun _ => 0
      A2 := A2_fn
      B2 := B2_fn
      C2 := pileSmall t₂ a₂ nC K₂
      sumA := by rw [sum_pileLarge ht₁, hsumA2]; omega
      sumB := by rw [sum_pileSmall ht₁, hsumB2]; omega
      sumC := by simp [sum_pileSmall ht₂]
      efx11 := fun i j => by
        simpa using identicalPile_internal_efx ht₁ hr₁ hK₁_lo hK₁_hi i j
      efx22 := fun i j => by
        rw [hAB2 i, hAB2 j]
        exact identicalPile_internal_efx ht₂ hr₂ hK₂_lo hK₂_hi i j
      efx12 := fun i j => by
        have htau := ownTau_le_pileTau ht₁ hr₁ hK₁_lo hK₁_hi (p := a₁ + 1) (s := nB - 1) i
        simp only [add_zero]
        by_cases hj : j = idx2
        · subst hj
          have hcost_idx : ownCost r₁ (A2_fn idx2 + pileSmall t₂ a₂ nC K₂ idx2) (B2_fn idx2) =
              r₁ * ((maxLargeSize t₂ a₂ nC K₂ ht₂ - 1 : ℕ) : ℝ) + 1 := by
            unfold ownCost maxLargeSize
            simp only [A2_fn, B2_fn, ↓reduceIte, Nat.cast_one]
            have heq : pileLarge t₂ a₂ idx2 - 1 + pileSmall t₂ a₂ nC K₂ idx2 =
                pileLarge t₂ a₂ idx2 + pileSmall t₂ a₂ nC K₂ idx2 - 1 := by omega
            rw [heq]; ring
          rw [hcost_idx]; exact le_trans htau hbridgeB
        · have hA2j : A2_fn j = pileLarge t₂ a₂ j := ite_eq_right hj
          have hB2j : B2_fn j = 0 := ite_eq_right hj
          rw [hA2j, hB2j]; unfold ownCost
          have hmin := pileMinSize_le_size ht₂ hK₂2 (p := a₂) (s := nC) j
          have hminR : (Mstar : ℝ) + 1 ≤
              (pileLarge t₂ a₂ j : ℝ) + (pileSmall t₂ a₂ nC K₂ j : ℝ) := by
            have : Mstar + 1 ≤ pileLarge t₂ a₂ j + pileSmall t₂ a₂ nC K₂ j := by omega
            exact_mod_cast this
          simp only [Nat.cast_zero, add_zero]; push_cast
          nlinarith only [htau, hmono1, hstep1, hminR, hr₁]
      efx21 := fun i j => by
        rw [hAB2 i]
        have htau := ownTau_le_pileTau ht₂ hr₂ hK₂_lo hK₂_hi (p := a₂) (s := nC) i
        have hmin := pileMinSize_le_size ht₁ hK₁2 (p := a₁ + 1) (s := nB - 1) j
        have hminR : (Mstar : ℝ) + 1 ≤
            (pileLarge t₁ (a₁ + 1) j : ℝ) + (pileSmall t₁ (a₁ + 1) (nB - 1) K₁ j : ℝ) := by
          have : Mstar + 1 ≤ pileLarge t₁ (a₁ + 1) j + pileSmall t₁ (a₁ + 1) (nB - 1) K₁ j := by omega
          exact_mod_cast this
        unfold ownCost; simp only [Nat.cast_zero, add_zero]; push_cast
        nlinarith only [htau, hstep2, hminR, hr₂]
    }⟩
  · -- ¬ hbridgeB: use Lemma C to prove maxLargeSize₁ ≥ Mstar + 2, so B_moveC is EFX!
    push Not at hbridgeB
    have hL2_ge : Mstar + 1 ≤ maxLargeSize t₂ a₂ nC K₂ ht₂ :=
      le_trans hM2_ge (pileMinSize_le_size ht₂ hK₂2 idx2)
    have htau1_gt : r₁ * (Mstar : ℝ) + 1 < pileTau t₁ (a₁ + 1) (nB - 1) K₁ r₁ := by
      have hMR : (Mstar : ℝ) ≤ ((maxLargeSize t₂ a₂ nC K₂ ht₂ - 1 : ℕ) : ℝ) := by
        have : Mstar ≤ maxLargeSize t₂ a₂ nC K₂ ht₂ - 1 := by omega
        exact_mod_cast this
      nlinarith only [hbridgeB, hMR, hr₁]
    -- Contrapositive of Lemma C on Pile 1 (a₁ + 1, nB)!
    have hL1_ge : Mstar + 2 ≤ maxLargeSize t₁ (a₁ + 1) nB K₁ ht₁ := by
      by_contra hle
      have hle' : maxLargeSize t₁ (a₁ + 1) nB K₁ ht₁ ≤ Mstar + 1 := by omega
      have hC := pileTau_sub_one_le_of_maxLargeSize ht₁ hr₁ hK₁_lo hK₁_hi hnB_pos hMstar_pos hle'
      linarith only [hC, htau1_gt]
    -- Construct B_moveC = (a₁, nB, 1 | a₂, 0, nC - 1)!
    let idx1 : Fin t₁ := maxLargeIdx t₁ (a₁ + 1) nB K₁ ht₁
    have hidx1_pos : 0 < pileLarge t₁ (a₁ + 1) idx1 := maxLargeIdx_large_pos ht₁ (Nat.succ_pos a₁)
    let C1_fn : Fin t₁ → ℕ := fun i => if i = idx1 then 1 else 0
    let A1_fn : Fin t₁ → ℕ := fun i => if i = idx1 then pileLarge t₁ (a₁ + 1) i - 1 else pileLarge t₁ (a₁ + 1) i
    have hAC1 : ∀ i : Fin t₁, A1_fn i + C1_fn i = pileLarge t₁ (a₁ + 1) i := by
      intro i; simp only [A1_fn, C1_fn]
      split_ifs with hi
      · subst hi; omega
      · omega
    have hsumC1 : ∑ i : Fin t₁, C1_fn i = 1 := by simp [C1_fn]
    have hsumA1 : ∑ i : Fin t₁, A1_fn i = a₁ := by
      have htot : ∑ i : Fin t₁, (A1_fn i + C1_fn i) = a₁ + 1 := by
        simp_rw [hAC1]; exact sum_pileLarge ht₁
      rw [Finset.sum_add_distrib, hsumC1] at htot; omega
    refine ⟨{
      A1 := A1_fn
      B1 := pileSmall t₁ (a₁ + 1) nB K₁
      C1 := C1_fn
      A2 := pileLarge t₂ a₂
      B2 := fun _ => 0
      C2 := pileSmall t₂ a₂ (nC - 1) K₂
      sumA := by rw [hsumA1, sum_pileLarge ht₂]; omega
      sumB := by simp [sum_pileSmall ht₁]
      sumC := by rw [hsumC1, sum_pileSmall ht₂]; omega
      efx11 := fun i j => by
        rw [hAC1 i, hAC1 j]
        exact identicalPile_internal_efx ht₁ hr₁ hK₁_lo hK₁_hi i j
      efx22 := fun i j => by
        simpa using identicalPile_internal_efx ht₂ hr₂ hK₂_lo hK₂_hi i j
      efx12 := fun i j => by
        rw [hAC1 i]
        have htau := ownTau_le_pileTau ht₁ hr₁ hK₁_lo hK₁_hi (p := a₁ + 1) (s := nB) i
        have hmin := pileMinSize_le_size ht₂ hK₂2 (p := a₂) (s := nC - 1) j
        have hminR : (Mstar : ℝ) + 1 ≤
            (pileLarge t₂ a₂ j : ℝ) + (pileSmall t₂ a₂ (nC - 1) K₂ j : ℝ) := by
          have : Mstar + 1 ≤ pileLarge t₂ a₂ j + pileSmall t₂ a₂ (nC - 1) K₂ j := by omega
          exact_mod_cast this
        unfold ownCost; simp only [Nat.cast_zero, add_zero]; push_cast
        nlinarith only [htau, hstep1, hminR, hr₁]
      efx21 := fun i j => by
        have htau := ownTau_le_pileTau ht₂ hr₂ hK₂_lo hK₂_hi (p := a₂) (s := nC - 1) i
        simp only [add_zero]
        by_cases hj : j = idx1
        · subst hj
          have hcost_idx : ownCost r₂ (A1_fn idx1 + pileSmall t₁ (a₁ + 1) nB K₁ idx1) (C1_fn idx1) =
              r₂ * ((maxLargeSize t₁ (a₁ + 1) nB K₁ ht₁ - 1 : ℕ) : ℝ) + 1 := by
            unfold ownCost maxLargeSize
            simp only [A1_fn, C1_fn, ↓reduceIte, Nat.cast_one]
            have heq : pileLarge t₁ (a₁ + 1) idx1 - 1 + pileSmall t₁ (a₁ + 1) nB K₁ idx1 =
                pileLarge t₁ (a₁ + 1) idx1 + pileSmall t₁ (a₁ + 1) nB K₁ idx1 - 1 := by omega
            rw [heq]; ring
          rw [hcost_idx]
          have hMR : (Mstar : ℝ) + 1 ≤ ((maxLargeSize t₁ (a₁ + 1) nB K₁ ht₁ - 1 : ℕ) : ℝ) := by
            have : Mstar + 1 ≤ maxLargeSize t₁ (a₁ + 1) nB K₁ ht₁ - 1 := by omega
            exact_mod_cast this
          nlinarith only [htau, hmono2, hstep2, hMR, hr₂]
        · have hA1j : A1_fn j = pileLarge t₁ (a₁ + 1) j := ite_eq_right hj
          have hC1j : C1_fn j = 0 := ite_eq_right hj
          rw [hA1j, hC1j]; unfold ownCost
          have hmin := pileMinSize_le_size ht₁ hK₁2 (p := a₁ + 1) (s := nB) j
          have hminR : (Mstar : ℝ) + 1 ≤
              (pileLarge t₁ (a₁ + 1) j : ℝ) + (pileSmall t₁ (a₁ + 1) nB K₁ j : ℝ) := by
            have : Mstar + 1 ≤ pileLarge t₁ (a₁ + 1) j + pileSmall t₁ (a₁ + 1) nB K₁ j := by omega
            exact_mod_cast this
          simp only [Nat.cast_zero, add_zero]; push_cast
          nlinarith only [htau, hmono2, hstep2, hminR, hr₂]
    }⟩

/-! ### Complete Two-Type Specification Existence (Phases 1, 2, 3 + Bridge) -/

/-- **Main Combinatorial Existence Theorem**: for all `t₁, t₂ ≥ 1`, `nA, nB, nC ≥ 0`, and
personalized ratios `r₁, r₂ > 1`, there exists an EFX `TwoTypeSpec`. -/
theorem exists_twoTypeSpec {t₁ t₂ nA nB nC : ℕ} {r₁ r₂ : ℝ}
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂) (hr₁ : 1 < r₁) (hr₂ : 1 < r₂) :
    Nonempty (TwoTypeSpec t₁ t₂ nA nB nC r₁ r₂) := by
  obtain ⟨K₁, hK₁2, hK₁_lo, hK₁_hi⟩ := exists_ceil_gt_one hr₁
  obtain ⟨K₂, hK₂2, hK₂_lo, hK₂_hi⟩ := exists_ceil_gt_one hr₂
  let E₁ : ℕ → Prop := fun a₁ =>
    r₁ * (pileMinSize t₂ (nA - a₁) nC K₂ : ℝ) < pileTau t₁ a₁ nB K₁ r₁
  let E₂ : ℕ → Prop := fun a₁ =>
    r₂ * (pileMinSize t₁ a₁ nB K₁ : ℝ) < pileTau t₂ (nA - a₁) nC K₂ r₂
  -- Case 1: ¬ E₂ 0 → solved by Phase 1!
  by_cases hJ1 : E₂ 0
  · -- Case 2: ¬ E₁ nA → solved by Phase 3 (exact mirror of Phase 1 via `swap`)!
    by_cases hJ2 : E₁ nA
    · -- Case 3: E₂ 0 ∧ E₁ nA → run Discrete Bolzano on Phase 2 (0 .. nA)!
      have hmutex : ∀ a₁ : ℕ, ¬ (E₁ a₁ ∧ E₂ a₁) := by
        rintro a₁ ⟨h1, h2⟩
        have hf1 := pileTau_le_r_mul_minSize (t := t₁) (p := a₁) (s := nB) (K := K₁) ht₁ hr₁ hK₁_lo hK₁_hi
        have hf2 := pileTau_le_r_mul_minSize (t := t₂) (p := nA - a₁) (s := nC) (K := K₂) ht₂ hr₂ hK₂_lo hK₂_hi
        have hm1 : (pileMinSize t₂ (nA - a₁) nC K₂ : ℝ) < (pileMinSize t₁ a₁ nB K₁ : ℝ) := by
          nlinarith only [h1, hf1, hr₁]
        have hm2 : (pileMinSize t₁ a₁ nB K₁ : ℝ) < (pileMinSize t₂ (nA - a₁) nC K₂ : ℝ) := by
          nlinarith only [h2, hf2, hr₂]
        linarith only [hm1, hm2]
      have hnotE1_0 : ¬ E₁ 0 := fun h => hmutex 0 ⟨h, hJ1⟩
      have hnotE2_nA : ¬ E₂ nA := fun h => hmutex nA ⟨hJ2, h⟩
      rcases discrete_bolzano E₁ E₂ hnotE1_0 hnotE2_nA with ⟨a₁, ha₁, h1, h2⟩ | ⟨a₁, ha₁, h2, h1⟩
      · -- Phase 2 state (a₁, nB, 0 | nA - a₁, 0, nC) is directly EFX!
        dsimp only [E₁, E₂] at h1 h2
        push Not at h1 h2
        refine ⟨{
          A1 := pileLarge t₁ a₁
          B1 := pileSmall t₁ a₁ nB K₁
          C1 := fun _ => 0
          A2 := pileLarge t₂ (nA - a₁)
          B2 := fun _ => 0
          C2 := pileSmall t₂ (nA - a₁) nC K₂
          sumA := by rw [sum_pileLarge ht₁, sum_pileLarge ht₂]; omega
          sumB := by simp [sum_pileSmall ht₁]
          sumC := by simp [sum_pileSmall ht₂]
          efx11 := fun i j => by
            simpa using identicalPile_internal_efx ht₁ hr₁ hK₁_lo hK₁_hi i j
          efx22 := fun i j => by
            simpa using identicalPile_internal_efx ht₂ hr₂ hK₂_lo hK₂_hi i j
          efx12 := fun i j => by
            have htau := ownTau_le_pileTau ht₁ hr₁ hK₁_lo hK₁_hi (p := a₁) (s := nB) i
            have hmin := pileMinSize_le_size ht₂ hK₂2 (p := nA - a₁) (s := nC) j
            have hminR : (pileMinSize t₂ (nA - a₁) nC K₂ : ℝ) ≤
                (pileLarge t₂ (nA - a₁) j : ℝ) + (pileSmall t₂ (nA - a₁) nC K₂ j : ℝ) := by
              exact_mod_cast hmin
            simp only [add_zero]; unfold ownCost; push_cast
            nlinarith only [htau, h1, hminR, hr₁]
          efx21 := fun i j => by
            have htau := ownTau_le_pileTau ht₂ hr₂ hK₂_lo hK₂_hi (p := nA - a₁) (s := nC) i
            have hmin := pileMinSize_le_size ht₁ hK₁2 (p := a₁) (s := nB) j
            have hminR : (pileMinSize t₁ a₁ nB K₁ : ℝ) ≤
                (pileLarge t₁ a₁ j : ℝ) + (pileSmall t₁ a₁ nB K₁ j : ℝ) := by
              exact_mod_cast hmin
            simp only [add_zero]; unfold ownCost; push_cast
            nlinarith only [htau, h2, hminR, hr₂]
        }⟩
      · -- Phase 2 Jump at a₁ < nA: E₂ a₁ ∧ E₁ (a₁ + 1)!
        exact exists_twoTypeSpec_phase2_jump ht₁ ht₂ hr₁ hr₂ hK₁2 hK₁_lo hK₁_hi
          hK₂2 hK₂_lo hK₂_hi ha₁ h2 h1
    · -- Case 2: ¬ E₁ nA → Phase 3 via exact symmetry!
      have h_end_swap : ¬ r₁ * (pileMinSize t₂ 0 nC K₂ : ℝ) < pileTau t₁ nA nB K₁ r₁ := by
        simpa [E₁] using hJ2
      obtain ⟨S⟩ := exists_twoTypeSpec_phase1 ht₂ ht₁ hr₂ hr₁ hK₂2 hK₂_lo hK₂_hi hK₁_lo hK₁_hi h_end_swap
      exact ⟨S.swap⟩
  · -- Case 1: ¬ E₂ 0 → Phase 1!
    have h_end : ¬ r₂ * (pileMinSize t₁ 0 nB K₁ : ℝ) < pileTau t₂ nA nC K₂ r₂ := by
      simpa [E₂] using hJ1
    exact exists_twoTypeSpec_phase1 ht₁ ht₂ hr₁ hr₂ hK₁2 hK₁_lo hK₁_hi hK₂_lo hK₂_hi h_end

/-! ### Single-Type (Identical Agents) Bi-Valued EFX Theorem -/

/-- **Identical Bi-Valued Agents Theorem**: for any `n ≥ 1`, `m ≥ 0`, and identical bi-valued
disutilities `v : Fin m → ℝ` taking values in `{1, r}` (`1 < r`), an EFX allocation exists. -/
theorem exists_efx_identical_bivalued_norm {n m : ℕ} (hn : 0 < n)
    (v : Fin m → ℝ) (r : ℝ) (hr : 1 < r) (hbiv : ∀ g, v g = 1 ∨ v g = r) :
    ∃ alloc : Fin m → Fin n, IsEFX (fun _ g => v g) alloc := by
  classical
  obtain ⟨K, _, hK_lo, hK_hi⟩ := exists_ceil_gt_one hr
  obtain ⟨p, s, e, hP, hNP⟩ := equiv_partition_fin (fun g : Fin m => v g ≠ 1)
  have hlarge : ∀ x : Fin p, v (e.symm (Fin.castAdd s x)) = r := by
    intro x
    rcases hbiv (e.symm (Fin.castAdd s x)) with h1 | hr'
    · exact absurd h1 (hP x)
    · exact hr'
  have hsmall : ∀ y : Fin s, v (e.symm (Fin.natAdd p y)) = 1 := by
    intro y
    have hnn := hNP y
    push Not at hnn
    exact hnn
  obtain ⟨fL, hfL⟩ := exists_assignment_with_counts (pileLarge n p) (sum_pileLarge hn)
  obtain ⟨fS, hfS⟩ := exists_assignment_with_counts (pileSmall n p s K) (sum_pileSmall hn)
  let alloc' : Fin (p + s) → Fin n := Fin.addCases fL fS
  let cost' : Fin n → Fin (p + s) → ℝ := fun _ g' => v (e.symm g')
  have hcost' : ∀ i k : Fin n,
      bundleCost cost' (bundle alloc' k) i =
        ownCost r (pileLarge n p k) (pileSmall n p s K k) := by
    intro i k
    unfold bundleCost bundle
    rw [Finset.sum_filter, Fin.sum_univ_add]
    simp only [alloc', cost', Fin.addCases_left, Fin.addCases_right, ← Finset.sum_filter,
      hlarge, hsmall, Finset.sum_const, nsmul_eq_mul, hfL k, hfS k, ownCost]
    ring
  have hefx' : IsEFX cost' alloc' := by
    intro i j g hg
    rw [bundleCost_sdiff_singleton cost' hg, hcost' i i, hcost' i j]
    have htau_ge : ownCost r (pileLarge n p i) (pileSmall n p s K i) - cost' i g ≤
        ownTau r (pileLarge n p i) (pileSmall n p s K i) := by
      have hg_eq : alloc' g = i := mem_bundle.mp hg
      revert hg_eq
      refine Fin.addCases (fun gL hg_eq => ?_) (fun gS hg_eq => ?_) g
      · have hgL : fL gL = i := by simpa [alloc'] using hg_eq
        have hposL : 0 < pileLarge n p i := by
          rw [← hfL]; exact Finset.card_pos.mpr ⟨gL, by simp [hgL]⟩
        simp only [cost', hlarge]
        unfold ownTau
        rw [ite_eq_right (by omega)]
        split_ifs <;> linarith
      · have hgS : fS gS = i := by simpa [alloc'] using hg_eq
        have hposS : 0 < pileSmall n p s K i := by
          rw [← hfS]; exact Finset.card_pos.mpr ⟨gS, by simp [hgS]⟩
        simp only [cost', hsmall]
        unfold ownTau
        rw [ite_eq_right (by omega), ite_eq_left (hposS)]
    exact le_trans htau_ge (identicalPile_internal_efx hn hr hK_lo hK_hi i j)
  exact ⟨fun g => alloc' (e g), isEFX_reindex_items e (fun _ g => v g) hefx'⟩

/-! ### Top-Level Main Theorem -/

/-- **Main Theorem (EFX Existence for Personalized Bi-Valued Chores with Two Agent Types)**:
For every `n ≥ 1`, every `m ≥ 0`, and every additive chores instance with two agent types
(`cls : Fin n → Bool`) whose disutilities are personalized bi-valued (`v b g ∈ {p b, q b}` with
`0 < p b ≤ q b`), there always exists a complete EFX allocation. -/
theorem exists_efx_two_agent_types_bivalued
    {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ)
    (cls : Fin n → Bool)
    (v : Bool → Fin m → ℝ)
    (h_types : ∀ i g, cost i g = v (cls i) g)
    (p q : Bool → ℝ)
    (hp : ∀ b, 0 < p b) (hpq : ∀ b, p b ≤ q b)
    (hbiv : ∀ b g, v b g = p b ∨ v b g = q b) :
    ∃ alloc : Fin m → Fin n, IsEFX cost alloc := by
  classical
  -- Step 1: Normalize each type by dividing by p b > 0
  let r : Bool → ℝ := fun b => if p b < q b then q b / p b else 2
  have hr : ∀ b, 1 < r b := by
    intro b; simp only [r]
    split_ifs with hlt
    · exact (one_lt_div (hp b)).mpr hlt
    · norm_num
  let vN : Bool → Fin m → ℝ := fun b g => v b g / p b
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
  have hscale : ∀ i g, cost i g = p (cls i) * costN i g := by
    intro i g
    simp only [h_types, costN, vN]
    exact (mul_div_cancel₀ _ (ne_of_gt (hp (cls i)))).symm
  -- Suffices to find EFX for normalized costN
  suffices hexN : ∃ alloc : Fin m → Fin n, IsEFX costN alloc by
    rcases hexN with ⟨alloc, hefxN⟩
    exact ⟨alloc, (isEFX_scale (fun i => p (cls i)) (fun i => hp (cls i)) hscale).mpr hefxN⟩
  -- Step 2: Partition agents into Group 1 (cls = false) and Group 2 (cls = true)
  obtain ⟨t₁, t₂, eAg, hAg1, hAg2⟩ := equiv_partition_fin (fun i : Fin n => cls i = false)
  let costAg : Fin (t₁ + t₂) → Fin m → ℝ := fun i' g => costN (eAg.symm i') g
  suffices hexAg : ∃ alloc' : Fin m → Fin (t₁ + t₂), IsEFX costAg alloc' by
    rcases hexAg with ⟨alloc', hefx'⟩
    exact ⟨fun g => eAg.symm (alloc' g), isEFX_reindex_agents eAg costN hefx'⟩
  have hAg1_cost : ∀ (i : Fin t₁) g, costAg (Fin.castAdd t₂ i) g = vN false g := by
    intro i g; simp [costAg, costN, hAg1 i]
  have hAg2_cost : ∀ (i : Fin t₂) g, costAg (Fin.natAdd t₁ i) g = vN true g := by
    intro i g
    have htrue : cls (eAg.symm (Fin.natAdd t₁ i)) = true := by
      have := hAg2 i; cases h : cls (eAg.symm (Fin.natAdd t₁ i)) <;> simp_all
    simp [costAg, costN, htrue]
  -- Check degenerate single-type cases: t₁ = 0 or t₂ = 0!
  have hn_eq : t₁ + t₂ = n := by
    have := Fintype.card_congr eAg
    simpa using this.symm
  by_cases ht₁ : t₁ = 0
  · subst ht₁
    have ht₂_pos : 0 < t₂ := by omega
    have hident : costAg = fun _ g => vN true g := by
      funext i g
      have hi : i = Fin.natAdd 0 ⟨i.1, by omega⟩ := by ext; simp
      rw [hi, hAg2_cost]
    rw [hident]
    exact exists_efx_identical_bivalued_norm (by omega : 0 < 0 + t₂) (vN true) (r true) (hr true) (hvN_biv true)
  by_cases ht₂ : t₂ = 0
  · subst ht₂
    have ht₁_pos : 0 < t₁ := by omega
    have hident : costAg = fun _ g => vN false g := by
      funext i g
      have hi : i = Fin.castAdd 0 ⟨i.1, by omega⟩ := by ext; simp
      rw [hi, hAg1_cost]
    rw [hident]
    exact exists_efx_identical_bivalued_norm ht₁_pos (vN false) (r false) (hr false) (hvN_biv false)
  have ht₁_pos : 0 < t₁ := by omega
  have ht₂_pos : 0 < t₂ := by omega
  -- Step 3: Split off all-small chores D = {g | vN false g = 1 ∧ vN true g = 1}!
  obtain ⟨mABC, mD, eD, hNotD, hD⟩ :=
    equiv_partition_fin (fun g : Fin m => ¬ (vN false g = 1 ∧ vN true g = 1))
  let costD : Fin (t₁ + t₂) → Fin (mABC + mD) → ℝ := fun i g' => costAg i (eD.symm g')
  suffices hexD : ∃ allocD : Fin (mABC + mD) → Fin (t₁ + t₂), IsEFX costD allocD by
    rcases hexD with ⟨allocD, hefxD⟩
    exact ⟨fun g => allocD (eD g), isEFX_reindex_items eD costAg hefxD⟩
  -- Apply Iterated All-Small Insertion Lemma to reduce to Fin mABC!
  have hcostD_ge1 : ∀ i g', 1 ≤ costD i g' := by
    intro i g'
    refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
    · simp only [costD, hAg1_cost]
      rcases hvN_biv false (eD.symm g') with h1 | hr'
      · linarith
      · linarith [hr false]
    · simp only [costD, hAg2_cost]
      rcases hvN_biv true (eD.symm g') with h1 | hr'
      · linarith
      · linarith [hr true]
  have hcostD_nn : ∀ i g', 0 ≤ costD i g' := fun i g' => by linarith [hcostD_ge1 i g']
  have hcostD_small : ∀ i (k : Fin mD) g', costD i (Fin.natAdd mABC k) ≤ costD i g' := by
    intro i k g'
    have hDk := hD k
    push Not at hDk
    have hval1 : costD i (Fin.natAdd mABC k) = 1 := by
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · simp [costD, hAg1_cost, hDk.1]
      · simp [costD, hAg2_cost, hDk.2]
    rw [hval1]
    exact hcostD_ge1 i g'
  apply exists_efx_extend_all_small (by omega : 0 < t₁ + t₂) costD hcostD_nn hcostD_small
  -- Step 4: Partition Fin mABC into A, B, C!
  let costABC : Fin (t₁ + t₂) → Fin mABC → ℝ := fun i g => costD i (Fin.castAdd mD g)
  -- Split off C = {g | vN true g = 1} (since ¬ D, these have vN false g = r false!)
  obtain ⟨mAB, nC, eC, hNotC, hC⟩ :=
    equiv_partition_fin (fun g : Fin mABC => vN true (eD.symm (Fin.castAdd mD g)) ≠ 1)
  -- Split mAB into A = {vN false ≠ 1} and B = {vN false = 1}
  obtain ⟨nA, nB, eAB, hA, hB⟩ :=
    equiv_partition_fin (fun g : Fin mAB => vN false (eD.symm (Fin.castAdd mD (eC.symm (Fin.castAdd nC g)))) ≠ 1)
  let eABC : Fin mABC ≃ Fin ((nA + nB) + nC) :=
    eC.trans ((finSumFinEquiv.symm.trans (eAB.sumCongr (Equiv.refl (Fin nC)))).trans finSumFinEquiv)
  let costNorm : Fin (t₁ + t₂) → Fin ((nA + nB) + nC) → ℝ := fun i g => costABC i (eABC.symm g)
  suffices hexNorm : ∃ allocN : Fin ((nA + nB) + nC) → Fin (t₁ + t₂), IsEFX costNorm allocN by
    rcases hexNorm with ⟨allocN, hefxN⟩
    exact ⟨fun g => allocN (eABC g), isEFX_reindex_items eABC costABC hefxN⟩
  -- Verify exact normalized costs on A, B, C!
  have heABC_A : ∀ g : Fin nA,
      eABC.symm (Fin.castAdd nC (Fin.castAdd nB g)) = eC.symm (Fin.castAdd nC (eAB.symm (Fin.castAdd nB g))) := by
    intro g
    have hL : (finSumFinEquiv : Fin (nA + nB) ⊕ Fin nC ≃ Fin ((nA + nB) + nC)).symm
        (Fin.castAdd nC (Fin.castAdd nB g)) = Sum.inl (Fin.castAdd nB g) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eABC, hL]
  have heABC_B : ∀ g : Fin nB,
      eABC.symm (Fin.castAdd nC (Fin.natAdd nA g)) = eC.symm (Fin.castAdd nC (eAB.symm (Fin.natAdd nA g))) := by
    intro g
    have hL : (finSumFinEquiv : Fin (nA + nB) ⊕ Fin nC ≃ Fin ((nA + nB) + nC)).symm
        (Fin.castAdd nC (Fin.natAdd nA g)) = Sum.inl (Fin.natAdd nA g) :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eABC, hL]
  have heABC_C : ∀ g : Fin nC,
      eABC.symm (Fin.natAdd (nA + nB) g) = eC.symm (Fin.natAdd mAB g) := by
    intro g
    have hR : (finSumFinEquiv : Fin (nA + nB) ⊕ Fin nC ≃ Fin ((nA + nB) + nC)).symm
        (Fin.natAdd (nA + nB) g) = Sum.inr g :=
      finSumFinEquiv.symm_apply_eq.mpr (by simp)
    simp [eABC, hR]
  obtain ⟨S⟩ := exists_twoTypeSpec (nA := nA) (nB := nB) (nC := nC) ht₁_pos ht₂_pos (hr false) (hr true)
  refine realize_twoTypeSpec (hr false) (hr true) costNorm ?_ ?_ ?_ ?_ ?_ ?_ S
  · intro i g
    simp only [costNorm, costABC, costD, hAg1_cost, heABC_A]
    rcases hvN_biv false _ with h1 | hr'
    · exact absurd h1 (hA g)
    · exact hr'
  · intro i g
    simp only [costNorm, costABC, costD, hAg2_cost, heABC_A]
    rcases hvN_biv true _ with h1 | hr'
    · exact absurd h1 (hNotC (eAB.symm (Fin.castAdd nB g)))
    · exact hr'
  · intro i g
    simp only [costNorm, costABC, costD, hAg1_cost, heABC_B]
    have hBg := hB g; push Not at hBg; exact hBg
  · intro i g
    simp only [costNorm, costABC, costD, hAg2_cost, heABC_B]
    rcases hvN_biv true _ with h1 | hr'
    · exact absurd h1 (hNotC (eAB.symm (Fin.natAdd nA g)))
    · exact hr'
  · intro i g
    simp only [costNorm, costABC, costD, hAg1_cost, heABC_C]
    have hCg := hC g; push Not at hCg
    have hND := hNotD (eC.symm (Fin.natAdd mAB g))
    rcases hvN_biv false _ with h1 | hr'
    · exact absurd ⟨h1, hCg⟩ hND
    · exact hr'
  · intro i g
    simp only [costNorm, costABC, costD, hAg2_cost, heABC_C]
    have hCg := hC g; push Not at hCg; exact hCg

end BivaluedChoresEFX
