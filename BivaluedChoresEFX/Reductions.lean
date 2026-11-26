module

public import BivaluedChoresEFX.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Max
import Mathlib.Order.Preorder.Finite

/-!
# General-n Reductions for Additive Chores (Arbitrary Agent Types)

This module formalizes two general-`n` theorems that hold for **arbitrary** numbers of agents `n`
and nonnegative additive disutilities:

1. **Modulo-`n` All-Large Reduction (`efx_add_all_large_round`)**: Adding `n` chores that each
   achieve agent `i`'s maximum disutility (one chore per agent) preserves EFX.
2. **All-Small Chore Insertion Lemma (`exists_efx_insert_all_small`,
   `exists_efx_extend_all_small`)**: Given an EFX allocation on a subset of chores, any number of
   all-small chores (minimum disutility for every agent) can be inserted while preserving EFX.
   Choose a cheapest bundle for each agent and rotate the bundles on one cycle of these
   choices. Each agent on that cycle then holds a cheapest bundle and can take the new chore.
-/

@[expose] public section

namespace BivaluedChoresEFX

open scoped BigOperators

section ModuloNReduction

/-- Adding one chore per agent, where each added chore has maximal cost `R i` for every agent `i`,
preserves EFX. This reduces the number of all-large chores modulo `n` for arbitrary agent types. -/
theorem efx_add_all_large_round {n m : ℕ}
    (cost : Fin n → Fin (m + n) → ℝ)
    (R : Fin n → ℝ)
    (hR_nn : ∀ i, 0 ≤ R i)
    (hnn : ∀ i (g : Fin m), 0 ≤ cost i (Fin.castAdd n g))
    (h_le_R : ∀ i (g : Fin m), cost i (Fin.castAdd n g) ≤ R i)
    (h_large : ∀ i (k : Fin n), cost i (Fin.natAdd m k) = R i)
    (alloc : Fin m → Fin n)
    (hefx : IsEFX (fun i g => cost i (Fin.castAdd n g)) alloc) :
    IsEFX cost (Fin.addCases alloc id) := by
  let alloc' : Fin (m + n) → Fin n := Fin.addCases alloc id
  have hdisj : ∀ (a : Fin m) (b : Fin n), Fin.castAdd n a ≠ Fin.natAdd m b := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hbundle_eq : ∀ k : Fin n,
      bundle alloc' k =
        insert (Fin.natAdd m k) ((bundle alloc k).map (Fin.castAddEmb n)) := by
    intro k
    ext x
    refine Fin.addCases (fun a => ?_) (fun b => ?_) x
    · simp [alloc', bundle, (hdisj a k)]
    · simp only [alloc', bundle, Finset.mem_filter, Finset.mem_univ, true_and, Fin.addCases_right,
        id_eq, Finset.mem_insert, Finset.mem_map, Fin.castAddEmb_apply]
      constructor
      · intro h; left; exact congrArg (Fin.natAdd m) h
      · rintro (h | ⟨a, _, ha⟩)
        · have hv := congrArg Fin.val h
          simp only [Fin.val_natAdd] at hv
          exact Fin.ext (by omega)
        · exact absurd ha (hdisj a b)
  have hnotmem : ∀ k : Fin n,
      Fin.natAdd m k ∉ (bundle alloc k).map (Fin.castAddEmb n) := by
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨a, _, ha⟩
    exact hdisj a k ha
  have hcost_bundle : ∀ i k : Fin n,
      bundleCost cost (bundle alloc' k) i =
        bundleCost (fun a g => cost a (Fin.castAdd n g)) (bundle alloc k) i + R i := by
    intro i k
    rw [hbundle_eq k, bundleCost_insert cost (hnotmem k)]
    simp [bundleCost, h_large]
  intro i j g hg
  rw [bundleCost_sdiff_singleton cost hg, hcost_bundle i i, hcost_bundle i j]
  have hg' : g ∈ insert (Fin.natAdd m i) ((bundle alloc i).map (Fin.castAddEmb n)) := by
    rwa [← hbundle_eq i]
  rcases Finset.mem_insert.mp hg' with rfl | hg_old
  · -- g is the newly added all-large chore Fin.natAdd m i
    rw [h_large i i]
    by_cases hemp : (bundle alloc i).Nonempty
    · obtain ⟨g₀, hg₀⟩ := hemp
      have h0 := hefx i j g₀ hg₀
      rw [bundleCost_sdiff_singleton (fun a x => cost a (Fin.castAdd n x)) hg₀] at h0
      have hle := h_le_R i g₀
      linarith
    · rw [Finset.not_nonempty_iff_eq_empty.mp hemp, bundleCost_empty]
      have hnn_j : 0 ≤ bundleCost (fun a x => cost a (Fin.castAdd n x)) (bundle alloc j) i :=
        bundleCost_nonneg (hnn i) (bundle alloc j)
      linarith [hR_nn i]
  · -- g is an old chore Fin.castAdd n g₀
    rcases Finset.mem_map.mp hg_old with ⟨g₀, hg₀, rfl⟩
    have h0 := hefx i j g₀ hg₀
    rw [bundleCost_sdiff_singleton (fun a x => cost a (Fin.castAdd n x)) hg₀] at h0
    simp only [Fin.castAddEmb_apply]
    linarith

end ModuloNReduction

section AllSmallInsertion

/-- Every finite nonempty directed graph with no directed cycles (equivalently, no nonempty
sequence of edges returning to its start) has a sink (a vertex with no outgoing edges). -/
lemma exists_sink_of_no_cycle {V : Type*} [Fintype V] [Nonempty V]
    (E : V → V → Prop)
    (hacyc : ∀ (k : ℕ), 0 < k → ∀ (p : Fin (k + 1) → V),
      (∀ t : Fin k, E (p t.castSucc) (p t.succ)) → p 0 ≠ p (Fin.last k)) :
    ∃ s : V, ∀ v : V, ¬ E s v := by
  classical
  by_contra h
  push Not at h
  -- Construct an infinite walk using choice: step v picks some neighbor with E v (step v)
  choose step hstep using h
  let v₀ : V := Classical.arbitrary V
  let walk : ℕ → V := fun t => step^[t] v₀
  have hwalk_edge : ∀ t : ℕ, E (walk t) (walk (t + 1)) := by
    intro t
    simpa [walk, Function.iterate_succ_apply'] using hstep (walk t)
  obtain ⟨a, b, hlt, hab⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := walk) (fun _ => Set.mem_univ _)
  let k := b - a
  have hk : 0 < k := Nat.sub_pos_of_lt hlt
  let p (t : Fin (k + 1)) := walk (a + t.val)
  have hp_edge (t : Fin k) : E (p t.castSucc) (p t.succ) := by
    simpa [p, Nat.add_assoc] using hwalk_edge (a + t.val)
  have hp_eq : p 0 = p (Fin.last k) := by
    have hb : a + k = b := by dsimp [k]; omega
    simpa [p, hb] using hab
  exact hacyc k hk p hp_edge hp_eq

/-- Total social cost of an allocation. -/
def socialCost {n m : ℕ} (cost : Fin n → Fin m → ℝ) (alloc : Fin m → Fin n) : ℝ :=
  ∑ i : Fin n, bundleCost cost (bundle alloc i) i

/-- Most-envy directed edge: `i` strictly envies `j` AND `j`'s bundle attains `i`'s minimum
bundle disutility among all agents. -/
def MostEnvyEdge {n m : ℕ} (cost : Fin n → Fin m → ℝ) (alloc : Fin m → Fin n)
    (i j : Fin n) : Prop :=
  bundleCost cost (bundle alloc j) i < bundleCost cost (bundle alloc i) i ∧
  ∀ k : Fin n, bundleCost cost (bundle alloc j) i ≤ bundleCost cost (bundle alloc k) i

/-- Follow a map on a finite set until a vertex repeats. Rotating that cycle agrees with
the map on the cycle and fixes all other vertices. -/
private lemma exists_cycle_rotation {V : Type*} [Finite V] (f : V → V) (start : V) :
    ∃ (σ : Equiv.Perm V) (s : V), σ s = f s ∧ ∀ i, σ i = f i ∨ σ i = i := by
  classical
  obtain ⟨a, b, hab, hrepeat⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem
    (f := fun k : ℕ => f^[k] start) (fun _ => Set.mem_univ _)
  let s := f^[a] start
  have hreturn : f^[b - a] s = s := by
    change f^[b - a] (f^[a] start) = f^[a] start
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab.le, hrepeat]
  let orbit := Set.range (fun k : ℕ => f^[k] s)
  let rotate (i : V) := if i ∈ orbit then f i else i
  have hsurj : Function.Surjective rotate := by
    intro i
    by_cases hi : i ∈ orbit
    · obtain ⟨k, rfl⟩ := hi
      -- Moving a full period ends at the same vertex, so its predecessor is in the orbit.
      let t := k + (b - a - 1)
      refine ⟨f^[t] s, ?_⟩
      have ht : f^[t] s ∈ orbit := ⟨t, rfl⟩
      simp only [rotate, ite_eq_left ht]
      rw [← Function.iterate_succ_apply' f t s, show t.succ = k + (b - a) by dsimp [t]; omega,
        Function.iterate_add_apply, hreturn]
    · exact ⟨i, ite_eq_right hi⟩
  let σ : Equiv.Perm V := Equiv.ofBijective rotate (Finite.surjective_iff_bijective.mp hsurj)
  have hs : s ∈ orbit := ⟨0, rfl⟩
  refine ⟨σ, s, ite_eq_left hs, fun i => ?_⟩
  by_cases hi : i ∈ orbit
  · exact Or.inl (ite_eq_left hi)
  · exact Or.inr (ite_eq_right hi)

/-- Starting from an EFX allocation, one rotation of cheapest bundles yields an EFX
allocation in which some agent holds a cheapest bundle. -/
theorem exists_efx_with_envy_free_agent {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ) (hnn : ∀ i g, 0 ≤ cost i g)
    (hex : ∃ alloc : Fin m → Fin n, IsEFX cost alloc) :
    ∃ (alloc : Fin m → Fin n) (s : Fin n),
      IsEFX cost alloc ∧
      ∀ k : Fin n, bundleCost cost (bundle alloc s) s ≤ bundleCost cost (bundle alloc k) s := by
  classical
  let start : Fin n := ⟨0, hn⟩
  have : Nonempty (Fin n) := ⟨start⟩
  obtain ⟨alloc, hefx⟩ := hex
  have cheapest (i : Fin n) : ∃ j, ∀ k : Fin n,
      bundleCost cost (bundle alloc j) i ≤ bundleCost cost (bundle alloc k) i := by
    obtain ⟨j, _, hj⟩ := Finset.univ.exists_min_image
      (fun k => bundleCost cost (bundle alloc k) i) Finset.univ_nonempty
    exact ⟨j, fun k => hj k (Finset.mem_univ k)⟩
  choose best hbest using cheapest
  obtain ⟨σ, s, hs, hσ⟩ := exists_cycle_rotation best start
  let rotated (g : Fin m) := σ.symm (alloc g)
  have hbundle (i : Fin n) : bundle rotated i = bundle alloc (σ i) := by
    ext g
    simp [rotated, bundle, Equiv.symm_apply_eq]
  refine ⟨rotated, s, ?_, ?_⟩
  · intro i j g hg
    rw [hbundle i] at hg ⊢
    rw [hbundle j]
    rcases hσ i with h | h
    · rw [bundleCost_sdiff_singleton cost hg, h]
      exact (sub_le_self _ (hnn i g)).trans (hbest i (σ j))
    · rw [h] at hg ⊢
      exact hefx i (σ j) g hg
  · intro j
    rw [hbundle s, hs, hbundle j]
    exact hbest s (σ j)

/-- **Single All-Small Chore Insertion Lemma**: If `cost` on `m + 1` chores admits an EFX allocation
on the first `m` chores, and the last chore `Fin.last m` has minimal disutility for every agent
(i.e. `cost i (Fin.last m) ≤ cost i g` for all `i, g`), then an EFX allocation exists on all
`m + 1` chores. -/
theorem exists_efx_insert_all_small {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin (m + 1) → ℝ)
    (hnn : ∀ i g, 0 ≤ cost i g)
    (hsmall : ∀ i g, cost i (Fin.last m) ≤ cost i g)
    (hex : ∃ alloc : Fin m → Fin n, IsEFX (fun i g => cost i g.castSucc) alloc) :
    ∃ alloc' : Fin (m + 1) → Fin n, IsEFX cost alloc' := by
  obtain ⟨alloc, s, hefx, hsink⟩ :=
    exists_efx_with_envy_free_agent hn (fun i g => cost i g.castSucc)
      (fun i g => hnn i g.castSucc) hex
  let alloc' : Fin (m + 1) → Fin n := Fin.snoc alloc s
  refine ⟨alloc', ?_⟩
  have hbundle_ne : ∀ k : Fin n, k ≠ s →
      bundle alloc' k = (bundle alloc k).map Fin.castSuccEmb := by
    intro k hks
    ext x
    refine Fin.lastCases ?_ (fun y => ?_) x
    · simp [alloc', bundle, Fin.snoc_last, hks.symm]
    · simp [alloc', bundle, Fin.snoc_castSucc]
  have hbundle_s :
      bundle alloc' s = insert (Fin.last m) ((bundle alloc s).map Fin.castSuccEmb) := by
    ext x
    refine Fin.lastCases ?_ (fun y => ?_) x
    · simp [alloc', bundle, Fin.snoc_last]
    · simp [alloc', bundle, Fin.snoc_castSucc]
  have hnotmem_s : Fin.last m ∉ (bundle alloc s).map Fin.castSuccEmb := by
    intro h
    rcases Finset.mem_map.mp h with ⟨y, _, hy⟩
    exact Fin.castSucc_ne_last y hy
  have hcost_old : ∀ i k : Fin n,
      bundleCost cost ((bundle alloc k).map Fin.castSuccEmb) i =
        bundleCost (fun a x => cost a x.castSucc) (bundle alloc k) i := by
    intro i k
    simp [bundleCost]
  have hcost_ge : ∀ i k : Fin n,
      bundleCost (fun a x => cost a x.castSucc) (bundle alloc k) i ≤
        bundleCost cost (bundle alloc' k) i := by
    intro i k
    by_cases hks : k = s
    · subst hks
      rw [hbundle_s, bundleCost_insert cost hnotmem_s, hcost_old]
      linarith [hnn i (Fin.last m)]
    · rw [hbundle_ne k hks, hcost_old]
  intro i j g hg
  by_cases his : i = s
  · subst his
    rw [bundleCost_sdiff_singleton cost hg, hbundle_s, bundleCost_insert cost hnotmem_s, hcost_old]
    have h1 : cost i (Fin.last m) ≤ cost i g := hsmall i g
    have h2 : bundleCost (fun a x => cost a x.castSucc) (bundle alloc i) i ≤
        bundleCost (fun a x => cost a x.castSucc) (bundle alloc j) i := hsink j
    have h3 := hcost_ge i j
    linarith
  · rw [hbundle_ne i his] at hg
    rcases Finset.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
    rw [bundleCost_sdiff_singleton cost (by rw [hbundle_ne i his]; exact Finset.mem_map.mpr ⟨g₀, hg₀, rfl⟩)]
    rw [hbundle_ne i his, hcost_old]
    have h0 := hefx i j g₀ hg₀
    rw [bundleCost_sdiff_singleton (fun a x => cost a x.castSucc) hg₀] at h0
    have h3 := hcost_ge i j
    simpa using le_trans h0 h3

/-- **Iterated All-Small Chore Insertion Lemma**: Given an EFX allocation on the first `m` chores,
any `d` additional chores that each have minimal disutility for every agent can be inserted while
preserving EFX. -/
theorem exists_efx_extend_all_small {n m d : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin (m + d) → ℝ)
    (hnn : ∀ i g, 0 ≤ cost i g)
    (hsmall : ∀ i (k : Fin d) g, cost i (Fin.natAdd m k) ≤ cost i g)
    (hex : ∃ alloc : Fin m → Fin n, IsEFX (fun i g => cost i (Fin.castAdd d g)) alloc) :
    ∃ alloc' : Fin (m + d) → Fin n, IsEFX cost alloc' := by
  induction d with
  | zero =>
    rcases hex with ⟨alloc, hefx⟩
    exact ⟨alloc, hefx⟩
  | succ d ih =>
    -- Reduce to inserting the last chore Fin.last (m + d) on top of the first m + d chores
    have hex_prev : ∃ alloc : Fin (m + d) → Fin n,
        IsEFX (fun i g => cost i g.castSucc) alloc := by
      apply ih (fun i g => cost i g.castSucc) (fun i g => hnn i g.castSucc)
      · intro i k g
        have h1 : (Fin.natAdd m k).castSucc = Fin.natAdd m k.castSucc := by
          ext; simp [Fin.natAdd]
        rw [h1]
        exact hsmall i k.castSucc g.castSucc
      · rcases hex with ⟨alloc, hefx⟩
        refine ⟨alloc, ?_⟩
        have h2 : ∀ i (g : Fin m), cost i (Fin.castAdd d g).castSucc = cost i (Fin.castAdd (d + 1) g) := by
          intro i g; congr 1
        simpa [h2] using hefx
    refine exists_efx_insert_all_small hn cost hnn ?_ hex_prev
    intro i g
    have hlast : (Fin.last (m + d) : Fin (m + (d + 1))) = Fin.natAdd m (Fin.last d) := by
      ext; simp [Fin.natAdd]
    change cost i (Fin.last (m + d)) ≤ cost i g
    rw [hlast]
    exact hsmall i (Fin.last d) g

end AllSmallInsertion

end BivaluedChoresEFX
