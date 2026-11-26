module

public import BivaluedChoresEFX.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Max

/-!
# General-n Reductions for Additive Chores (Arbitrary Agent Types)

This module formalizes two general-`n` theorems that hold for **arbitrary** numbers of agents `n`
and **arbitrary** additive disutilities (not restricted to two agent types):

1. **Modulo-`n` All-Large Reduction (`efx_add_all_large_round`)**: Adding `n` chores that each
   achieve agent `i`'s maximum disutility (one chore per agent) preserves EFX.
2. **All-Small Chore Insertion Lemma (`exists_efx_insert_all_small`,
   `exists_efx_extend_all_small`)**: Given an EFX allocation on a subset of chores, any number of
   all-small chores (minimum disutility for every agent) can be inserted while preserving EFX.
   The proof uses a global minimum-social-cost EFX allocation whose most-envy graph is acyclic,
   hence admits a sink (an envy-free agent) who can safely absorb the new all-small chore.
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

section MostEnvyDAG

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
  -- By pigeonhole on Fin (Fintype.card V + 1) → V, two indices collide
  have hnotinj : ¬ Function.Injective (fun t : Fin (Fintype.card V + 1) => walk t.1) := by
    intro hinj
    have hcard := Fintype.card_le_of_injective _ hinj
    simp at hcard
  unfold Function.Injective at hnotinj
  push Not at hnotinj
  rcases hnotinj with ⟨a, b, hab, hne⟩
  wlog hlt : a.1 < b.1 generalizing a b
  · have hgt : b.1 < a.1 := by
      have : a.1 ≠ b.1 := fun heq => hne (Fin.ext heq)
      omega
    exact this b a hab.symm hne.symm hgt
  let k := b.1 - a.1
  have hk : 0 < k := by omega
  let p : Fin (k + 1) → V := fun t => walk (a.1 + t.1)
  have hp_edge : ∀ t : Fin k, E (p t.castSucc) (p t.succ) := by
    intro t
    simpa [p, Nat.add_assoc] using hwalk_edge (a.1 + t.1)
  have hp_eq : p 0 = p (Fin.last k) := by
    simp only [p, Fin.val_zero, add_zero, Fin.val_last]
    have hba : a.1 + k = b.1 := by omega
    rw [hba]
    exact hab
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

/-- Every nonempty set of EFX allocations contains one with an envy-free agent (a sink of the
most-envy graph), obtained by minimizing total social cost over all EFX allocations. -/
theorem exists_efx_with_envy_free_agent {n m : ℕ} (hn : 0 < n)
    (cost : Fin n → Fin m → ℝ) (hnn : ∀ i g, 0 ≤ cost i g)
    (hex : ∃ alloc : Fin m → Fin n, IsEFX cost alloc) :
    ∃ (alloc : Fin m → Fin n) (s : Fin n),
      IsEFX cost alloc ∧
      ∀ k : Fin n, bundleCost cost (bundle alloc s) s ≤ bundleCost cost (bundle alloc k) s := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let S : Finset (Fin m → Fin n) := Finset.univ.filter (fun a => IsEFX cost a)
  have hS_ne : S.Nonempty := by
    rcases hex with ⟨a₀, ha₀⟩
    exact ⟨a₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₀⟩⟩
  obtain ⟨alloc, hmem, hmin⟩ := S.exists_min_image (socialCost cost) hS_ne
  have hefx : IsEFX cost alloc := (Finset.mem_filter.mp hmem).2
  -- Show MostEnvyEdge cost alloc has no directed cycle; otherwise rotating a simple cycle
  -- strictly decreases socialCost while preserving EFX.
  have hacyc : ∀ (k : ℕ) (hk : 0 < k) (p : Fin (k + 1) → Fin n),
      (∀ t : Fin k, MostEnvyEdge cost alloc (p t.castSucc) (p t.succ)) →
      p 0 ≠ p (Fin.last k) := by
    -- Prove by strong induction on k so we may extract a simple cycle (injective on Fin k)
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk p hp heq
      -- Check if p is injective on Fin k (indices 0 .. k-1)
      by_cases hinj : Function.Injective (fun t : Fin k => p t.castSucc)
      · -- Simple cycle of length k! Define permutation σ rotating p(t) ↦ p(t+1) (mod k).
        -- Under the rotated allocation alloc'(g) = σ⁻¹(alloc(g)), agent p(t) receives bundle p(t+1),
        -- while agents outside the cycle keep their own bundle.
        let onCyc (i : Fin n) : Prop := ∃ t : Fin k, p t.castSucc = i
        -- Helper: next vertex on the cycle for t : Fin k
        let nxt (t : Fin k) : Fin k := ⟨(t.1 + 1) % k, Nat.mod_lt _ hk⟩
        have hp_nxt : ∀ t : Fin k, p (nxt t).castSucc = p t.succ := by
          intro t
          by_cases hlast : t.1 + 1 < k
          · have hmod : (t.1 + 1) % k = t.1 + 1 := Nat.mod_eq_of_lt hlast
            congr 1; ext; simpa [nxt] using hmod
          · have htk : t.1 + 1 = k := by omega
            have hmod : (t.1 + 1) % k = 0 := by rw [htk, Nat.mod_self]
            have h1 : (nxt t).castSucc = (0 : Fin (k + 1)) := by ext; simpa [nxt] using hmod
            have h2 : t.succ = Fin.last k := by ext; simpa using htk
            rw [h1, h2, heq]
        -- Helper: previous vertex on the cycle for t : Fin k
        let prv (t : Fin k) : Fin k := ⟨(t.1 + k - 1) % k, Nat.mod_lt _ hk⟩
        have hnxt_prv : ∀ t : Fin k, nxt (prv t) = t := by
          intro t
          ext
          simp only [nxt, prv]
          have ht := t.2
          by_cases h0 : t.1 = 0
          · have h1 : (0 + k - 1) % k = k - 1 := by
              rw [zero_add]
              exact Nat.mod_eq_of_lt (by omega)
            rw [h0, h1]
            have : k - 1 + 1 = k := by omega
            rw [this, Nat.mod_self]
          · have h1 : (t.1 + k - 1) % k = t.1 - 1 := by
              have : t.1 + k - 1 = (t.1 - 1) + k := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            rw [h1]
            have : t.1 - 1 + 1 = t.1 := by omega
            rw [this, Nat.mod_eq_of_lt ht]
        have hprv_nxt : ∀ t : Fin k, prv (nxt t) = t := by
          intro t
          ext
          simp only [nxt, prv]
          have ht := t.2
          by_cases hlast : t.1 + 1 < k
          · rw [Nat.mod_eq_of_lt hlast]
            have : t.1 + 1 + k - 1 = t.1 + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
          · have htk : t.1 + 1 = k := by omega
            rw [htk, Nat.mod_self, zero_add]
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
        -- Build bijection σ : Fin n ≃ Fin n with σ (p t.castSucc) = p t.succ and σ i = i off cycle
        let toFun (i : Fin n) : Fin n :=
          if h : ∃ t : Fin k, p t.castSucc = i then
            p (nxt h.choose).castSucc
          else i
        let invFun (i : Fin n) : Fin n :=
          if h : ∃ t : Fin k, p t.castSucc = i then
            p (prv h.choose).castSucc
          else i
        have hto_cyc : ∀ t : Fin k, toFun (p t.castSucc) = p (nxt t).castSucc := by
          intro t
          have h : ∃ s : Fin k, p s.castSucc = p t.castSucc := ⟨t, rfl⟩
          simp only [toFun, dite_eq_left h]
          have hch : h.choose = t := hinj h.choose_spec
          rw [hch]
        have hinv_cyc : ∀ t : Fin k, invFun (p t.castSucc) = p (prv t).castSucc := by
          intro t
          have h : ∃ s : Fin k, p s.castSucc = p t.castSucc := ⟨t, rfl⟩
          simp only [invFun, dite_eq_left h]
          have hch : h.choose = t := hinj h.choose_spec
          rw [hch]
        have hleft : Function.LeftInverse invFun toFun := by
          intro i
          by_cases h : ∃ t : Fin k, p t.castSucc = i
          · rcases h with ⟨t, rfl⟩
            rw [hto_cyc t, hinv_cyc (nxt t), hprv_nxt t]
          · simp only [toFun, invFun, dite_eq_right h]
        have hright : Function.RightInverse invFun toFun := by
          intro i
          by_cases h : ∃ t : Fin k, p t.castSucc = i
          · rcases h with ⟨t, rfl⟩
            rw [hinv_cyc t, hto_cyc (prv t), hnxt_prv t]
          · simp only [invFun, toFun, dite_eq_right h]
        let σ : Fin n ≃ Fin n := ⟨toFun, invFun, hleft, hright⟩
        -- Define rotated allocation: agent i receives old bundle (σ i)
        let alloc' : Fin m → Fin n := fun g => σ.symm (alloc g)
        have hbundle' : ∀ i : Fin n, bundle alloc' i = bundle alloc (σ i) := by
          intro i
          ext g
          simp [alloc', bundle, Equiv.symm_apply_eq]
        -- 1) alloc' is still EFX!
        have hefx' : IsEFX cost alloc' := by
          intro i j g hg
          rw [hbundle' i] at hg ⊢
          rw [hbundle' j]
          by_cases h : ∃ t : Fin k, p t.castSucc = i
          · rcases h with ⟨t, rfl⟩
            have hσt : σ (p t.castSucc) = p t.succ := by
              change toFun (p t.castSucc) = p t.succ
              rw [hto_cyc t, hp_nxt t]
            rw [hσt] at hg ⊢
            have hmin_t := (hp t).2 (σ j)
            rw [bundleCost_sdiff_singleton cost hg]
            linarith [hnn (p t.castSucc) g]
          · have hσi : σ i = i := by
              change toFun i = i
              simp [toFun, dite_eq_right h]
            rw [hσi] at hg ⊢
            exact hefx i (σ j) g hg
        -- 2) alloc' has STRICTLY SMALLER socialCost than alloc!
        have hsc_lt : socialCost cost alloc' < socialCost cost alloc := by
          unfold socialCost
          apply Finset.sum_lt_sum
          · intro i _
            rw [hbundle' i]
            by_cases h : ∃ t : Fin k, p t.castSucc = i
            · rcases h with ⟨t, rfl⟩
              have hσt : σ (p t.castSucc) = p t.succ := by
                change toFun (p t.castSucc) = p t.succ
                rw [hto_cyc t, hp_nxt t]
              rw [hσt]
              exact le_of_lt (hp t).1
            · have hσi : σ i = i := by
                change toFun i = i
                simp [toFun, dite_eq_right h]
              rw [hσi]
          · refine ⟨p (⟨0, hk⟩ : Fin k).castSucc, Finset.mem_univ _, ?_⟩
            rw [hbundle']
            have hσ0 : σ (p (⟨0, hk⟩ : Fin k).castSucc) = p (⟨0, hk⟩ : Fin k).succ := by
              change toFun _ = _
              rw [hto_cyc ⟨0, hk⟩, hp_nxt ⟨0, hk⟩]
            rw [hσ0]
            exact (hp ⟨0, hk⟩).1
        -- Contradiction with minimality of alloc!
        have hmem' : alloc' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hefx'⟩
        linarith [hmin alloc' hmem']
      · -- Not injective on Fin k: extract a strictly shorter cycle and apply IH!
        unfold Function.Injective at hinj
        push Not at hinj
        rcases hinj with ⟨a, b, hab, hne⟩
        have hne_val : a.1 ≠ b.1 := fun h => hne (Fin.ext h)
        rcases lt_or_gt_of_ne hne_val with hlt | hgt
        · let k' := b.1 - a.1
          have hk'_pos : 0 < k' := by omega
          have hk'_lt : k' < k := by omega
          let p' : Fin (k' + 1) → Fin n := fun t => p ⟨a.1 + t.1, by omega⟩
          have hp' : ∀ t : Fin k', MostEnvyEdge cost alloc (p' t.castSucc) (p' t.succ) := by
            intro t
            have ht_lt : a.1 + t.1 < k := by omega
            have hstep := hp ⟨a.1 + t.1, ht_lt⟩
            have h1 : (⟨a.1 + t.1, ht_lt⟩ : Fin k).castSucc = ⟨a.1 + t.castSucc.1, by omega⟩ := by
              ext; simp
            have h2 : (⟨a.1 + t.1, ht_lt⟩ : Fin k).succ = ⟨a.1 + t.succ.1, by omega⟩ := by
              ext; simp; omega
            simpa [p', h1, h2] using hstep
          have heq' : p' 0 = p' (Fin.last k') := by
            change p ⟨a.1 + 0, _⟩ = p ⟨a.1 + k', _⟩
            have h1 : (⟨a.1 + 0, by omega⟩ : Fin (k + 1)) = a.castSucc := by ext; simp
            have h2 : (⟨a.1 + k', by omega⟩ : Fin (k + 1)) = b.castSucc := by
              ext; simp [k']; omega
            rw [h1, h2]
            exact hab
          exact ih k' hk'_lt hk'_pos p' hp' heq'
        · let k' := a.1 - b.1
          have hk'_pos : 0 < k' := by omega
          have hk'_lt : k' < k := by omega
          let p' : Fin (k' + 1) → Fin n := fun t => p ⟨b.1 + t.1, by omega⟩
          have hp' : ∀ t : Fin k', MostEnvyEdge cost alloc (p' t.castSucc) (p' t.succ) := by
            intro t
            have ht_lt : b.1 + t.1 < k := by omega
            have hstep := hp ⟨b.1 + t.1, ht_lt⟩
            have h1 : (⟨b.1 + t.1, ht_lt⟩ : Fin k).castSucc = ⟨b.1 + t.castSucc.1, by omega⟩ := by
              ext; simp
            have h2 : (⟨b.1 + t.1, ht_lt⟩ : Fin k).succ = ⟨b.1 + t.succ.1, by omega⟩ := by
              ext; simp; omega
            simpa [p', h1, h2] using hstep
          have heq' : p' 0 = p' (Fin.last k') := by
            change p ⟨b.1 + 0, _⟩ = p ⟨b.1 + k', _⟩
            have h1 : (⟨b.1 + 0, by omega⟩ : Fin (k + 1)) = b.castSucc := by ext; simp
            have h2 : (⟨b.1 + k', by omega⟩ : Fin (k + 1)) = a.castSucc := by
              ext; simp [k']; omega
            rw [h1, h2]
            exact hab.symm
          exact ih k' hk'_lt hk'_pos p' hp' heq'
  -- Obtain a sink s of the acyclic MostEnvyEdge graph
  obtain ⟨s, hs⟩ := exists_sink_of_no_cycle (MostEnvyEdge cost alloc) hacyc
  refine ⟨alloc, s, hefx, ?_⟩
  -- Since s has no outgoing MostEnvyEdge, s's own bundle achieves min_k c_s(X_k)!
  obtain ⟨j₀, _, hj₀⟩ := (Finset.univ : Finset (Fin n)).exists_min_image
    (fun k => bundleCost cost (bundle alloc k) s) Finset.univ_nonempty
  have hnot : ¬ bundleCost cost (bundle alloc j₀) s < bundleCost cost (bundle alloc s) s := by
    intro hlt
    exact hs j₀ ⟨hlt, fun k => hj₀ k (Finset.mem_univ k)⟩
  push Not at hnot
  intro k
  exact le_trans hnot (hj₀ k (Finset.mem_univ k))

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

end MostEnvyDAG

end BivaluedChoresEFX
