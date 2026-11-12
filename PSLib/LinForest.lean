/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.HamConn

/-!
# Spanning linear forests with prescribed ends (Plantholt–Shan, Lemma 2.12)

Given pairs `(aᵢ, bᵢ)`, `i < t + 1`, of distinct vertices of a graph with large minimum degree, there
are vertex-disjoint paths `Pᵢ` from `aᵢ` to `bᵢ` covering all vertices. Proof (Plantholt–Shan): join
`a₀` and `b₀` through a common neighbour, delete the three vertices, and recurse; the last pair is
joined by a Hamiltonian path (Hamilton-connectedness, `PSLib.exists_hamiltonian_path`).
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib

open Finset SimpleGraph

universe u

/-- Deleting at most three vertices lowers the minimum degree by at most three. -/
theorem minDegree_induce_le {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : Set V) [DecidablePred (· ∈ s)] (T : Finset V)
    (hT : ∀ w, w ∉ s → w ∈ T) (hne : Nonempty s) :
    G.minDegree ≤ (G.induce s).minDegree + #T := by
  classical
  haveI := hne
  obtain ⟨w, hw⟩ := (G.induce s).exists_minimal_degree_vertex
  rw [hw]
  have h1 := G.minDegree_le_degree (w : V)
  have hsub : G.neighborFinset w ⊆
      ((G.induce s).neighborFinset w).map (Function.Embedding.subtype _) ∪ T := by
    intro x hx
    rw [mem_neighborFinset] at hx
    by_cases hxs : x ∈ s
    · refine mem_union_left _ (mem_map.2 ⟨⟨x, hxs⟩, ?_, rfl⟩)
      rw [mem_neighborFinset]; exact hx
    · exact mem_union_right _ (hT x hxs)
  have h2 := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h2
  omega

/-- **Spanning paths with prescribed ends.** -/
theorem exists_paths : ∀ (t : ℕ) {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a b : Fin (t + 1) → V), (∀ i j, a i ≠ b j) → Function.Injective a →
    Function.Injective b → Fintype.card V + 6 * (t + 1) + 2 ≤ 2 * G.minDegree →
    3 * (t + 1) + 5 ≤ Fintype.card V →
    ∃ P : ∀ i, G.Walk (a i) (b i), (∀ i, (P i).IsPath) ∧
      (∀ i j, i ≠ j → ∀ v, v ∈ (P i).support → v ∉ (P j).support) ∧
      ∀ v, ∃ i, v ∈ (P i).support := by
  intro t
  induction t with
  | zero =>
    intro V _ _ G _ a b hab _ _ hdeg hn
    obtain ⟨p, hp⟩ := PSLib.exists_hamiltonian_path G (by omega) (by omega) (hab 0 0)
    refine ⟨fun i => (Fin.fin_one_eq_zero i ▸ p : G.Walk (a i) (b i)), fun i => ?_,
      fun i j hij => absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij, fun v => ⟨0, ?_⟩⟩
    · obtain rfl := Fin.fin_one_eq_zero i
      exact hp.isPath
    · exact hp.mem_support v
  | succ t ih =>
    intro V _ _ G _ a b hab ha hb hdeg hn
    classical
    -- a common neighbour `c` of `a 0` and `b 0` outside all prescribed ends
    have hcommon : ∃ c, G.Adj (a 0) c ∧ G.Adj c (b 0) ∧ (∀ i, c ≠ a i) ∧ ∀ i, c ≠ b i := by
      have hNA : G.minDegree ≤ #(G.neighborFinset (a 0)) := by
        rw [card_neighborFinset_eq_degree]; exact G.minDegree_le_degree _
      have hNB : G.minDegree ≤ #(G.neighborFinset (b 0)) := by
        rw [card_neighborFinset_eq_degree]; exact G.minDegree_le_degree _
      have hunion := card_union_add_card_inter (G.neighborFinset (a 0)) (G.neighborFinset (b 0))
      have hle : #(G.neighborFinset (a 0) ∪ G.neighborFinset (b 0)) ≤ Fintype.card V :=
        card_le_univ _
      have himg : #(univ.image a ∪ univ.image b) ≤ 2 * (t + 2) := by
        have := card_union_le (univ.image a) (univ.image b)
        have h1 := card_image_le (s := (univ : Finset (Fin (t + 2)))) (f := a)
        have h2 := card_image_le (s := (univ : Finset (Fin (t + 2)))) (f := b)
        simp only [card_univ, Fintype.card_fin] at h1 h2
        omega
      have hsd := le_card_sdiff (univ.image a ∪ univ.image b)
        (G.neighborFinset (a 0) ∩ G.neighborFinset (b 0))
      have hN : 0 < #((G.neighborFinset (a 0) ∩ G.neighborFinset (b 0)) \ (univ.image a ∪ univ.image b)) := by
        omega
      obtain ⟨c, hc⟩ := card_pos.1 hN
      simp only [mem_sdiff, mem_inter, mem_neighborFinset, mem_union, mem_image, mem_univ,
        true_and, not_or, not_exists] at hc
      exact ⟨c, hc.1.1, (G.adj_comm _ _).1 hc.1.2, fun i h => hc.2.1 i h.symm,
        fun i h => hc.2.2 i h.symm⟩
    obtain ⟨c, hac, hcb, hca, hcb'⟩ := hcommon
    set s : Set V := {w | w ≠ a 0 ∧ w ≠ b 0 ∧ w ≠ c}
    have hcard : Fintype.card s + 3 = Fintype.card V := by
      rw [Fintype.card_subtype, ← card_univ]
      have : (univ.filter fun w => w ∈ s) = ((univ.erase (a 0)).erase (b 0)).erase c := by
        ext w; simp [s]; tauto
      rw [this, card_erase_of_mem (by simp [hcb' 0, hca 0]),
        card_erase_of_mem (by simp [(hab 0 0).symm]), card_erase_of_mem (mem_univ _)]
      have : 3 ≤ #(univ : Finset V) := by rw [card_univ]; omega
      omega
    have hmin := minDegree_induce_le G s {a 0, b 0, c}
      (fun w hw => by
        simp only [s, Set.mem_setOf_eq, not_and_or, not_not] at hw
        rcases hw with rfl | rfl | rfl <;> simp)
      (by rw [← Fintype.card_pos_iff]; omega)
    have h3 : #({a 0, b 0, c} : Finset V) ≤ 3 := card_le_three
    have hs : ∀ i : Fin (t + 1), a i.succ ∈ s ∧ b i.succ ∈ s := by
      intro i
      refine ⟨⟨fun h => Fin.succ_ne_zero i (ha h), hab _ _, fun h => hca _ h.symm⟩,
        ⟨fun h => hab 0 _ h.symm, fun h => Fin.succ_ne_zero i (hb h), fun h => hcb' _ h.symm⟩⟩
    obtain ⟨P', hP'p, hP'd, hP'c⟩ := ih (G.induce s) (fun i => ⟨a i.succ, (hs i).1⟩)
      (fun i => ⟨b i.succ, (hs i).2⟩)
      (fun i j h => hab i.succ j.succ (congrArg Subtype.val h))
      (fun i j h => Fin.succ_injective _ (ha (congrArg Subtype.val h)))
      (fun i j h => Fin.succ_injective _ (hb (congrArg Subtype.val h)))
      (by omega) (by omega)
    -- the paths in `G`
    let φ : G.induce s →g G := (Embedding.induce s).toHom
    have hφ : Function.Injective φ := Subtype.val_injective
    let P0 : G.Walk (a 0) (b 0) := Walk.cons hac (Walk.cons hcb Walk.nil)
    let P : ∀ i : Fin (t + 2), G.Walk (a i) (b i) :=
      Fin.cases (motive := fun i => G.Walk (a i) (b i)) P0 fun i => ((P' i).map φ).copy rfl rfl
    have hPz : P 0 = P0 := rfl
    have hPsucc : ∀ i : Fin (t + 1), P i.succ = ((P' i).map φ).copy rfl rfl := fun i => rfl
    have hP0 : ∀ v, v ∈ P0.support ↔ v = a 0 ∨ v = c ∨ v = b 0 := by
      intro v; simp [P0]
    have hPs : ∀ (i : Fin (t + 1)) v, v ∈ (P i.succ).support ↔ ∃ w ∈ (P' i).support, w.1 = v := by
      intro i v
      have e : (P i.succ).support = (P' i).support.map φ :=
        (Walk.support_copy ((P' i).map φ) rfl rfl).trans (Walk.support_map φ (P' i))
      rw [e, List.mem_map]
      rfl
    refine ⟨P, fun i => ?_, fun i j hij v hvi hvj => ?_, fun v => ?_⟩
    · induction i using Fin.cases with
      | zero =>
        rw [hPz]
        simp only [P0]
        rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff]
        simp [Ne.symm (hca 0), hab 0 0, hcb' 0]
      | succ i =>
        exact (Walk.isPath_copy ((P' i).map φ) rfl rfl).2 (Walk.map_isPath_of_injective hφ (hP'p i))
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact hij rfl
        | succ j =>
          obtain ⟨w, -, rfl⟩ := (hPs j v).1 hvj
          rcases (hP0 _).1 (by rw [← hPz]; exact hvi) with h | h | h
          · exact w.2.1 h
          · exact w.2.2.2 h
          · exact w.2.2.1 h
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          obtain ⟨w, -, rfl⟩ := (hPs i v).1 hvi
          rcases (hP0 _).1 (by rw [← hPz]; exact hvj) with h | h | h
          · exact w.2.1 h
          · exact w.2.2.2 h
          · exact w.2.2.1 h
        | succ j =>
          obtain ⟨w, hw, rfl⟩ := (hPs i v).1 hvi
          obtain ⟨w', hw', hww⟩ := (hPs j w.1).1 hvj
          have := Subtype.ext hww
          subst this
          exact hP'd i j (fun h => hij (by rw [h])) w' hw hw'
    · by_cases hv : v ∈ s
      · obtain ⟨i, hi⟩ := hP'c ⟨v, hv⟩
        exact ⟨i.succ, (hPs i v).2 ⟨⟨v, hv⟩, hi, rfl⟩⟩
      · refine ⟨0, ?_⟩
        have : v ∈ P0.support := by
          rw [hP0]
          simp only [s, Set.mem_setOf_eq, not_and_or, not_not] at hv
          tauto
        rw [hPz]; exact this

end PSLib
