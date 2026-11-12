/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import MengerHamilton.Hamiltonian

/-!
# Hamilton-connectedness for large minimum degree

If `|V| = n ≥ 5` and `δ(G) ≥ n/2 + 1`, then any two distinct vertices `u`, `v` are the ends of a
Hamiltonian path. Proof: by Dirac's theorem (registered in `menger-hamiltonian`), `G − u − v` has
a Hamiltonian cycle `c₀ c₁ … c_{m−1}`; since `u` and `v` together have more than `m` neighbours on
it, some index `i` has `u ~ cᵢ` and `v ~ c_{i+1}`, and `u cᵢ c_{i−1} … c_{i+1} v` is the path.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib

open Finset SimpleGraph Hamiltonicity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Periodic functions: `f (a + m * k) = f a`. -/
theorem CycArr.periodic_mul {W : Type*} {H : SimpleGraph W} {m : ℕ} {f : ℕ → W}
    (hC : CycArr H m f) (a k : ℕ) : f (a + m * k) = f a := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, hC.periodic, ih]

/-- **Hamilton-connectedness** for `δ ≥ n/2 + 1`. -/
theorem exists_hamiltonian_path (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 5 ≤ Fintype.card V) (hdeg : Fintype.card V + 2 ≤ 2 * G.minDegree) {u v : V}
    (huv : u ≠ v) : ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  set s : Set V := {w | w ≠ u ∧ w ≠ v}
  set H : SimpleGraph s := G.induce s
  -- the size of `s`
  have hcard : Fintype.card s + 2 = Fintype.card V := by
    rw [Fintype.card_subtype, ← card_univ]
    have : (univ.filter fun w => w ∈ s) = (univ.erase u).erase v := by
      ext w; simp [s, and_comm]
    rw [this, card_erase_of_mem (by simp [Ne.symm huv]), card_erase_of_mem (mem_univ u)]
    have : 2 ≤ #(univ : Finset V) := by rw [card_univ]; omega
    omega
  -- minimum degree of `H`
  have hdegH : ∀ w : s, G.minDegree ≤ H.degree w + 2 := by
    intro w
    have h1 := G.minDegree_le_degree (w : V)
    have hsub : G.neighborFinset w ⊆ (H.neighborFinset w).map (Function.Embedding.subtype _) ∪
        {u, v} := by
      intro x hx
      rw [mem_neighborFinset] at hx
      by_cases hxs : x ∈ s
      · refine mem_union_left _ (mem_map.2 ⟨⟨x, hxs⟩, ?_, rfl⟩)
        rw [mem_neighborFinset]; exact hx
      · refine mem_union_right _ ?_
        simp only [s, Set.mem_setOf_eq, not_and_or, not_not] at hxs
        rcases hxs with rfl | rfl <;> simp
    have h2 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_map, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h2
    have : #({u, v} : Finset V) ≤ 2 := card_le_two
    omega
  have hHdeg : Fintype.card s ≤ 2 * H.minDegree := by
    have : G.minDegree ≤ H.minDegree + 2 := by
      obtain ⟨w, hw⟩ : ∃ w : s, H.minDegree = H.degree w := by
        have : Nonempty s := by
          rw [← Fintype.card_pos_iff]; omega
        exact H.exists_minimal_degree_vertex.imp fun w hw => hw
      rw [hw]; exact hdegH w
    omega
  have hHam := dirac H (by omega) hHdeg
  obtain ⟨f, hf⟩ := exists_cycArr_of_isHamiltonian hHam (by omega)
  set m := Fintype.card s with hm
  have hm3 : 3 ≤ m := by omega
  -- `f` is a bijection from `[0, m)` onto `s`
  have hsurj : ∀ w : s, ∃ k < m, f k = w := by
    intro w
    have himg : (range m).image f = univ := by
      apply eq_univ_of_card
      rw [card_image_of_injOn fun a ha b hb h => hf.inj a b (mem_range.1 ha) (mem_range.1 hb) h,
        card_range]
    have : w ∈ (range m).image f := by rw [himg]; exact mem_univ w
    obtain ⟨k, hk, rfl⟩ := mem_image.1 this
    exact ⟨k, mem_range.1 hk, rfl⟩
  -- neighbours on the cycle
  set X := (range m).filter fun i => G.Adj u (f i)
  set Y := (range m).filter fun i => G.Adj v (f (i + 1))
  have hX : G.minDegree ≤ #X + 1 := by
    have h1 := G.minDegree_le_degree u
    rw [← card_neighborFinset_eq_degree] at h1
    have hsub : G.neighborFinset u ⊆ X.image (fun i => (f i : V)) ∪ {v} := by
      intro x hx
      rw [mem_neighborFinset] at hx
      by_cases hxv : x = v
      · exact mem_union_right _ (by simp [hxv])
      · have hxs : x ∈ s := ⟨fun h => hx.ne h.symm, hxv⟩
        obtain ⟨k, hk, hfk⟩ := hsurj ⟨x, hxs⟩
        refine mem_union_left _ (mem_image.2 ⟨k, mem_filter.2 ⟨mem_range.2 hk, ?_⟩, ?_⟩)
        · rw [hfk]; exact hx
        · rw [hfk]
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_singleton] at this
    have := card_image_le (s := X) (f := fun i => (f i : V))
    omega
  have hY : G.minDegree ≤ #Y + 1 := by
    have h1 := G.minDegree_le_degree v
    rw [← card_neighborFinset_eq_degree] at h1
    have hsub : G.neighborFinset v ⊆ Y.image (fun i => (f (i + 1) : V)) ∪ {u} := by
      intro x hx
      rw [mem_neighborFinset] at hx
      by_cases hxu : x = u
      · exact mem_union_right _ (by simp [hxu])
      · have hxs : x ∈ s := ⟨hxu, fun h => hx.ne h.symm⟩
        obtain ⟨k, hk, hfk⟩ := hsurj ⟨x, hxs⟩
        -- `x = f k = f ((k + m - 1) + 1)`
        have hk' : f (k + m - 1 + 1) = f k := by
          rw [show k + m - 1 + 1 = k + m by omega, hf.periodic]
        refine mem_union_left _ (mem_image.2 ⟨(k + m - 1) % m,
          mem_filter.2 ⟨mem_range.2 (Nat.mod_lt _ (by omega)), ?_⟩, ?_⟩)
        · have : f ((k + m - 1) % m + 1) = f k := by
            rw [← hk', hf.eq_iff]
            simp [Nat.add_mod, Nat.mod_mod]
          rw [this, hfk]; exact hx
        · have : f ((k + m - 1) % m + 1) = f k := by
            rw [← hk', hf.eq_iff]
            simp [Nat.add_mod, Nat.mod_mod]
          rw [this, hfk]
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_singleton] at this
    have := card_image_le (s := Y) (f := fun i => (f (i + 1) : V))
    omega
  obtain ⟨i, hiX, hiY⟩ : ∃ i, i ∈ X ∧ i ∈ Y := by
    by_contra h
    push Not at h
    have hdisj : Disjoint X Y := Finset.disjoint_left.2 fun i hi hi' => h i hi hi'
    have hXs : X ⊆ range m := filter_subset _ _
    have hYs : Y ⊆ range m := filter_subset _ _
    have := card_le_card (union_subset hXs hYs)
    rw [card_union_of_disjoint hdisj, card_range] at this
    omega
  rw [mem_filter] at hiX hiY
  -- the reversed arc
  set g : ℕ → V := fun j => (f (i + (m - 1) * j) : V)
  have hg : ∀ j, G.Adj (g j) (g (j + 1)) := by
    intro j
    simp only [g]
    have e : i + (m - 1) * (j + 1) + 1 = i + (m - 1) * j + m := by
      rw [Nat.mul_succ]; omega
    have hadj := hf.adj (i + (m - 1) * (j + 1))
    rw [e, hf.periodic] at hadj
    exact (H.adj_comm _ _).1 hadj
  have hg0 : g 0 = f i := by simp [g]
  have hgm : g (m - 1) = f (i + 1) := by
    simp only [g]
    congr 1
    have : i + (m - 1) * (m - 1) = (i + 1) + m * (m - 2) := by
      have h1 : (m - 1) * (m - 1) = m * (m - 2) + 1 := by
        zify [show 1 ≤ m by omega, show 2 ≤ m by omega]
        ring
      omega
    rw [this, CycArr.periodic_mul hf]
  set q := (Hamiltonicity.walkOf G g hg (m - 1)).copy hg0 hgm
  set p : G.Walk u v := (Walk.cons hiX.2 q).concat ((G.adj_comm _ _).1 hiY.2)
  -- `p` is a path
  have hsupp : p.support = u :: ((List.range m).map g ++ [v]) := by
    simp only [p, q, Walk.support_concat, Walk.support_cons, Walk.support_copy,
      Hamiltonicity.support_walkOf, show m - 1 + 1 = m by omega, List.concat_eq_append,
      List.cons_append]
  have hginj : ∀ j < m, ∀ j' < m, g j = g j' → j = j' := by
    intro j hj j' hj' h
    simp only [g] at h
    have h' := Subtype.ext h
    rw [hf.eq_iff] at h'
    -- `i + (m−1) j + j ≡ i`
    have e1 : (i + (m - 1) * j + j) % m = i % m := by
      rw [show i + (m - 1) * j + j = i + m * j by
        rw [show m * j = (m - 1) * j + j by
          zify [show 1 ≤ m by omega]; ring]; omega]
      simp
    have e2 : (i + (m - 1) * j' + j') % m = i % m := by
      rw [show i + (m - 1) * j' + j' = i + m * j' by
        rw [show m * j' = (m - 1) * j' + j' by
          zify [show 1 ≤ m by omega]; ring]; omega]
      simp
    have : j % m = j' % m := by
      have h1 : (i + (m - 1) * j + j) % m = (i + (m - 1) * j + j') % m := by
        rw [e1, Nat.add_mod, h', ← Nat.add_mod, e2]
      exact Nat.ModEq.add_left_cancel' _ h1
    rwa [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at this
  have hgs : ∀ j, g j ≠ u ∧ g j ≠ v := fun j => (f (i + (m - 1) * j)).2
  have hpath : p.IsPath := by
    rw [Walk.isPath_def, hsupp]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · simp only [List.mem_append, List.mem_map, List.mem_range, List.mem_singleton, not_or]
      exact ⟨fun ⟨j, _, hj⟩ => (hgs j).1 hj, huv⟩
    · refine List.Nodup.append ?_ (List.nodup_singleton v) ?_
      · exact List.Nodup.map_on (fun a ha b hb h => hginj a (List.mem_range.1 ha) b
          (List.mem_range.1 hb) h) List.nodup_range
      · simp only [List.disjoint_singleton, List.mem_map, List.mem_range, not_exists, not_and]
        exact fun j _ hj => (hgs j).2 hj
  refine ⟨p, hpath.isHamiltonian_of_mem fun w => ?_⟩
  have hlen : p.support.length = Fintype.card V := by
    rw [hsupp]; simp; omega
  have hcardsupp : p.support.toFinset.card = Fintype.card V := by
    rw [List.toFinset_card_of_nodup (Walk.isPath_def _ |>.1 hpath), hlen]
  have huniv : p.support.toFinset = univ := eq_univ_of_card _ hcardsupp
  have : w ∈ p.support.toFinset := huniv ▸ mem_univ w
  simpa using this

end PSLib
