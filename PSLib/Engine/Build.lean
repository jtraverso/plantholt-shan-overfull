/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PSLib.Engine.Init
public import LeanPool.Vizing.Corollaries

/-!
# Step 1 for a simple graph

* `exists_equalized_sides`: a proper colouring of the inner edges of an edge family can be equalized
  on each side separately (McDiarmid on each side).
* The edge family of a simple graph `G`: `GE G` (the edges of `G`) with `gends G e` the two ends;
  inner and crossing degrees are the numbers of neighbours on the same and on the other side.
* `exists_inner_colouring`: Vizing's theorem colours the inner edges with `k ≥ Δ(G_A ∪ G_B) + 1`
  colours.
-/

set_option linter.unusedSectionVars false

@[expose] public section

namespace PSLib.Eng

open Finset ShannonColouring

variable {V : Type*} [Fintype V] [DecidableEq V]

section General

variable {E : Type*} [Fintype E] [DecidableEq E] {ends : E → V × V} {A : Finset V} {k : ℕ}

/-- **Equalizing each side.** -/
theorem exists_equalized_sides (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (c0 : E → Fin k)
    (h0 : ProperOn ends (univ.filter fun e => Inner ends A e) c0) :
    ∃ c1 : E → Fin k, ProperOn ends (univ.filter fun e => Inner ends A e) c1 ∧
      (∀ a b, cls (innerSide ends A A) c1 a ≤ cls (innerSide ends A A) c1 b + 1) ∧
      (∀ a b, cls (innerSide ends A Aᶜ) c1 a ≤ cls (innerSide ends A Aᶜ) c1 b + 1) := by
  classical
  have hsubA : innerSide ends A A ⊆ univ.filter fun e => Inner ends A e :=
    fun e he => mem_filter.2 ⟨mem_univ _, (mem_filter.1 he).2.1⟩
  have hsubB : innerSide ends A Aᶜ ⊆ univ.filter fun e => Inner ends A e :=
    fun e he => mem_filter.2 ⟨mem_univ _, (mem_filter.1 he).2.1⟩
  obtain ⟨cA, hcA, heA⟩ := exists_equalized hloop (innerSide ends A A)
    (energy (innerSide ends A A) c0) c0 rfl (h0.mono hsubA)
  obtain ⟨cB, hcB, heB⟩ := exists_equalized hloop (innerSide ends A Aᶜ)
    (energy (innerSide ends A Aᶜ) c0) c0 rfl (h0.mono hsubB)
  let c1 : E → Fin k := fun e => if (ends e).1 ∈ A then cA e else cB e
  have hclsA : ∀ j, cls (innerSide ends A A) c1 j = cls (innerSide ends A A) cA j := by
    intro j; unfold cls; congr 1
    refine filter_congr fun e he => ?_
    simp [c1, (mem_filter.1 he).2.2]
  have hclsB : ∀ j, cls (innerSide ends A Aᶜ) c1 j = cls (innerSide ends A Aᶜ) cB j := by
    intro j; unfold cls; congr 1
    refine filter_congr fun e he => ?_
    have : (ends e).1 ∉ A := by have := (mem_filter.1 he).2.2; rwa [mem_compl] at this
    simp [c1, this]
  refine ⟨c1, ?_, fun a b => by rw [hclsA, hclsA]; exact heA a b,
    fun a b => by rw [hclsB, hclsB]; exact heB a b⟩
  intro e he f hf hef ⟨v, hev, hfv⟩
  have hei := (mem_filter.1 he).2
  have hfi := (mem_filter.1 hf).2
  have hside := same_side_of_share hei hfi hev hfv
  by_cases heA : (ends e).1 ∈ A
  · have hfA := hside.1 heA
    simp only [c1, if_pos heA, if_pos hfA]
    exact hcA e (mem_filter.2 ⟨mem_univ _, hei, heA⟩) f (mem_filter.2 ⟨mem_univ _, hfi, hfA⟩) hef
      ⟨v, hev, hfv⟩
  · have hfA : (ends f).1 ∉ A := fun h => heA (hside.2 h)
    simp only [c1, if_neg heA, if_neg hfA]
    exact hcB e (mem_filter.2 ⟨mem_univ _, hei, mem_compl.2 heA⟩) f
      (mem_filter.2 ⟨mem_univ _, hfi, mem_compl.2 hfA⟩) hef ⟨v, hev, hfv⟩

end General

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)

/-- The edges of `G`. -/
abbrev GE := {e : Sym2 V // e ∈ G.edgeFinset}

/-- The two ends of an edge. -/
noncomputable def gends (e : GE G) : V × V := Quot.out e.1

variable {G A}

theorem mk_gends (e : GE G) : s((gends G e).1, (gends G e).2) = e.1 := Quot.out_eq e.1

theorem gends_incident_iff (e : GE G) (v : V) : Incident (gends G) e v ↔ v ∈ e.1 := by
  rw [← mk_gends e]
  unfold Incident
  rw [Sym2.mem_iff]
  constructor <;> rintro (h | h) <;> first | exact Or.inl h.symm | exact Or.inr h.symm

theorem gends_adj (e : GE G) : G.Adj (gends G e).1 (gends G e).2 := by
  have := e.2
  rw [SimpleGraph.mem_edgeFinset, ← mk_gends e] at this
  exact this

theorem gends_loop (e : GE G) : (gends G e).1 ≠ (gends G e).2 := (gends_adj e).ne

theorem gends_eq_of {e : GE G} {u w : V} (hu : Incident (gends G) e u)
    (hw : Incident (gends G) e w) (huw : u ≠ w) : e.1 = s(u, w) := by
  rw [gends_incident_iff] at hu hw
  exact Sym2.eq_of_ne_mem huw hu hw (Sym2.mem_mk_left u w) (Sym2.mem_mk_right u w)

theorem gends_xsimple : XSimple (gends G) A := by
  intro e f _ _ u w huw heu hew hfu hfw
  exact Subtype.ext ((gends_eq_of heu hew huw).trans (gends_eq_of hfu hfw huw).symm)

theorem gends_inner_iff {e : GE G} {u w : V} (he : e.1 = s(u, w)) :
    Inner (gends G) A e ↔ (u ∈ A ↔ w ∈ A) := by
  have h := mk_gends e
  rw [he] at h
  unfold Inner
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; tauto

/-- Edges at `v` with a property of the other end correspond to neighbours. -/
theorem card_edges_at (v : V) (P : V → Prop) [DecidablePred P] :
    #(univ.filter fun e : GE G => Incident (gends G) e v ∧
      P (if (gends G e).1 = v then (gends G e).2 else (gends G e).1)) =
      #(univ.filter fun u => G.Adj v u ∧ P u) := by
  classical
  refine card_bij (fun e _ => if (gends G e).1 = v then (gends G e).2 else (gends G e).1)
    ?_ ?_ ?_
  · intro e he
    obtain ⟨hev, hP⟩ := (mem_filter.1 he).2
    refine mem_filter.2 ⟨mem_univ _, ?_, hP⟩
    have hadj := gends_adj e
    unfold Incident at hev
    split_ifs with h
    · rw [← h]; exact hadj
    · have h2 : (gends G e).2 = v := hev.resolve_left h
      rw [← h2]; exact hadj.symm
  · intro e he f hf hef
    obtain ⟨hev, -⟩ := (mem_filter.1 he).2
    obtain ⟨hfv, -⟩ := (mem_filter.1 hf).2
    set u := if (gends G e).1 = v then (gends G e).2 else (gends G e).1
    have heu : Incident (gends G) e u := by
      simp only [u]; split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]
    have hfu : Incident (gends G) f u := by
      rw [hef]; split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]
    have hvu : v ≠ u := by
      simp only [u]
      split_ifs with h
      · rw [← h]; exact gends_loop e
      · exact fun h' => h h'.symm
    exact Subtype.ext ((gends_eq_of hev heu hvu).trans (gends_eq_of hfv hfu hvu).symm)
  · intro u hu
    obtain ⟨hadj, hP⟩ := (mem_filter.1 hu).2
    let e : GE G := ⟨s(v, u), by rw [SimpleGraph.mem_edgeFinset]; exact hadj⟩
    have hev : Incident (gends G) e v := (gends_incident_iff e v).2 (Sym2.mem_mk_left v u)
    have heu : Incident (gends G) e u := (gends_incident_iff e u).2 (Sym2.mem_mk_right v u)
    have hoth : (if (gends G e).1 = v then (gends G e).2 else (gends G e).1) = u := by
      unfold Incident at hev heu
      split_ifs with h
      · rcases heu with h' | h'
        · exact absurd (h.symm.trans h') hadj.ne
        · exact h'
      · rcases hev with h' | h'
        · exact absurd h' h
        · rcases heu with h'' | h''
          · exact h''
          · exact absurd (h'.symm.trans h'') hadj.ne
    exact ⟨e, mem_filter.2 ⟨mem_univ _, hev, hoth ▸ hP⟩, hoth⟩

theorem din_eq (v : V) :
    din (gends G) A v = #(univ.filter fun u => G.Adj v u ∧ (v ∈ A ↔ u ∈ A)) := by
  classical
  rw [← card_edges_at v (fun u => (v ∈ A ↔ u ∈ A))]
  unfold din
  congr 1; ext e
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hi, hv⟩
    refine ⟨hv, ?_⟩
    unfold Inner at hi; unfold Incident at hv
    split_ifs with h
    · rw [← h]; exact hi
    · rw [← hv.resolve_left h]; exact hi.symm
  · rintro ⟨hv, hi⟩
    refine ⟨?_, hv⟩
    unfold Inner; unfold Incident at hv
    split_ifs at hi with h
    · rw [h]; exact hi
    · rw [hv.resolve_left h]; exact hi.symm

theorem dx_eq (v : V) :
    dx (gends G) A v = #(univ.filter fun u => G.Adj v u ∧ ¬ (v ∈ A ↔ u ∈ A)) := by
  classical
  rw [← card_edges_at v (fun u => ¬ (v ∈ A ↔ u ∈ A))]
  unfold dx
  congr 1; ext e
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hi, hv⟩
    refine ⟨hv, ?_⟩
    unfold Inner at hi; unfold Incident at hv
    split_ifs with h
    · rw [← h]; exact hi
    · rw [← hv.resolve_left h]; exact fun h' => hi h'.symm
  · rintro ⟨hv, hi⟩
    refine ⟨?_, hv⟩
    unfold Inner; unfold Incident at hv
    split_ifs at hi with h
    · rw [h]; exact hi
    · rw [hv.resolve_left h]; exact fun h' => hi h'.symm

theorem dx_add_din (v : V) : dx (gends G) A v + din (gends G) A v = G.degree v := by
  classical
  rw [dx_eq, din_eq, ← card_union_of_disjoint]
  · rw [← G.card_neighborFinset_eq_degree]
    congr 1; ext u; simp only [mem_union, mem_filter, mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]; tauto
  · rw [disjoint_filter]; intro u _ h1 h2; exact h1.2 h2.2

variable (G A) in
/-- The graph of inner edges `G_A ∪ G_B`. -/
def innerGraph : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∈ A ↔ v ∈ A)
  symm := ⟨fun u v h => ⟨G.symm.symm u v h.1, h.2.symm⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

instance : DecidableRel (innerGraph G A).Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u v ∧ (u ∈ A ↔ v ∈ A)))

theorem innerGraph_degree (v : V) : (innerGraph G A).degree v = din (gends G) A v := by
  rw [din_eq, ← (innerGraph G A).card_neighborFinset_eq_degree]
  congr 1; ext u
  simp only [SimpleGraph.mem_neighborFinset, mem_filter, mem_univ, true_and]
  rfl

/-- **Vizing on the inner edges.** -/
theorem exists_inner_colouring {k : ℕ} (hk : (innerGraph G A).maxDegree + 1 ≤ k) :
    ∃ c0 : GE G → Fin k,
      ProperOn (gends G) (univ.filter fun e => Inner (gends G) A e) c0 := by
  classical
  obtain ⟨colour, hprop, -⟩ := LeanPool.Vizing.exists_equitable_edge_colouring (innerGraph G A) k hk
  refine ⟨fun e => colour e.1, ?_⟩
  intro e he f hf hef ⟨v, hev, hfv⟩ hc
  have hmem : ∀ g : GE G, Inner (gends G) A g → g.1 ∈ (innerGraph G A).edgeFinset := by
    intro g hg
    rw [SimpleGraph.mem_edgeFinset, ← mk_gends g]
    exact ⟨gends_adj g, hg⟩
  have := hprop e.1 (hmem e (mem_filter.1 he).2) f.1 (hmem f (mem_filter.1 hf).2)
    (fun h => hef (Subtype.ext h)) hc
  rw [gends_incident_iff] at hev hfv
  exact Finset.disjoint_left.1 this (Sym2.mem_toFinset.2 hev) (Sym2.mem_toFinset.2 hfv)

end Graph

end PSLib.Eng
