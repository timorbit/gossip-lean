import Gossip.Lower

/-!
Milestones M4-M6 of the blueprint.

M4: if j's secret reaches node y, then j and y are connected in the call graph.
M5 (whole-graph version): the call graph has at most as many edges as calls.
M6: Lemma 1. A list with at most n - 2 calls has no F-points.

Lemma 1 only needs the whole call graph to be connected, so Mathlib's lemma
applies directly. The component version of M5 is needed later, for P(k).
-/

namespace Gossip

variable {n : Nat}

/-- Edge between the two parties of every call. Self-calls give no edge. -/
def callGraph (l : List (Fin n × Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ p ∈ l, e = s(p.1, p.2)}

lemma callGraph_mono {l l' : List (Fin n × Fin n)} (h : ∀ p ∈ l, p ∈ l') :
    callGraph l ≤ callGraph l' := by
  intro u v huv
  rw [callGraph, SimpleGraph.fromEdgeSet_adj] at huv ⊢
  obtain ⟨⟨p, hp, e⟩, hne⟩ := huv
  exact ⟨⟨p, h p hp, e⟩, hne⟩

lemma endpoints_reach (a b : Fin n) (l : List (Fin n × Fin n)) :
    (callGraph ((a, b) :: l)).Reachable a b := by
  by_cases h : a = b
  · subst h
    exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    rw [callGraph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨(a, b), by simp, rfl⟩, h⟩

/-! M4: information flow implies a path -/

theorem info_path (s : State n) (l : List (Fin n × Fin n)) (j y : Fin n)
    (h : j ∈ run s l y) : ∃ z, j ∈ s z ∧ (callGraph l).Reachable z y := by
  induction l generalizing s with
  | nil => exact ⟨y, h, SimpleGraph.Reachable.refl _⟩
  | cons p l ih =>
    obtain ⟨z, hz, hr⟩ := ih (call s p) h
    have hmono : callGraph l ≤ callGraph (p :: l) :=
      callGraph_mono (fun q hq => by simp [hq])
    have hr' := hr.mono hmono
    by_cases hzp : z = p.1 ∨ z = p.2
    · rw [call_of_mem s p z hzp, Finset.mem_union] at hz
      have e : (callGraph (p :: l)).Reachable p.1 p.2 := endpoints_reach p.1 p.2 l
      -- both endpoints of p can reach z inside the graph of p :: l
      have hpz : (callGraph (p :: l)).Reachable p.1 z ∧
          (callGraph (p :: l)).Reachable p.2 z := by
        rcases hzp with rfl | rfl
        · exact ⟨SimpleGraph.Reachable.refl _, e.symm⟩
        · exact ⟨e, SimpleGraph.Reachable.refl _⟩
      rcases hz with hz | hz
      · exact ⟨p.1, hz, hpz.1.trans hr'⟩
      · exact ⟨p.2, hz, hpz.2.trans hr'⟩
    · push Not at hzp
      rw [call_of_ne s p z hzp.1 hzp.2] at hz
      exact ⟨z, hz, hr'⟩

lemma reach_of_isF {l : List (Fin n × Fin n)} {x : Fin n} (h : IsF l x) (j : Fin n) :
    (callGraph l).Reachable j x := by
  have hj : j ∈ run (init n) l x := by
    unfold IsF at h
    rw [h]
    exact Finset.mem_univ j
  obtain ⟨z, hz, hr⟩ := info_path (init n) l j x hj
  simp [init] at hz
  subst hz
  exact hr

lemma connected_of_isF {l : List (Fin n × Fin n)} {x : Fin n} (h : IsF l x) :
    (callGraph l).Connected := by
  have : Nonempty (Fin n) := ⟨x⟩
  exact ⟨fun u v => (reach_of_isF h u).trans (reach_of_isF h v).symm⟩

/-! M5, whole-graph version: edges <= calls -/

lemma card_edgeSet_le (l : List (Fin n × Fin n)) :
    Nat.card (callGraph l).edgeSet ≤ l.length := by
  classical
  let S : Finset (Sym2 (Fin n)) := (l.map (fun p => s(p.1, p.2))).toFinset
  have hsub : (callGraph l).edgeSet ⊆ (S : Set (Sym2 (Fin n))) := by
    intro e he
    rw [callGraph, SimpleGraph.edgeSet_fromEdgeSet] at he
    obtain ⟨⟨p, hp, rfl⟩, _⟩ := he
    exact Finset.mem_coe.mpr (List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩))
  calc Nat.card (callGraph l).edgeSet
      = (callGraph l).edgeSet.ncard := Nat.card_coe_set_eq _
    _ ≤ (S : Set (Sym2 (Fin n))).ncard := Set.ncard_le_ncard hsub (Finset.finite_toSet S)
    _ = S.card := Set.ncard_coe_finset S
    _ ≤ (l.map (fun p => s(p.1, p.2))).length := List.toFinset_card_le _
    _ = l.length := by simp

/-! M6: Lemma 1 -/

theorem no_F_short {l : List (Fin n × Fin n)} (hl : l.length + 2 ≤ n) (x : Fin n) :
    ¬ IsF l x := by
  intro hF
  have h1 := (connected_of_isF hF).card_vert_le_card_edgeSet_add_one
  have h2 := card_edgeSet_le l
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  omega

end Gossip

#min_imports
