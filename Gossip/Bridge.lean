import Gossip.Flow

/-!
Component bridge (M5, component version).

If every node of S can be reached from z using only the calls of l, then
S has at most l.length + 1 nodes.

Proof: S sits inside the connected component C of z. C is connected, so
Mathlib gives |C| <= edges(C) + 1. The edges of C inject into the edges of
the whole call graph, and those are at most l.length.
-/

namespace Gossip

variable {n : Nat}

theorem card_le_of_reach (l : List (Fin n × Fin n)) (z : Fin n) (S : Finset (Fin n))
    (hS : ∀ y ∈ S, (callGraph l).Reachable z y) : S.card ≤ l.length + 1 := by
  classical
  set G := callGraph l with hG
  let C := G.connectedComponentMk z
  have h1 := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  -- S injects into the component of z
  have hmem : ∀ y, G.Reachable z y → y ∈ C.supp := by
    intro y hy
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact SimpleGraph.ConnectedComponent.eq.mpr hy.symm
  have hS' : S.card ≤ Nat.card C := by
    let f : S → C := fun y => ⟨y.1, hmem y.1 (hS y.1 y.2)⟩
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (congrArg (fun x : C => x.1) h)
    have := Nat.card_le_card_of_injective f hf
    simpa using this
  -- edges of the component inject into edges of the whole graph
  have hmap : ∀ e ∈ C.toSimpleGraph.edgeSet, Sym2.map Subtype.val e ∈ G.edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | h u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      change s(u.1, v.1) ∈ G.edgeSet
      rw [SimpleGraph.mem_edgeSet]
      exact he
  have hE : Nat.card C.toSimpleGraph.edgeSet ≤ Nat.card G.edgeSet := by
    let g : C.toSimpleGraph.edgeSet → G.edgeSet :=
      fun e => ⟨Sym2.map Subtype.val e.1, hmap e.1 e.2⟩
    have hg : Function.Injective g := fun a b h =>
      Subtype.ext (Sym2.map.injective Subtype.val_injective
        (congrArg (fun x : G.edgeSet => x.1) h))
    exact Nat.card_le_card_of_injective g hg
  have h2 : Nat.card G.edgeSet ≤ l.length := card_edgeSet_le l
  omega

end Gossip

#min_imports
