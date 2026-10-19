import Mathlib

/-!
Gossip problem, upper bound: 2n - 4 calls suffice for n >= 4 nodes.

State: each node holds a set of secrets (identified by the node they came from).
A call between p.1 and p.2 gives both of them the union of what they know.
-/

namespace Gossip

abbrev State (n : Nat) := Fin n → Finset (Fin n)

def init (n : Nat) : State n := fun i => {i}

def call {n : Nat} (s : State n) (p : Fin n × Fin n) : State n :=
  fun k => if k = p.1 ∨ k = p.2 then s p.1 ∪ s p.2 else s k

def run {n : Nat} : State n → List (Fin n × Fin n) → State n
  | s, [] => s
  | s, p :: l => run (call s p) l

/-! Basic facts about calls and runs -/

lemma call_mono {n : Nat} (s : State n) (p : Fin n × Fin n) (k : Fin n) :
    s k ⊆ call s p k := by
  unfold call
  split_ifs with h
  · rcases h with h | h <;> subst h
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exact le_rfl

lemma run_mono {n : Nat} (s : State n) (l : List (Fin n × Fin n)) (k : Fin n) :
    s k ⊆ run s l k := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons p l ih => exact (call_mono s p k).trans (ih (call s p))

lemma run_append {n : Nat} (s : State n) (l₁ l₂ : List (Fin n × Fin n)) :
    run s (l₁ ++ l₂) = run (run s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons p l ih => exact ih (call s p)

lemma call_fst {n : Nat} (s : State n) (a j : Fin n) :
    call s (a, j) a = s a ∪ s j := by
  simp [call]

lemma call_snd {n : Nat} (s : State n) (a j : Fin n) :
    call s (a, j) j = s a ∪ s j := by
  simp [call]

/-
Node a calls every node in L, in order. Afterwards a has everything the
L nodes started with, and every L node has everything a started with.
-/
lemma star {n : Nat} (s : State n) (a : Fin n) (L : List (Fin n)) :
    ∀ j ∈ L, s j ⊆ run s (L.map (a, ·)) a ∧ s a ⊆ run s (L.map (a, ·)) j := by
  induction L generalizing s with
  | nil => simp
  | cons j L ih =>
    intro j' hj'
    simp only [List.map_cons, run]
    rcases List.mem_cons.mp hj' with h | h
    · subst h
      constructor
      · calc s j' ⊆ call s (a, j') a := by rw [call_fst]; exact Finset.subset_union_right
          _ ⊆ _ := run_mono _ _ _
      · calc s a ⊆ call s (a, j') j' := by rw [call_snd]; exact Finset.subset_union_left
          _ ⊆ _ := run_mono _ _ _
    · obtain ⟨h1, h2⟩ := ih (call s (a, j)) j' h
      exact ⟨(call_mono s _ j').trans h1, (call_mono s _ a).trans h2⟩

/-
The four-call protocol on distinct a b c d: everyone in the core ends up
with everything the core knew collectively.
-/
lemma core_spreads {n : Nat} (s : State n) (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∀ x ∈ ({a, b, c, d} : Finset (Fin n)),
      s a ∪ s b ∪ s c ∪ s d ⊆ run s [(a, b), (c, d), (a, c), (b, d)] x := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
  · intro y hy
    simp only [Finset.mem_union] at hy
    simp [run, call, hab, hac, had, hbc, hbd, hcd,
      hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm]
    tauto

/-! The protocol on n + 4 nodes -/

def na (n : Nat) : Fin (n + 4) := ⟨0, by omega⟩
def nb (n : Nat) : Fin (n + 4) := ⟨1, by omega⟩
def nc (n : Nat) : Fin (n + 4) := ⟨2, by omega⟩
def nd (n : Nat) : Fin (n + 4) := ⟨3, by omega⟩

-- the outsiders: nodes 4, 5, ..., n + 3
def outsiders (n : Nat) : List (Fin (n + 4)) :=
  (List.finRange n).map (fun i => i.addNat 4)

def coreCalls (n : Nat) : List (Fin (n + 4) × Fin (n + 4)) :=
  [(na n, nb n), (nc n, nd n), (na n, nc n), (nb n, nd n)]

def proto (n : Nat) : List (Fin (n + 4) × Fin (n + 4)) :=
  (outsiders n).map (na n, ·) ++ coreCalls n ++ (outsiders n).map (na n, ·)

lemma mem_outsiders {n : Nat} (j : Fin (n + 4)) :
    j ∈ outsiders n ↔ 4 ≤ j.val := by
  simp only [outsiders, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro h
    exact ⟨⟨j.val - 4, by omega⟩, Fin.ext (by simp; omega)⟩

lemma proto_length (n : Nat) : (proto n).length = 2 * (n + 4) - 4 := by
  simp [proto, outsiders, coreCalls]
  omega

theorem proto_works (n : Nat) (k : Fin (n + 4)) :
    run (init (n + 4)) (proto n) k = Finset.univ := by
  rw [← Finset.univ_subset_iff]
  unfold proto
  rw [run_append, run_append]
  -- phase 1: na collects every outsider's secret
  set s1 := run (init (n + 4)) ((outsiders n).map (na n, ·)) with hs1
  have h1 : ∀ j, 4 ≤ j.val → j ∈ s1 (na n) := by
    intro j hj
    have := (star (init (n + 4)) (na n) (outsiders n) j ((mem_outsiders j).mpr hj)).1
    exact this (by simp [init])
  have hself : ∀ j, j ∈ s1 j := fun j => run_mono _ _ j (by simp [init])
  -- after phase 1, the core collectively knows everything
  have hU : Finset.univ ⊆ s1 (na n) ∪ s1 (nb n) ∪ s1 (nc n) ∪ s1 (nd n) := by
    intro j _
    simp only [Finset.mem_union]
    by_cases hj : 4 ≤ j.val
    · exact Or.inl (Or.inl (Or.inl (h1 j hj)))
    · have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
      rcases this with h | h | h | h
      · have e : j = na n := Fin.ext h
        subst e; exact Or.inl (Or.inl (Or.inl (hself _)))
      · have e : j = nb n := Fin.ext h
        subst e; exact Or.inl (Or.inl (Or.inr (hself _)))
      · have e : j = nc n := Fin.ext h
        subst e; exact Or.inl (Or.inr (hself _))
      · have e : j = nd n := Fin.ext h
        subst e; exact Or.inr (hself _)
  -- phase 2: the core spreads it among the four
  set s2 := run s1 (coreCalls n) with hs2
  have h2 : ∀ x ∈ ({na n, nb n, nc n, nd n} : Finset (Fin (n + 4))),
      Finset.univ ⊆ s2 x := by
    intro x hx
    refine hU.trans ?_
    exact core_spreads s1 _ _ _ _
      (by simp [na, nb]) (by simp [na, nc]) (by simp [na, nd])
      (by simp [nb, nc]) (by simp [nb, nd]) (by simp [nc, nd]) x hx
  -- phase 3: na hands everything to the outsiders
  by_cases hk : 4 ≤ k.val
  · have := (star s2 (na n) (outsiders n) k ((mem_outsiders k).mpr hk)).2
    exact (h2 (na n) (by simp)).trans this
  · have hcore : k ∈ ({na n, nb n, nc n, nd n} : Finset (Fin (n + 4))) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 := by omega
      rcases this with h | h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
    exact (h2 k hcore).trans (run_mono _ _ k)

/-- Main result: for n >= 4, some protocol with 2n - 4 calls informs everyone. -/
theorem upper_bound (n : Nat) (hn : 4 ≤ n) :
    ∃ p : List (Fin n × Fin n), p.length = 2 * n - 4 ∧
      ∀ k, run (init n) p k = Finset.univ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  exact ⟨proto m, proto_length m, proto_works m⟩

end Gossip

#min_imports
