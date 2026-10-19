import Gossip.Basic

/-!
Lower bound groundwork (milestones M1-M3 of the blueprint).

M1: F-points persist when more calls are appended.
M2: swapping two adjacent calls that share no node changes nothing.
M3: partition lemma. If the calls satisfying P never share a node with the
    calls not satisfying P, the list is equivalent to "non-P calls, then
    P calls", keeping order inside each group.
-/

namespace Gossip

variable {n : Nat}

/-! M1: F-points -/

def IsF (l : List (Fin n × Fin n)) (x : Fin n) : Prop :=
  run (init n) l x = Finset.univ

lemma isF_append {l : List (Fin n × Fin n)} {x : Fin n} (h : IsF l x)
    (l' : List (Fin n × Fin n)) : IsF (l ++ l') x := by
  unfold IsF at *
  rw [run_append]
  have hm := run_mono (run (init n) l) l' x
  rw [h] at hm
  exact Finset.univ_subset_iff.mp hm

/-! M2: swapping disjoint calls -/

def Disj (p q : Fin n × Fin n) : Prop :=
  p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

lemma Disj.symm {p q : Fin n × Fin n} (h : Disj p q) : Disj q p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨Ne.symm h1, Ne.symm h3, Ne.symm h2, Ne.symm h4⟩

lemma call_of_ne (s : State n) (p : Fin n × Fin n) (k : Fin n)
    (h1 : k ≠ p.1) (h2 : k ≠ p.2) : call s p k = s k := by
  simp only [call]
  split_ifs with hc
  · rcases hc with hc | hc <;> contradiction
  · rfl

lemma call_of_mem (s : State n) (p : Fin n × Fin n) (k : Fin n)
    (h : k = p.1 ∨ k = p.2) : call s p k = s p.1 ∪ s p.2 := by
  simp [call, h]

lemma call_swap (s : State n) (p q : Fin n × Fin n) (h : Disj p q) :
    call (call s p) q = call (call s q) p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  -- what each call sees of the other's endpoints: nothing changed
  have hq1 : call s p q.1 = s q.1 := call_of_ne s p q.1 (Ne.symm h1) (Ne.symm h3)
  have hq2 : call s p q.2 = s q.2 := call_of_ne s p q.2 (Ne.symm h2) (Ne.symm h4)
  have hp1 : call s q p.1 = s p.1 := call_of_ne s q p.1 h1 h2
  have hp2 : call s q p.2 = s p.2 := call_of_ne s q p.2 h3 h4
  funext k
  by_cases hk : k = p.1 ∨ k = p.2
  · have hkq1 : k ≠ q.1 := by rcases hk with rfl | rfl <;> assumption
    have hkq2 : k ≠ q.2 := by rcases hk with rfl | rfl <;> assumption
    rw [call_of_ne (call s p) q k hkq1 hkq2, call_of_mem s p k hk,
      call_of_mem (call s q) p k hk, hp1, hp2]
  · have hkp1 : k ≠ p.1 := fun e => hk (Or.inl e)
    have hkp2 : k ≠ p.2 := fun e => hk (Or.inr e)
    by_cases hk' : k = q.1 ∨ k = q.2
    · rw [call_of_mem (call s p) q k hk', hq1, hq2,
        call_of_ne (call s q) p k hkp1 hkp2, call_of_mem s q k hk']
    · have hkq1 : k ≠ q.1 := fun e => hk' (Or.inl e)
      have hkq2 : k ≠ q.2 := fun e => hk' (Or.inr e)
      rw [call_of_ne (call s p) q k hkq1 hkq2, call_of_ne s p k hkp1 hkp2,
        call_of_ne (call s q) p k hkp1 hkp2, call_of_ne s q k hkq1 hkq2]

/-- One swap of two adjacent disjoint calls. -/
inductive Swap : List (Fin n × Fin n) → List (Fin n × Fin n) → Prop
  | mk (l₁ l₂ : List (Fin n × Fin n)) (p q : Fin n × Fin n) (h : Disj p q) :
      Swap (l₁ ++ p :: q :: l₂) (l₁ ++ q :: p :: l₂)

/-- Equivalent call lists: related by any number of disjoint swaps. -/
abbrev CallEquiv : List (Fin n × Fin n) → List (Fin n × Fin n) → Prop :=
  Relation.ReflTransGen Swap

lemma run_swap {l l' : List (Fin n × Fin n)} (h : Swap l l') (s : State n) :
    run s l = run s l' := by
  cases h with
  | mk l₁ l₂ p q hd =>
    rw [run_append, run_append]
    change run (call (call (run s l₁) p) q) l₂ = run (call (call (run s l₁) q) p) l₂
    rw [call_swap _ _ _ hd]

lemma run_equiv {l l' : List (Fin n × Fin n)} (h : CallEquiv l l') (s : State n) :
    run s l = run s l' := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, run_swap hs]

lemma isF_equiv {l l' : List (Fin n × Fin n)} (h : CallEquiv l l') (x : Fin n) :
    IsF l x ↔ IsF l' x := by
  unfold IsF
  rw [run_equiv h]

/-! Congruence: swaps survive adding calls on either side -/

lemma Swap.append_left (a : List (Fin n × Fin n)) {l l' : List (Fin n × Fin n)}
    (h : Swap l l') : Swap (a ++ l) (a ++ l') := by
  cases h with
  | mk l₁ l₂ p q hd =>
    have := Swap.mk (a ++ l₁) l₂ p q hd
    simpa [List.append_assoc] using this

lemma Swap.append_right (b : List (Fin n × Fin n)) {l l' : List (Fin n × Fin n)}
    (h : Swap l l') : Swap (l ++ b) (l' ++ b) := by
  cases h with
  | mk l₁ l₂ p q hd =>
    have := Swap.mk l₁ (l₂ ++ b) p q hd
    simpa [List.append_assoc] using this

lemma CallEquiv.append_left (a : List (Fin n × Fin n)) {l l' : List (Fin n × Fin n)}
    (h : CallEquiv l l') : CallEquiv (a ++ l) (a ++ l') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (Swap.append_left a hs)

lemma CallEquiv.append_right (b : List (Fin n × Fin n)) {l l' : List (Fin n × Fin n)}
    (h : CallEquiv l l') : CallEquiv (l ++ b) (l' ++ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (Swap.append_right b hs)

lemma CallEquiv.cons (x : Fin n × Fin n) {l l' : List (Fin n × Fin n)}
    (h : CallEquiv l l') : CallEquiv (x :: l) (x :: l') :=
  CallEquiv.append_left [x] h

/-! M3: partition lemma -/

-- move one call past a block it shares no node with
lemma move_past (a : Fin n × Fin n) (A B : List (Fin n × Fin n))
    (h : ∀ x ∈ A, Disj a x) : CallEquiv (a :: (A ++ B)) (A ++ a :: B) := by
  induction A with
  | nil => exact Relation.ReflTransGen.refl
  | cons x A ih =>
    have hx : Disj a x := h x (by simp)
    have hA : ∀ y ∈ A, Disj a y := fun y hy => h y (by simp [hy])
    have step : Swap (a :: x :: (A ++ B)) (x :: a :: (A ++ B)) :=
      Swap.mk [] (A ++ B) a x hx
    exact Relation.ReflTransGen.head step (CallEquiv.cons x (ih hA))

theorem partition (P : Fin n × Fin n → Bool) (l : List (Fin n × Fin n))
    (hD : ∀ p ∈ l, ∀ q ∈ l, P p = true → P q = false → Disj p q) :
    CallEquiv l (l.filter (fun x => !P x) ++ l.filter P) := by
  induction l with
  | nil => exact Relation.ReflTransGen.refl
  | cons a l ih =>
    have hD' : ∀ p ∈ l, ∀ q ∈ l, P p = true → P q = false → Disj p q :=
      fun p hp q hq => hD p (by simp [hp]) q (by simp [hq])
    have e := CallEquiv.cons a (ih hD')
    cases ha : P a
    · -- a stays in the front group
      simp [ha]
      exact e
    · -- a moves past the non-P calls
      simp [ha]
      refine e.trans (move_past a _ _ ?_)
      intro x hx
      simp only [List.mem_filter, Bool.not_eq_true'] at hx
      exact hD a (by simp) x (by simp [hx.1]) ha hx.2

end Gossip

#min_imports
