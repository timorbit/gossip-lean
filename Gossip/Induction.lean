import Gossip.Bridge
set_option profiler true
set_option profiler.threshold 2000
/-!
Skeleton of the full lower bound.

P(k): every list of n + k - 4 calls has at most k F-points, and if it has
exactly k, some equivalent list ends with k calls between F-points.

This file proves:
- part (a) of P(k), assuming P(j) for all j < k
- part (b) of P(k), assuming P(j) for all j < k (HMS steps 1-6)
- the main theorem from P(k) for all k
-/

namespace Gossip

variable {n : Nat}

instance decIsF (l : List (Fin n × Fin n)) : DecidablePred (IsF l) :=
  fun x => inferInstanceAs (Decidable (run (init n) l x = Finset.univ))

/-- The set of F-points of a list. -/
def Fset (l : List (Fin n × Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (IsF l)

lemma mem_Fset {l : List (Fin n × Fin n)} {x : Fin n} : x ∈ Fset l ↔ IsF l x := by
  simp [Fset]

/-- The last k calls of l are all between F-points. -/
def TailF (l : List (Fin n × Fin n)) (k : Nat) : Prop :=
  ∀ p ∈ l.drop (l.length - k), IsF l p.1 ∧ IsF l p.2

def P (n k : Nat) : Prop :=
  ∀ l : List (Fin n × Fin n), l.length + 4 = n + k →
    (Fset l).card ≤ k ∧ ((Fset l).card = k → ∃ l', CallEquiv l l' ∧ TailF l' k)

/-! Small facts about equivalence -/

lemma Swap.symm {l l' : List (Fin n × Fin n)} (h : Swap l l') : Swap l' l := by
  cases h with
  | mk l₁ l₂ p q hd => exact Swap.mk l₁ l₂ q p hd.symm

lemma CallEquiv.symm {l l' : List (Fin n × Fin n)} (h : CallEquiv l l') :
    CallEquiv l' l := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact Relation.ReflTransGen.head hs.symm ih

lemma Swap.length_eq {l l' : List (Fin n × Fin n)} (h : Swap l l') :
    l.length = l'.length := by
  cases h
  simp

lemma CallEquiv.length_eq {l l' : List (Fin n × Fin n)} (h : CallEquiv l l') :
    l.length = l'.length := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, hs.length_eq]

lemma Fset_equiv {l l' : List (Fin n × Fin n)} (h : CallEquiv l l') :
    Fset l = Fset l' := by
  ext x
  rw [mem_Fset, mem_Fset]
  exact isF_equiv h x

/-! Facts about F-points -/

-- calls that don't involve x leave x's knowledge alone
lemma run_untouched (s : State n) (l : List (Fin n × Fin n)) (x : Fin n)
    (h : ∀ p ∈ l, x ≠ p.1 ∧ x ≠ p.2) : run s l x = s x := by
  induction l generalizing s with
  | nil => rfl
  | cons p l ih =>
    have hp := h p (by simp)
    change run (call s p) l x = s x
    rw [ih (call s p) (fun q hq => h q (by simp [hq])), call_of_ne s p x hp.1 hp.2]

-- one extra call creates at most its two endpoints as new F-points
lemma Fset_concat_sub (l : List (Fin n × Fin n)) (c : Fin n × Fin n) :
    Fset (l ++ [c]) ⊆ insert c.1 (insert c.2 (Fset l)) := by
  intro x hx
  rw [mem_Fset] at hx
  by_cases h1 : x = c.1
  · simp [h1]
  by_cases h2 : x = c.2
  · simp [h2]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  rw [mem_Fset]
  unfold IsF at hx ⊢
  rw [run_append] at hx
  change call (run (init n) l) c x = _ at hx
  rwa [call_of_ne _ c x h1 h2] at hx

lemma Fset_card_short {l : List (Fin n × Fin n)} (hl : l.length + 2 ≤ n) :
    (Fset l).card = 0 := by
  rw [Finset.card_eq_zero]
  ext x
  simp [mem_Fset, no_F_short hl x]

/-! Part (a) of P(k) -/

lemma step_a (hn : 4 ≤ n) (k : Nat) (ih : ∀ j < k, P n j)
    (l : List (Fin n × Fin n)) (hl : l.length + 4 = n + k) :
    (Fset l).card ≤ k := by
  by_cases hs : l.length + 2 ≤ n
  · rw [Fset_card_short hs]
    exact Nat.zero_le _
  -- l is long enough to have a last call c
  obtain ⟨l0, c, rfl⟩ : ∃ l0 c, l = l0 ++ [c] := by
    rcases List.eq_nil_or_concat l with h | ⟨L, b, h⟩
    · subst h
      simp only [List.length_nil] at hs
      omega
    · exact ⟨L, b, by rw [h, List.concat_eq_append]⟩
  have hlen : l0.length + 5 = n + k := by simp at hl; omega
  have hk : 3 ≤ k := by simp at hs; omega
  by_contra hcon
  push Not at hcon
  obtain ⟨ha0, hb0⟩ := ih (k - 1) (by omega) l0 (by omega)
  have hsub := Fset_concat_sub l0 c
  -- both endpoints of c must be new F-points, otherwise the count stays <= k
  have hc1 : c.1 ∉ Fset l0 := by
    intro h
    rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at hsub
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le c.2 (Fset l0)
    omega
  have hc2 : c.2 ∉ Fset l0 := by
    intro h
    rw [Finset.insert_eq_of_mem h] at hsub
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le c.1 (Fset l0)
    omega
  have hF0 : (Fset l0).card = k - 1 := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le c.1 (insert c.2 (Fset l0))
    have h3 := Finset.card_insert_le c.2 (Fset l0)
    omega
  have hnew : c.1 ∈ Fset (l0 ++ [c]) := by
    by_contra hnot
    have hsub' : Fset (l0 ++ [c]) ⊆ insert c.2 (Fset l0) := by
      intro y hy
      rcases Finset.mem_insert.mp (hsub hy) with rfl | h
      · exact absurd hy hnot
      · exact h
    have h1 := Finset.card_le_card hsub'
    have h2 := Finset.card_insert_le c.2 (Fset l0)
    omega
  -- by (b) for k - 1, reorder l0 so its last k - 1 calls are between F-points
  obtain ⟨l0', he, htail⟩ := hb0 hF0
  have hlen' := CallEquiv.length_eq he
  set m := l0'.length - (k - 1) with hm
  have hdisj : ∀ q ∈ l0'.drop m, Disj c q := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := htail q hq
    have h1 : q.1 ∈ Fset l0 := by rw [Fset_equiv he, mem_Fset]; exact hq1
    have h2 : q.2 ∈ Fset l0 := by rw [Fset_equiv he, mem_Fset]; exact hq2
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e
    · exact hc1 (by rw [e]; exact h1)
    · exact hc1 (by rw [e]; exact h2)
    · exact hc2 (by rw [e]; exact h1)
    · exact hc2 (by rw [e]; exact h2)
  -- move c in front of that tail
  have hmove : CallEquiv (l0'.drop m ++ [c]) (c :: l0'.drop m) := by
    have h := move_past c (l0'.drop m) [] hdisj
    rw [List.append_nil] at h
    exact CallEquiv.symm h
  have hequiv : CallEquiv (l0 ++ [c]) (l0'.take m ++ c :: l0'.drop m) := by
    have e1 : CallEquiv (l0 ++ [c]) (l0' ++ [c]) := CallEquiv.append_right [c] he
    have e2 : CallEquiv (l0' ++ [c]) (l0'.take m ++ (l0'.drop m ++ [c])) := by
      rw [← List.append_assoc, List.take_append_drop]
    exact e1.trans (e2.trans (CallEquiv.append_left (l0'.take m) hmove))
  -- so c.1 already knows everything after only the first n - 3 calls
  have hFc : IsF (l0'.take m ++ [c]) c.1 := by
    have hFl := mem_Fset.mp hnew
    unfold IsF at hFl ⊢
    rw [run_equiv hequiv] at hFl
    have hu := run_untouched (run (init n) (l0'.take m ++ [c])) (l0'.drop m) c.1
      (fun q hq => ⟨(hdisj q hq).1, (hdisj q hq).2.1⟩)
    rw [show l0'.take m ++ c :: l0'.drop m = (l0'.take m ++ [c]) ++ l0'.drop m by simp,
      run_append, hu] at hFl
    exact hFl
  have hshort : (l0'.take m ++ [c]).length + 2 ≤ n := by
    simp only [List.length_append, List.length_take, List.length_singleton]
    omega
  exact no_F_short hshort c.1 hFc

/-! Tools for part (b) -/

lemma callGraph_adj {l : List (Fin n × Fin n)} {u v : Fin n} :
    (callGraph l).Adj u v ↔ (∃ q ∈ l, s(u, v) = s(q.1, q.2)) ∧ u ≠ v := by
  simp only [callGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]

-- the two parties of any call are connected
lemma reach_of_mem {l : List (Fin n × Fin n)} {q : Fin n × Fin n} (hq : q ∈ l) :
    (callGraph l).Reachable q.1 q.2 := by
  by_cases h : q.1 = q.2
  · exact h ▸ SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (callGraph_adj.mpr ⟨⟨q, hq, rfl⟩, h⟩)

-- a node no call touches can't reach anyone else
lemma reach_untouched {A : List (Fin n × Fin n)} {x y : Fin n}
    (hx : ∀ q ∈ A, x ≠ q.1 ∧ x ≠ q.2) (h : (callGraph A).Reachable x y) : y = x := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    obtain ⟨⟨q, hq, e⟩, _⟩ := callGraph_adj.mp hadj
    rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (hx q hq).1 h1
    · exact (hx q hq).2 h1

-- ...so nobody else learns its secret
lemma secret_stays {A : List (Fin n × Fin n)} {x y : Fin n}
    (hx : ∀ q ∈ A, x ≠ q.1 ∧ x ≠ q.2) (h : x ∈ run (init n) A y) : y = x := by
  obtain ⟨z, hz, hr⟩ := info_path (init n) A x y h
  simp [init] at hz
  subst hz
  exact reach_untouched hx hr

-- swap two whole blocks that share no node
lemma swap_blocks (A B : List (Fin n × Fin n)) (h : ∀ a ∈ A, ∀ b ∈ B, Disj a b) :
    CallEquiv (A ++ B) (B ++ A) := by
  induction A with
  | nil =>
    simp only [List.nil_append, List.append_nil]
    exact Relation.ReflTransGen.refl
  | cons a A ih =>
    have ha : ∀ b ∈ B, Disj a b := fun b hb => h a (by simp) b hb
    have hA : ∀ x ∈ A, ∀ b ∈ B, Disj x b := fun x hx b hb => h x (by simp [hx]) b hb
    exact (CallEquiv.cons a (ih hA)).trans (move_past a B A ha)

-- split a list at its last element failing some test
lemma last_bad (good : Fin n × Fin n → Prop) (L : List (Fin n × Fin n))
    (h : ∃ q ∈ L, ¬ good q) :
    ∃ X b Y, L = X ++ b :: Y ∧ ¬ good b ∧ ∀ y ∈ Y, good y := by
  induction L with
  | nil => simp at h
  | cons c L ih =>
    by_cases h' : ∃ q ∈ L, ¬ good q
    · obtain ⟨X, b, Y, rfl, hb, hY⟩ := ih h'
      exact ⟨c :: X, b, Y, rfl, hb, hY⟩
    · push Not at h'
      obtain ⟨q, hq, hgq⟩ := h
      have hc : ¬ good c := by
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact hgq
        · exact absurd (h' q hq') hgq
      exact ⟨[], c, L, rfl, hc, h'⟩

/-- Does call q lie in the component of a in G? -/
noncomputable def inComp (G : SimpleGraph (Fin n)) (a : Fin n) (q : Fin n × Fin n) : Bool :=
  @decide (G.Reachable a q.1) (Classical.propDecidable _)

lemma inComp_iff {G : SimpleGraph (Fin n)} {a : Fin n} {q : Fin n × Fin n} :
    inComp G a q = true ↔ G.Reachable a q.1 := by
  simp [inComp]

-- a component of the call graph is already connected by its own calls
lemma reach_filter (L : List (Fin n × Fin n)) (a y : Fin n)
    (h : (callGraph L).Reachable a y) :
    (callGraph (L.filter (inComp (callGraph L) a))).Reachable a y := by
  have key : ∀ (u v : Fin n) (w : (callGraph L).Walk u v), (callGraph L).Reachable a u →
      (callGraph (L.filter (inComp (callGraph L) a))).Reachable u v := by
    intro u v w
    induction w with
    | nil => intro _; exact SimpleGraph.Reachable.refl _
    | @cons u v w hadj p ih =>
      intro hau
      have hav : (callGraph L).Reachable a v := hau.trans hadj.reachable
      obtain ⟨⟨q, hq, e⟩, hne⟩ := callGraph_adj.mp hadj
      have hq' : q ∈ L.filter (inComp (callGraph L) a) := by
        rw [List.mem_filter]
        refine ⟨hq, inComp_iff.mpr ?_⟩
        rcases Sym2.eq_iff.mp e with ⟨h1, _⟩ | ⟨_, h2⟩
        · rw [← h1]; exact hau
        · rw [← h2]; exact hav
      exact (SimpleGraph.Adj.reachable (callGraph_adj.mpr ⟨⟨q, hq', e⟩, hne⟩)).trans (ih hav)
  obtain ⟨w⟩ := h
  exact key a y w (SimpleGraph.Reachable.refl _)

-- dropping from W ++ Y leaves part of W's tail, then Y
lemma mem_drop_app {α : Type*} {p : α} (W Y : List α) (i : Nat)
    (h : p ∈ (W ++ Y).drop i) : p ∈ W.drop i ∨ p ∈ Y := by
  induction W generalizing i with
  | nil => exact Or.inr (List.mem_of_mem_drop h)
  | cons w W ih =>
    cases i with
    | zero =>
      simp only [List.drop_zero] at h ⊢
      exact List.mem_append.mp h
    | succ i =>
      simp only [List.cons_append, List.drop_succ_cons] at h ⊢
      exact ih i h

lemma mem_drop_append {α : Type*} {W Y : List α} {r : Nat} {p : α}
    (h : p ∈ (W ++ Y).drop ((W ++ Y).length - (r + Y.length))) :
    p ∈ W.drop (W.length - r) ∨ p ∈ Y := by
  have e : (W ++ Y).length - (r + Y.length) = W.length - r := by
    rw [List.length_append]; omega
  rw [e] at h
  exact mem_drop_app W Y _ h

/-! Step 1: in the first n - 2 calls, every node takes part -/

lemma touched_all (k : Nat) (A B : List (Fin n × Fin n)) (hB : B.length + 2 = k)
    (hcard : (Fset (A ++ B)).card = k) : ∀ x, ∃ q ∈ A, x = q.1 ∨ x = q.2 := by
  intro x
  by_contra hx
  push Not at hx
  -- x's secret leaves x only during B, so x reaches every F-point inside B's graph
  have hreach : ∀ y ∈ insert x (Fset (A ++ B)), (callGraph B).Reachable x y := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact SimpleGraph.Reachable.refl _
    · have hxy : x ∈ run (init n) (A ++ B) y := by
        have hF := mem_Fset.mp hy
        unfold IsF at hF
        rw [hF]
        exact Finset.mem_univ x
      rw [run_append] at hxy
      obtain ⟨z, hz, hr⟩ := info_path _ B x y hxy
      have hzx := secret_stays hx hz
      subst hzx
      exact hr
  have h1 := card_le_of_reach B x _ hreach
  have h2 := Finset.card_le_card (Finset.subset_insert x (Fset (A ++ B)))
  omega

/-! Step 2: reorder the first n - 2 calls so the last two are disjoint -/

lemma split_disjoint (A : List (Fin n × Fin n)) (hA : A.length + 2 = n) (hA2 : 2 ≤ A.length)
    (htouch : ∀ x, ∃ q ∈ A, x = q.1 ∨ x = q.2) :
    ∃ A3 b a, CallEquiv A (A3 ++ [b, a]) ∧ Disj b a := by
  obtain ⟨A', a, rfl⟩ : ∃ A' a, A = A' ++ [a] := by
    rcases List.eq_nil_or_concat A with h | ⟨L, c, h⟩
    · subst h
      simp at hA2
    · exact ⟨L, c, by rw [h, List.concat_eq_append]⟩
  -- the call graph isn't connected, so some node is outside a's component
  have hw : ∃ w, ¬ (callGraph (A' ++ [a])).Reachable a.1 w := by
    by_contra hcon
    push Not at hcon
    have : Nonempty (Fin n) := ⟨a.1⟩
    have hconn : (callGraph (A' ++ [a])).Connected :=
      ⟨fun u v => (hcon u).symm.trans (hcon v)⟩
    have h1 := hconn.card_vert_le_card_edgeSet_add_one
    have h2 := card_edgeSet_le (A' ++ [a])
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    omega
  obtain ⟨w, hw⟩ := hw
  obtain ⟨q, hq, hwq⟩ := htouch w
  have hq1 : ¬ (callGraph (A' ++ [a])).Reachable a.1 q.1 := by
    intro h
    apply hw
    rcases hwq with rfl | rfl
    · exact h
    · exact h.trans (reach_of_mem hq)
  have hqA' : q ∈ A' := by
    rcases List.mem_append.mp hq with h | h
    · exact h
    · exfalso
      simp at h
      subst h
      exact hq1 (SimpleGraph.Reachable.refl _)
  -- b is the last call of A' outside a's component
  obtain ⟨X, b, Y, hsplit, hb, hY⟩ :=
    last_bad (fun c => (callGraph (A' ++ [a])).Reachable a.1 c.1) A' ⟨q, hqA', hq1⟩
  have hb' : ¬ (callGraph (A' ++ [a])).Reachable a.1 b.1 := hb
  have hbA : b ∈ A' ++ [a] := by rw [hsplit]; simp
  have hdisj : ∀ c ∈ A' ++ [a], (callGraph (A' ++ [a])).Reachable a.1 c.1 → Disj b c := by
    intro c hc hcr
    have hb2 : ¬ (callGraph (A' ++ [a])).Reachable a.1 b.2 :=
      fun h => hb' (h.trans (reach_of_mem hbA).symm)
    have hc2 := hcr.trans (reach_of_mem hc)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e
    · exact hb' (by rw [e]; exact hcr)
    · exact hb' (by rw [e]; exact hc2)
    · exact hb2 (by rw [e]; exact hcr)
    · exact hb2 (by rw [e]; exact hc2)
  refine ⟨X ++ Y, b, a, ?_, hdisj a (by simp) (SimpleGraph.Reachable.refl _)⟩
  have hm := move_past b Y [a]
    (fun y hy => hdisj y (by rw [hsplit]; simp [hy]) (hY y hy))
  have := CallEquiv.append_left X hm
  rw [hsplit]
  simpa using this

/-! Steps 3-6: a bad call with at most k - 2 calls after it -/

lemma core (hn : 4 ≤ n) (k : Nat) (ih : ∀ j < k, P n j)
    (l2 X : List (Fin n × Fin n)) (d : Fin n × Fin n) (T : List (Fin n × Fin n))
    (hsplit : l2 = X ++ d :: T) (hl : l2.length + 4 = n + k) (hcard : (Fset l2).card = k)
    (hd : ¬ (d.1 ∈ Fset l2 ∧ d.2 ∈ Fset l2)) (hTk : T.length + 2 ≤ k) :
    ∃ l', CallEquiv l2 l' ∧ TailF l' k := by
  classical
  subst hsplit
  set F := Fset (X ++ d :: T) with hF
  set G2 := callGraph (d :: T) with hG2
  set Pc := inComp G2 d.1 with hPc
  set Th := (d :: T).filter (fun q => !Pc q) with hTh
  set Cl := (d :: T).filter Pc with hCl
  have hinC : ∀ q, Pc q = true ↔ G2.Reachable d.1 q.1 := fun q => inComp_iff
  -- Cl: the calls in d's component (among d :: T); Th: the others
  have hCl_reach : ∀ q ∈ Cl, G2.Reachable d.1 q.1 ∧ G2.Reachable d.1 q.2 := by
    intro q hq
    rw [hCl, List.mem_filter] at hq
    have h1 := (hinC q).mp hq.2
    exact ⟨h1, h1.trans (reach_of_mem hq.1)⟩
  have hpart : CallEquiv (d :: T) (Th ++ Cl) := partition Pc (d :: T) (by
    intro p hp q hq hpP hqP
    have hp1 := (hinC p).mp hpP
    have hp2 : G2.Reachable d.1 p.2 := hp1.trans (reach_of_mem hp)
    have hq1 : ¬ G2.Reachable d.1 q.1 := fun h => by simp [(hinC q).mpr h] at hqP
    have hq2 : ¬ G2.Reachable d.1 q.2 := fun h => hq1 (h.trans (reach_of_mem hq).symm)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e
    · exact hq1 (by rw [← e]; exact hp1)
    · exact hq2 (by rw [← e]; exact hp1)
    · exact hq1 (by rw [← e]; exact hp2)
    · exact hq2 (by rw [← e]; exact hp2))
  have hdC : d ∈ Cl := by
    rw [hCl, List.mem_filter]
    exact ⟨by simp, (hinC d).mpr (SimpleGraph.Reachable.refl _)⟩
  have hr1 : 1 ≤ Cl.length := List.length_pos_of_mem hdC
  have hrk : Cl.length + 1 ≤ k := by
    have := CallEquiv.length_eq hpart
    simp at this
    omega
  -- an endpoint of d that is not an F-point
  obtain ⟨u, hu, huF⟩ : ∃ u, (u = d.1 ∨ u = d.2) ∧ u ∉ F := by
    by_cases h1 : d.1 ∈ F
    · exact ⟨d.2, Or.inr rfl, fun h2 => hd ⟨h1, h2⟩⟩
    · exact ⟨d.1, Or.inl rfl, h1⟩
  -- F-points inside d's component (FC) and outside it (FO)
  set FC := F.filter (fun x => G2.Reachable d.1 x) with hFC
  set FO := F.filter (fun x => ¬ G2.Reachable d.1 x) with hFO
  have hsum : FC.card + FO.card = k := by
    have hsplitF : FC.card + FO.card = F.card := by
      rw [hFC, hFO]
      exact Finset.card_filter_add_card_filter_not ..
    omega
  -- FC plus u sit in one component of Cl's graph, so |FC| <= |Cl|
  have hFC_le : FC.card ≤ Cl.length := by
    have hreach : ∀ y ∈ insert u FC, (callGraph Cl).Reachable d.1 y := by
      intro y hy
      have hyr : G2.Reachable d.1 y := by
        rcases Finset.mem_insert.mp hy with h | h
        · rw [h]
          rcases hu with h' | h' <;> subst h'
          · exact SimpleGraph.Reachable.refl _
          · exact reach_of_mem (l := d :: T) (q := d) (by simp)
        · rw [hFC, Finset.mem_filter] at h
          exact h.2
      exact reach_filter (d :: T) d.1 y hyr
    have h1 := card_le_of_reach Cl d.1 _ hreach
    have huFC : u ∉ FC := by
      rw [hFC, Finset.mem_filter]
      exact fun h => huF h.1
    have h2 := Finset.card_lt_card (Finset.ssubset_insert huFC)
    omega
  -- FO points don't need Cl: they're F-points of X ++ Th already
  have hl2eq : CallEquiv (X ++ d :: T) (X ++ Th ++ Cl) := by
    have := CallEquiv.append_left X hpart
    simpa [List.append_assoc] using this
  have hFO_sub : FO ⊆ Fset (X ++ Th) := by
    intro x hx
    rw [hFO, Finset.mem_filter] at hx
    obtain ⟨hxF, hxr⟩ := hx
    rw [mem_Fset]
    have hxF' := mem_Fset.mp hxF
    unfold IsF at hxF' ⊢
    rw [run_equiv hl2eq, run_append] at hxF'
    have hu' := run_untouched (run (init n) (X ++ Th)) Cl x (fun q hq =>
      ⟨fun e => hxr (by rw [e]; exact (hCl_reach q hq).1),
       fun e => hxr (by rw [e]; exact (hCl_reach q hq).2)⟩)
    rw [hu'] at hxF'
    exact hxF'
  -- (a) and (b) at k - |Cl| for X ++ Th
  have hlenXTh : (X ++ Th).length + 4 = n + (k - Cl.length) := by
    have := CallEquiv.length_eq hl2eq
    simp at this hl ⊢
    omega
  obtain ⟨haO, hbO⟩ := ih (k - Cl.length) (by omega) (X ++ Th) hlenXTh
  have hFO_card : FO.card = k - Cl.length := by
    have := Finset.card_le_card hFO_sub
    omega
  have hFC_card : FC.card = Cl.length := by omega
  have hFO_eq : FO = Fset (X ++ Th) := Finset.eq_of_subset_of_card_le hFO_sub (by omega)
  obtain ⟨Y, hY, hYtail⟩ := hbO (by rw [← hFO_eq]; exact hFO_card)
  have hYlen := CallEquiv.length_eq hY
  set m := Y.length - (k - Cl.length) with hm
  have hY2good : ∀ q ∈ Y.drop m, q.1 ∈ FO ∧ q.2 ∈ FO := by
    intro q hq
    obtain ⟨h1, h2⟩ := hYtail q hq
    rw [hFO_eq, Fset_equiv hY]
    exact ⟨mem_Fset.mpr h1, mem_Fset.mpr h2⟩
  have hdisjYC : ∀ a ∈ Y.drop m, ∀ b ∈ Cl, Disj a b := by
    intro a ha b hb
    obtain ⟨ha1, ha2⟩ := hY2good a ha
    rw [hFO, Finset.mem_filter] at ha1 ha2
    obtain ⟨hb1, hb2⟩ := hCl_reach b hb
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e
    · exact ha1.2 (by rw [e]; exact hb1)
    · exact ha1.2 (by rw [e]; exact hb2)
    · exact ha2.2 (by rw [e]; exact hb1)
    · exact ha2.2 (by rw [e]; exact hb2)
  -- move Cl in front of Y's tail
  set Y1 := Y.take m with hY1
  set Y2 := Y.drop m with hY2
  have hchain : CallEquiv (X ++ d :: T) (Y1 ++ Cl ++ Y2) := by
    have e1 : CallEquiv (X ++ Th ++ Cl) (Y ++ Cl) := CallEquiv.append_right Cl hY
    have e2 : CallEquiv (Y ++ Cl) (Y1 ++ (Y2 ++ Cl)) := by
      rw [← List.append_assoc, hY1, hY2, List.take_append_drop]
    have e3 : CallEquiv (Y1 ++ (Y2 ++ Cl)) (Y1 ++ (Cl ++ Y2)) :=
      CallEquiv.append_left Y1 (swap_blocks Y2 Cl hdisjYC)
    have := hl2eq.trans (e1.trans (e2.trans e3))
    simpa [List.append_assoc] using this
  have hY1len : Y1.length = n - 4 := by
    rw [hY1, List.length_take]
    omega
  have hY2len : Y2.length = k - Cl.length := by
    rw [hY2, List.length_drop]
    omega
  -- FC points are F-points of Y1 ++ Cl, since Y2 never touches them
  have hFC_sub : FC ⊆ Fset (Y1 ++ Cl) := by
    intro x hx
    rw [hFC, Finset.mem_filter] at hx
    obtain ⟨hxF, hxr⟩ := hx
    rw [mem_Fset]
    have hxF' := mem_Fset.mp hxF
    unfold IsF at hxF' ⊢
    rw [run_equiv hchain, run_append] at hxF'
    have hu' := run_untouched (run (init n) (Y1 ++ Cl)) Y2 x (fun q hq => by
      obtain ⟨h1, h2⟩ := hY2good q hq
      rw [hFO, Finset.mem_filter] at h1 h2
      exact ⟨fun e => h1.2 (by rw [← e]; exact hxr), fun e => h2.2 (by rw [← e]; exact hxr)⟩)
    rw [hu'] at hxF'
    exact hxF'
  -- (a) and (b) at |Cl| for Y1 ++ Cl
  have hZlen : (Y1 ++ Cl).length + 4 = n + Cl.length := by
    simp
    omega
  obtain ⟨haZ, hbZ⟩ := ih Cl.length (by omega) (Y1 ++ Cl) hZlen
  have hZcard : (Fset (Y1 ++ Cl)).card = Cl.length := by
    have := Finset.card_le_card hFC_sub
    omega
  have hFC_eq : FC = Fset (Y1 ++ Cl) := Finset.eq_of_subset_of_card_le hFC_sub (by omega)
  obtain ⟨W, hW, hWtail⟩ := hbZ hZcard
  -- final list: W then Y2
  have hfin : CallEquiv (X ++ d :: T) (W ++ Y2) := hchain.trans (CallEquiv.append_right Y2 hW)
  refine ⟨W ++ Y2, hfin, ?_⟩
  unfold TailF
  intro p hp
  have hFfin : Fset (W ++ Y2) = F := (Fset_equiv hfin).symm
  have key : p.1 ∈ F ∧ p.2 ∈ F := by
    have hp' : p ∈ (W ++ Y2).drop ((W ++ Y2).length - (Cl.length + Y2.length)) := by
      rw [show Cl.length + Y2.length = k by omega]
      exact hp
    rcases mem_drop_append hp' with h | h
    · obtain ⟨h1, h2⟩ := hWtail p h
      have h1' : p.1 ∈ FC := by rw [hFC_eq, Fset_equiv hW]; exact mem_Fset.mpr h1
      have h2' : p.2 ∈ FC := by rw [hFC_eq, Fset_equiv hW]; exact mem_Fset.mpr h2
      rw [hFC, Finset.mem_filter] at h1' h2'
      exact ⟨h1'.1, h2'.1⟩
    · obtain ⟨h1, h2⟩ := hY2good p h
      rw [hFO, Finset.mem_filter] at h1 h2
      exact ⟨h1.1, h2.1⟩
  rw [← hFfin] at key
  exact ⟨mem_Fset.mp key.1, mem_Fset.mp key.2⟩

/-! Part (b) of P(k) -/

lemma step_b (hn : 4 ≤ n) (k : Nat) (ih : ∀ j < k, P n j)
    (l : List (Fin n × Fin n)) (hl : l.length + 4 = n + k) :
    (Fset l).card = k → ∃ l', CallEquiv l l' ∧ TailF l' k := by
  intro hcard
  by_cases hs : l.length + 2 ≤ n
  · -- no F-points at all, so k = 0 and there's nothing to arrange
    have hk0 : k = 0 := by
      rw [Fset_card_short hs] at hcard
      omega
    subst hk0
    refine ⟨l, Relation.ReflTransGen.refl, ?_⟩
    unfold TailF
    intro p hp
    simp at hp
  have hk : 3 ≤ k := by omega
  obtain ⟨A, B, rfl, hAlen, hBlen⟩ :
      ∃ A B, l = A ++ B ∧ A.length = n - 2 ∧ B.length = k - 2 :=
    ⟨l.take (n - 2), l.drop (n - 2), (List.take_append_drop _ _).symm,
      by simp; omega, by simp; omega⟩
  -- steps 1 and 2
  have htouch := touched_all k A B (by omega) hcard
  obtain ⟨A3, b, a, hA3, hba⟩ := split_disjoint A (by omega) (by omega) htouch
  have hA3len : A3.length = n - 4 := by
    have := CallEquiv.length_eq hA3
    simp at this
    omega
  have he1 : CallEquiv (A ++ B) (A3 ++ b :: a :: B) := by
    have := CallEquiv.append_right B hA3
    simpa using this
  have hF1 : Fset (A3 ++ b :: a :: B) = Fset (A ++ B) := (Fset_equiv he1).symm
  have hlen1 : (A3 ++ b :: a :: B).length + 4 = n + k := by
    simp
    omega
  -- the last k calls are b :: a :: B; if all are between F-points we're done
  by_cases hall : ∀ q ∈ b :: a :: B, q.1 ∈ Fset (A ++ B) ∧ q.2 ∈ Fset (A ++ B)
  · refine ⟨_, he1, ?_⟩
    unfold TailF
    intro p hp
    have hidx : (A3 ++ b :: a :: B).length - k = A3.length := by
      simp
      omega
    rw [hidx, List.drop_left] at hp
    obtain ⟨h1, h2⟩ := hall p hp
    rw [← hF1] at h1 h2
    exact ⟨mem_Fset.mp h1, mem_Fset.mp h2⟩
  have hbad : ∃ q ∈ b :: a :: B, ¬ (q.1 ∈ Fset (A ++ B) ∧ q.2 ∈ Fset (A ++ B)) := by
    by_contra hc
    push Not at hc
    exact hall hc
  obtain ⟨X0, d, T, hsplit, hd, -⟩ :=
    last_bad (fun q => q.1 ∈ Fset (A ++ B) ∧ q.2 ∈ Fset (A ++ B)) _ hbad
  rcases X0 with _ | ⟨x, X0'⟩
  · -- the bad call is b, with k - 1 calls after it: swap b and a first
    simp only [List.nil_append, List.cons.injEq] at hsplit
    obtain ⟨hbd, -⟩ := hsplit
    rw [← hbd] at hd
    have hswap : Swap (A3 ++ b :: a :: B) (A3 ++ a :: b :: B) := Swap.mk A3 B b a hba
    have he2 : CallEquiv (A ++ B) (A3 ++ a :: b :: B) :=
      he1.trans (Relation.ReflTransGen.single hswap)
    have hF2 : Fset (A3 ++ a :: b :: B) = Fset (A ++ B) := (Fset_equiv he2).symm
    obtain ⟨l', he', ht'⟩ := core hn k ih (A3 ++ a :: b :: B) (A3 ++ [a]) b B
      (by simp) (by simp; omega) (by rw [hF2]; exact hcard) (by rw [hF2]; exact hd)
      (by omega)
    exact ⟨l', he2.trans he', ht'⟩
  · -- the bad call already has at most k - 2 calls after it
    have hTlen : T.length + 2 ≤ k := by
      have := congrArg List.length hsplit
      simp at this
      omega
    obtain ⟨l', he', ht'⟩ := core hn k ih (A3 ++ b :: a :: B) (A3 ++ x :: X0') d T
      (by rw [hsplit]; simp) hlen1 (by rw [hF1]; exact hcard) (by rw [hF1]; exact hd) hTlen
    exact ⟨l', he1.trans he', ht'⟩

/-! Assembling everything -/

theorem P_all (hn : 4 ≤ n) (k : Nat) : P n k := by
  refine Nat.strong_induction_on k ?_
  intro k ih l hl
  exact ⟨step_a hn k ih l hl, step_b hn k ih l hl⟩

theorem lower_bound (hn : 4 ≤ n) (l : List (Fin n × Fin n)) (hc : ∀ x, IsF l x) :
    2 * n - 4 ≤ l.length := by
  by_contra hlt
  push Not at hlt
  by_cases hs : l.length + 2 ≤ n
  · exact no_F_short hs ⟨0, by omega⟩ (hc _)
  · have hall : Fset l = Finset.univ := by
      ext x
      simp [mem_Fset, hc x]
    have h := (P_all hn (l.length + 4 - n) l (by omega)).1
    rw [hall, Finset.card_univ, Fintype.card_fin] at h
    omega

end Gossip

#min_imports
