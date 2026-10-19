import Gossip.Induction

/-!
The full result in one place. To trust it, you only need to read the
definitions below and the two theorem statements; the Lean kernel checks
that the proofs match them.

Definitions (Gossip/Basic.lean):

  State n  := Fin n → Finset (Fin n)            -- who knows which secrets
  init n i := {i}                                -- agent i knows only its own secret
  call s p := both p.1 and p.2 get s p.1 ∪ s p.2, everyone else unchanged
  run s l  := apply the calls in l from first to last

Gossip/Lower.lean:

  IsF l x  := run (init n) l x = Finset.univ     -- x knows every secret
-/

namespace Gossip

/-- For n ≥ 4, the minimum number of calls is exactly 2n - 4. -/
theorem gossip_min_calls (n : Nat) (hn : 4 ≤ n) :
    (∃ l : List (Fin n × Fin n), l.length = 2 * n - 4 ∧ ∀ x, IsF l x) ∧
    (∀ l : List (Fin n × Fin n), (∀ x, IsF l x) → 2 * n - 4 ≤ l.length) := by
  refine ⟨?_, fun l hl => lower_bound hn l hl⟩
  obtain ⟨l, hlen, hall⟩ := upper_bound n hn
  exact ⟨l, hlen, hall⟩

#print axioms gossip_min_calls

/-! Sanity checks: the model behaves as expected on small cases. -/

-- the 4-call protocol for n = 4: everyone ends with {0, 1, 2, 3}
#eval (List.finRange 4).map (run (init 4) [(0, 1), (2, 3), (0, 2), (1, 3)])

-- a call shares both ways: after (0, 1), agents 0 and 1 know {0, 1}, 2 still knows {2}
#eval (List.finRange 3).map (run (init 3) [(0, 1)])

-- order matters: (0,1) then (1,2) informs 2 of secret 0, but not the reverse order
#eval run (init 3) [(0, 1), (1, 2)] 2
#eval run (init 3) [(1, 2), (0, 1)] 2

-- a direct consequence: no 3-call protocol works for 4 agents
example : ¬ ∃ l : List (Fin 4 × Fin 4), l.length = 3 ∧ ∀ x, IsF l x := by
  rintro ⟨l, hlen, hall⟩
  have := lower_bound (by norm_num) l hall
  omega

end Gossip
