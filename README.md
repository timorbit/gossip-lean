# Gossip: 2n − 4 calls in Lean 4

A Lean 4 / Mathlib formalization of the classic gossip (telephone) problem: with n ≥ 4 people, each knowing one secret, where a call between two people shares everything both know, exactly 2n − 4 calls are needed for everyone to learn everything.

Both directions are proved, with no `sorry`:

- `Gossip.upper_bound` (Gossip/Basic.lean): a protocol with 2n − 4 calls exists.
- `Gossip.lower_bound` (Gossip/Induction.lean): every complete protocol has at least 2n − 4 calls.

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for both.

## Proof

The lower bound follows Hajnal, Milner and Szemerédi, "A cure for the telephone disease", Canad. Math. Bull. 15 (1972) 447–450. The key statement is that after n + k − 4 calls at most k people know everything, proved by strong induction on k using two operations: swapping adjacent calls that share no person, and comparing edge counts with connectivity of the call graph.

| File | Contents |
|---|---|
| Basic.lean | model (states, calls, runs) and the upper bound |
| Lower.lean | swapping disjoint calls, equivalent call lists, partition lemma |
| Flow.lean | information flow implies paths in the call graph; at most n − 2 calls inform nobody |
| Bridge.lean | a connected set of nodes has at most (calls + 1) nodes |
| Induction.lean | the induction, both parts, and the final theorem |

## Building

```
lake exe cache get
lake build
```

The proofs were written with Claude (Anthropic) and checked by the Lean kernel.
