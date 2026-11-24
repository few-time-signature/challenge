# GRS-CC · 756-byte construction

This directory contains the compact [program manifest](program.json) for the organizer's fixed [Lean scheme](../../formal/PoissonDAG/Constructions/GRSCC/Circuit.lean). Its 756-byte signature sets the construction track’s opening bound. [Complete starter and proof](../entries/construction/grs-cc-756-lean/) · [Verified submission](https://github.com/few-time-signature/challenge/pull/8)

## What is transmitted?

A route picks one of 16 buckets, one of two starting owners, and one slot in each of seven layers. Each layer contributes one guard label and five authentication labels from a height-five binary tree. A six-coordinate codeword with entries in 0…8 and sum 16 selects their hash-chain depths. The 42 layer labels and five outer authentication labels cost at most 47 × 16 bytes. A 32-bit counter adds four bytes, giving **756 bytes**.

The addressed graph has 2,629,119 vertices. Each counter trial uses two hash calls for a 170-bit input. An accepted input decodes into a route. Expected signing uses fewer than 11,676,797 hashes. Honest verification uses at most 441 hashes on an accepted input. See the [graph](../../formal/PoissonDAG/Constructions/GRSCC/Graph.lean), [encoder](../../formal/PoissonDAG/Constructions/GRSCC/RankEncoding.lean), and [size, cost and correctness lemmas](../../formal/PoissonDAG/Constructions/GRSCC/Circuit.lean).

## Why the covering bound holds

The shared-Poisson reduction needs twenty local supplier-count inequalities. The submitted proof computes all twenty from 63 integer evaluations, extracts the required coefficients, and applies the organizer’s Poisson theorem. The final Lean goal binds this calculation, authentication, correctness, hash costs and size to the registered graph and encoder. [Verified proof and author write-up](https://github.com/few-time-signature/challenge/pull/8) · [Kernel replay](https://github.com/few-time-signature/challenge/actions/runs/45456970669)

To build the public components locally with the pinned Lean toolchain:

```sh
lake build PoissonDAG.Constructions.GRSCC.Certification PoissonDAG.Constructions.GRSCC.TwoSame
```
