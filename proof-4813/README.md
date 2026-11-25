# Petersen edge-function lower bound L-meta-4813

This branch contains a Lean proof of the exact statement posted as L-meta-4813. Each vertex of the Petersen graph supplies one Boolean input. The target is true when the endpoints of at least one edge are both true. The circuit is given two additional wires. The first is the conjunction of inputs 0 and 2. The second is an AND of at most two of the pins specified by the task. For every allowed wiring, any further fan-in-two AND/OR/NOT circuit with at most 17 gates fails on some input. [Project statement](https://pequalnp.com/lemma#L-meta-4813)

The proof handles monotone circuits by removing the first auxiliary wire, which is false on every minimal positive input. In a circuit containing a NOT, at most 16 binary gates remain. The checker can allow complementation for free in that case. A finite certificate combines restrictions to smaller induced graphs with tests that a circuit's available signals distinguish positive inputs from negative ones. The signed search expanded 1,284 states after identifying graph symmetries.

## Reproduce the local verification

This branch is based on upstream commit `5dc39d7ba06efb05c2bc7b2f9da2075a9f335840`, with Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. From the root of this checkout, obtain the pinned Mathlib cache and run the verifier.

```sh
(cd lean && lake exe cache get)
python3 proof-4813/verify.py
```

The verifier builds each source module. The final audit checks the theorem against a second copy of the desk statement and prints its axiom dependencies. The audit produced this line.

```text
'PEqualNP.Outside.L_meta_4813' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The SHA-256 of the published statement, excluding the trailing newline, is `252390eff8004467f249b6648750400b8c224b723077ba83aca2ba6df38ce09b`. The certificate uses the project's checked nine-vertex results L-meta-6581 and L-meta-670. The source adaptations retain the upstream Apache-2.0 license and contributor attributions. [Upstream proof library](https://github.com/open-goat/pequalnp-proofs)

The project task desk and its authoritative checker separately record official submission and credit for the single-file entry.
