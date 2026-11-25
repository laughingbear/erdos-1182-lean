# erdos-1182-lean

Lean 4 proofs of two statements from Erdős Problem 1182 in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/1182.lean`):

- `erdos_1182.variants.chvatal`: Chvátal's theorem for triangles, R(K₃, T) = 2n − 1 for every tree T on n vertices.
- `erdos_1182.variants.F_ge_pred`: F(n) ≥ n − 1.

Definitions and statements are copied verbatim from formal-conjectures; Mathlib is pinned to the same
commit (`0df444a`, Lean v4.33.1). `lake build` checks everything; both theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`.

The proofs were written with AI assistance (Claude).
