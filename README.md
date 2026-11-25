# List distinctness lower bound from OpenAI's 9/4 matrix multiplication paper: standalone Lean restatement and Boolean circuit corollary

This repository is an independent companion to the OpenAI paper **"The matrix multiplication exponent is nine fourths"** (November 24, 2026) and its Lean formalization in [openai/math](https://github.com/openai/math). Paper: [paper.pdf](https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf). All credit for the underlying mathematics and its formal proof belongs to the authors of that paper.

It looks at the load bearing lemma, the list distinctness bound (Theorem 2.2, `BatchDescent.manyList` in the Lean source), and contributes three things:

1. **An independent build.** `ListDistinct.lean` imports the upstream modules and restates the bound with the wrapper predicates (`ManyList`, `Realizes`, `listBits`) unfolded, so a reader only has to trust the network model `Net` and the target tensor `distinctPower`. It also records the matching upper bound, which shows the statement is not vacuous.
2. **A Lean checked corollary.** `circuit_lower` proves in Lean that Boolean straight line programs embed into the network model with linear overhead (at most `2n + 4s` vertices), so the list bound implies: there is `σ > 0` such that any Boolean circuit over the full binary basis deciding element distinctness of `2^w` strings of `2w` bits has size greater than `(n·w^σ − 9n − 3)/12`, where `n = 2w·2^w` is the input length. That is size `Ω(n·(log n)^σ)`.
3. **A human readable exposition.** `exposition.md` maps the dependency tree, sketches the proof levels as they appear in the Lean source, and lists where the Lean route and the paper's prose differ.

## Important caveats

* **Everything here is conditional on the soundness of the upstream proof** of `BatchDescent.hard` (about 168k lines in its dependency closure). We built it and replayed our own module through the kernel, but we have not audited Levels 3 and 4 of the proof as human mathematics. See `exposition.md`, Sections 3, 4 and 7.
* **σ is not explicit**, because the upstream proof goes through a contradiction argument.
* The embedding of Boolean circuits is a routine step. The new content is that it is now stated and checked in Lean, and that the superlinear Boolean reading is made explicit.
* Context: the best explicit lower bound for general circuits over the full binary basis that we are aware of is linear, `4n − O(log n)` ([Mishra and Santhanam, ECCC TR26 260](https://eccc.weizmann.ac.il/report/2026/260/)). For element distinctness specifically, the prior lower bounds we know of are time space tradeoffs for branching programs (Ajtai; Beame, Saks, Sun and Vee 2003), not superlinear circuit size bounds. If the upstream proof is sound, the corollary here is a superlinear bound of a kind not previously known. Please treat it as a claim to be scrutinized by experts.

## Files

| File | Content |
|---|---|
| `ListDistinct.lean` | Standalone restatement and the `circuit_lower` corollary (SHA256 `12b017a49872e161e1bc8ee3d413411893c20f40716d2ef4cd64cba28caeaa29`) |
| `build.log` | `lake env lean ListDistinct.lean`: exit 0, all `#print axioms` lines show only `[propext, Classical.choice, Quot.sound]` |
| `leanchecker.log` | `lake env leanchecker ListDistinct`: kernel replay of every declaration in this module, exit 0 (imported modules trusted) |
| `exposition.md` | Readable exposition of the bound and its proof structure |

## How to reproduce

1. Check out [openai/math](https://github.com/openai/math) and build its Lean project (Lean v4.34.1, Mathlib `d13f23b7`).
2. Copy `ListDistinct.lean` into the project root and run `lake env lean ListDistinct.lean`.
3. For the kernel replay, compile an olean with `lake env lean -R . -o .lake/build/lib/lean/ListDistinct.olean ListDistinct.lean`, then run `lake env leanchecker ListDistinct`.

## License

Apache License 2.0, see `LICENSE`. The upstream openai/math code is under its own license.
