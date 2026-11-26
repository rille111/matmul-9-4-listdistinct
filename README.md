# List distinctness lower bound from OpenAI's 9/4 matrix multiplication paper: standalone Lean restatement and Boolean circuit corollary

This repository is an independent companion to the OpenAI paper **"The matrix multiplication exponent is nine fourths"** (November 24, 2026) and its Lean formalization in [openai/math](https://github.com/openai/math). Paper: [paper.pdf](https://github.com/openai/math/blob/main/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf). All credit for the underlying mathematics and its formal proof belongs to the authors of that paper.

It looks at the load bearing lemma, the list distinctness bound (Theorem 2.2, `BatchDescent.manyList` in the Lean source), and contributes three things:

1. **An independent build.** `ListDistinct.lean` imports the upstream modules and restates the bound with the wrapper predicates (`ManyList`, `Realizes`, `listBits`) unfolded, so a reader only has to trust the network model `Net` and the target tensor `distinctPower`. It also records the matching upper bound, which shows the statement is not vacuous.
2. **A Lean checked corollary.** `circuit_lower` proves in Lean that Boolean straight line programs embed into the network model with linear overhead (at most `2n + 4s` vertices), so the list bound implies: there is `σ > 0` such that any Boolean circuit over the full binary basis deciding element distinctness of `2^w` strings of `2w` bits has size greater than `(n·w^σ − 9n − 3)/12`, where `n = 2w·2^w` is the input length. That is size `Ω(n·(log n)^σ)`.
3. **A human readable exposition.** `exposition.md` maps the dependency tree, sketches the proof levels as they appear in the Lean source, and lists where the Lean route and the paper's prose differ.

## Paper, trust base and second kernel check

**Paper (version 2, 14 pages):** *A Lean checked Boolean circuit corollary of OpenAI's list distinctness theorem*, Rickard Robin. PDF: [`paper/main.pdf`](paper/main.pdf). Source: [`paper/main.tex`](paper/main.tex), [`paper/refs.bib`](paper/refs.bib), abstract: [`paper/abstract.txt`](paper/abstract.txt). Not yet on arXiv. The paper is licensed CC BY 4.0.

**Trust base:** [`trustbase/`](trustbase/). `TrustBase.lean` is a Lean metaprogram that computes the transitive closure of constants used by `circuit_lower`; `trustbase.txt` is its output and `circuit_lower_modules.txt` lists the contributing modules with constant and line counts. Summary: 44,847 constants from 1,360 modules, among them 191 openai/math modules with 94,244 lines, of which about 1,000 have been read by us as human mathematics.

**Second kernel:** [`second-kernel/`](second-kernel/). The full dependency closure of our five main theorems, including the whole upstream proof of `BatchDescent.hard`, was exported with lean4export and checked by the independent type checker [nanoda](https://github.com/ammkrn/nanoda_lib), admitting only `propext`, `Classical.choice` and `Quot.sound`: "Checked 45579 declarations with no errors". Files: `nanoda-config.json`, `nanoda-run.log`, `nanoda-pp.txt` (pretty printed statement of `circuit_lower`) and `nanoda-run-summary.md` (versions, commits, hashes and a negative control).

## Important caveats

* **Everything here is conditional on the soundness of the upstream proof** of `BatchDescent.hard`. Its import closure has about 168k lines; the constants actually used come from 191 upstream modules with 94,244 lines. Two kernels (Lean's own via leanchecker, and nanoda) accept the proof, but we have read only about 1,000 of those lines as human mathematics, and none of Levels 3 and 4. See `exposition.md`, Sections 3, 4 and 7, and Section 6.6 of the paper.
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
| `paper/` | The paper (PDF, LaTeX source, bibliography, abstract) |
| `trustbase/` | Trust base metaprogram and its output |
| `second-kernel/` | nanoda configuration, log, pretty printed statement and run summary |

## How to reproduce

1. Check out [openai/math](https://github.com/openai/math) and build its Lean project (Lean v4.34.1, Mathlib `d13f23b7`).
2. Copy `ListDistinct.lean` into the project root and run `lake env lean ListDistinct.lean`.
3. For the kernel replay, compile an olean with `lake env lean -R . -o .lake/build/lib/lean/ListDistinct.olean ListDistinct.lean`, then run `lake env leanchecker ListDistinct`.

## License

Apache License 2.0, see `LICENSE`. The upstream openai/math code is under its own license.
