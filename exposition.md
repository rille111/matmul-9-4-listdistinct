# List distinctness lower bound (Theorem 2.2 / `manyList`): standalone Lean restatement, Boolean circuit corollary, and human readable exposition

This is the English part of the exposition. It assumes the soundness of the upstream Lean proof of `BatchDescent.hard` in openai/math, which we did not audit line by line (see Levels 3 and 4).

## 0. Files and provenance

| Item | Location |
|---|---|
| Lean file (this work) | `ListDistinct.lean` in this repository |
| SHA256 of the Lean file | `12b017a49872e161e1bc8ee3d413411893c20f40716d2ef4cd64cba28caeaa29` |
| Build log | `build.log`; kernel replay log `leanchecker.log` |
| Build | `lake env lean ListDistinct.lean` on a Windows x86_64 workstation, Lean 4.34.1 (commit 5045d005), Lake 5.0.0, Mathlib d13f23b7. Priority BelowNormal, `LEAN_NUM_THREADS=8`. Started 2026-11-25 23:55:14 Europe/Stockholm, exit code 0, 27.7 s. |
| Upstream source | openai/math Lean project (https://github.com/openai/math). Paper text at `math/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf`. |

The Lean file has 13 `#print axioms` lines. Every one prints `[propext, Classical.choice, Quot.sound]`, and this includes the upstream `BatchDescent.manyList` and `BatchDescent.hard`. Everything below was read from the Lean source or produced by the Lean build.

## 1. The model (Network.lean)

* **Wires.** `Wire` is a binary tree whose leaves are `bit` or `unit`. `Val a` is the set of assignments to its bits, and `wd a` is the number of bits.
* **Networks.** `Net F a b k m` means: the tensor `k : Val a → Val b → F` has a network with `m` vertices (Network.lean:59). The constructors are:
  * `table`: one vertex carrying any `F`-valued table on at most 3 bits (`wd a + wd b ≤ 3`). Cost 1.
  * `par`: juxtapose two networks. Their tensors multiply.
  * `comp`: join wires. This **sums over** the shared bits.
  * `trace`: join an output bundle back to an input bundle, also summed. This is what allows arbitrary graphs and cycles.
  * `pre`, `post`: free rewirings (permute bits and rebracket).
  * `empty`: the empty network.
* **The target tensor.** `lists w t` is `t` independent lists. Each list is a binary tree of `2^w` records of `2w` bits. `distinctPower F w t x` is the product over the `t` lists of the 0/1 indicator "the records of this list are pairwise distinct" (Network.lean:85 to 91).
* **Size.** `Realizes F w t m` holds when there is `v` with `Net F (lists w t) unit (distinctPower F w t) v` and `m = v + t·listBits w`, where `listBits w = 2w·2^w` (Network.lean:93, ListBounds.lean:15). So `m` counts vertices plus exterior bits.

Because the tables take values in a field and internal wires are summed, the model is at least as strong as Boolean circuits (Section 4 proves this in Lean). It also captures exact "count the witnesses in F" computations.

## 2. The statement, unfolded (Lean output)

`ListDistinctExposition.manyList_unfolded` (ListDistinct.lean:34) is proved by `BatchDescent.manyList F`:

```
∀ F [Field F] [Finite F], ∃ σ > 0, ∀ᶠ w in atTop, ∀ t m,
  1 ≤ t → t ≤ 2w·2^w →
  (∃ v, Net F (lists w t) unit (distinctPower F w t) v ∧ m = v + t·(2w·2^w)) →
  t · (2w·2^w) · w^σ < 3m
```

The stronger upstream form, `manyList_full_unfolded` (ListDistinct.lean:44, from Hard.lean:20), allows `t ≤ 2^(w^(1+η))` and drops the factor 3: `t·listBits w·w^η < m`.

**Non-vacuity** (`upper`, ListDistinct.lean:116, from Distinctness.lean:51 `seed`): there is a constant `C` such that for all large `w` some `m ≤ C·listBits w·w²` satisfies `Realizes F w 1 m`. The upstream proof uses `C = 2000` and a Batcher sorting network followed by an adjacent comparison. So for one list the true complexity lies between `n·w^σ/3 − n` and `2000·n·w²`, where `n = listBits w`.

## 3. Dependency tree

Computed from the `import` lines of the upstream Lean project:

* `BatchDescent.Hard` has 309 OAI modules in its import closure, about 168,333 lines. These form a subset of the 592 modules behind `square_exponent`.
* Modules by directory: Assembly 64, Sphere 47, BatchDescent 26, Processor 16, Routing 15, Packing 14, Spectral 12, Rounds 10, plus smaller groups. Tagged has 7, Diagonal 9 and Network 2.
* Directory sizes: BatchDescent 17,986 lines, Processor 10,165, Diagonal 4,531, Tagged 1,829.

The proof term for `manyList` (Hard.lean:17 to 27):

```
manyList F   = Tagged.manyList_of_tag (hard F)                        -- Reduction.lean:382
hard F       = Processor.hard_of_descent (descent (fun bad => compilation_of_encoded (encoded bad)))
hard_of_descent h = hard_of_resists (resists F K q) h                  -- Resistance.lean:67, Broadcast.lean:556
resists      = resists_of_programmable (programmable_of_control (control F) K q)   -- Resistance.lean:62, Broadcast.lean:813, DispatchSize.lean:738
descent      : (¬Tagged.Hard F → Compilation F) → Diagonal.Descent F (Cheap F 50000 2)   -- Encoded.lean:82
encoded      : ¬Tagged.Hard F → Encoded F                              -- Compilation.lean:867
compilation_of_encoded : Encoded F → Compilation F                     -- Compilation.lean:783
```

There are four levels. Level 1 is ManyList from Hard. Level 2 is Hard from Resists plus Descent. Level 3 is Descent, obtained from the failure of Hard. Level 4 is Resists, which is unconditional.

## 4. Human readable proof sketch, following the Lean source

### Level 1. ManyList follows from tagged permutation hardness (Tagged/Reduction.lean, read in full)

**Tagged.Hard F** (Tagged/Hard.lean:11). There is `σ > 0` such that for all large `w`, every network for `tag F w (word w)` has at least `2^w·w·w^σ` vertices. The tensor `tag` takes `N = 2^w` input records and `N` proposed output rows `(index, payload)`. Its value is 1 exactly when the output rows are a permutation of the inputs, each labelled with its original position, and 0 otherwise (Tags.lean, `tag`, `permuted`, `label`). The input has about `3w·N` bits, so Hard says that verifying a tagged permutation costs a factor `w^σ` more than linear.

**Lemma A (signed distinctness, `cancel`, Reduction.lean:128).** Let `A` be a list of `N` distinct records and `B` a list of `N` records. Fix an injective encoding `E(p, x)` of a flag bit `p` together with a record `x`. For a flag vector `z ∈ {0,1}^N`, form the list

`L(z) = [E(false, B_i)]_i ++ [E(z_i, A_i)]_i`

and the sign `sign(z) = ∏_i (z_i ? 1 : −1)`. Then

`Σ_z sign(z)·[L(z) has no repeats] = [B is a permutation of A]`.

*Proof idea.* Take `B` without repeats, which is necessary for the left side to be nonzero. For each `i`:
* The flagged word `E(true, A_i)` never collides with anything.
* The word `E(false, A_i)` collides exactly when `A_i ∈ B`.

The sum factorizes over `i` (`sum_term`), and each factor is `1 − [A_i ∉ B] = [A_i ∈ B]`. So the left side equals `[B has no repeats]·[A ⊆ B]`, and since `|A| = |B|` this is "B is a permutation of A". Only the scalars 0, 1 and −1 occur, so the lemma holds in every characteristic.

**Step 1.1 (`tag_of_distinct`, Reduction.lean:180).** Apply Lemma A with `A` = the input records tagged by position (these are distinct by construction) and `B` = the proposed rows. The flag sums, the encoders and the sign tables cost `O(t·listBits)` vertices. So a network of size `m` for `t` distinctness tests at width `w+1` gives a batch of `t` tagged permutation tests at width `w`, of size `m + 3t·listBits(w+1)`.

**Step 1.2 (`transfer`, Reduction.lean:277).** Merge the batch into one big test. Let `v = ⌊log₂ t⌋`.
1. Keep `2^v` of the tests (`tag_truncate`).
2. Widen the payloads to width `2(w+v)` using `2^k` slices (`tag_slices`). Cost factor `≤ 21·4^k`.
3. Turn the tagged permutation tests into sorting networks for `2^v` independent lists, using a comparator network (`sort_of_tag`, Array.lean:522).
4. Merge the `2^v` sorts into one sort of `2^(w+v)` records with `j` column lifts (`sort_lift_iterate`, ColumnNetwork.lean:487). Cost factor `4^j`.
5. Turn the single sort back into one tagged permutation verifier on `2^(w+v)` rows (`tag_of_sort`, SortBack.lean:35). Cost `2m' + 3·2^w·(w + wd a)`.

Total: a `tag` network at width `w+v` of size `l ≤ 10^6·4^k·4^j·m`.

**Step 1.3 (`parameters` at Reduction.lean:31, `manyList_full` at Reduction.lean:349).** Apply Hard at width `w+v`. This gives `l ≥ 2^(w+v)·(w+v)·(w+v)^σ`, and `space` gives `t·listBits(w+1) < 100·2^(w+v)·(w+v)`.

The parameters are chosen as `η = σ/15` and `2^k ≈ 8·(w+1)^η`, `j = 2k`. Then `4^k·4^j = 2^(6k) ≤ (8(w+1)^η)^6`, so the loss in the reduction is `w^(O(η))` and is absorbed into `w^σ`. The result is `t·listBits(w+1)·(w+1)^η < m` for every `t ≤ 2^((w+1)^(1+η))`. `manyList_of_tag` (Reduction.lean:382) restricts to `t ≤ listBits w`.

Level 1 is elementary and about 400 lines. We regard it as clearly correct (it is also Lean checked). **Everything deep is in Tagged.Hard.**

### Level 2. Hard follows from Resists and Descent (Diagonal/Broadcast.lean:556, read in full)

**Definitions** (Diagonal/Bounds.lean). Write `N = 2^w`.

* **Resists F L.** For every constant `C ≥ 4` there are `k` and `δ > 0` such that for all large `w` there is a tensor `U` on at most `N` exterior bits with:
  * a network of size at most `N·w^k`, so U is quasi-linear;
  * for every `d ≤ N^δ`, every "wide" network for `U^⊗d` has size greater than `C·N·d`. Wide networks may also use the high-arity tables in `L`.
* **Descent F L.** If Hard fails, then there are `C` and `α > 0` such that for every `κ > 0` and for infinitely many `w`, every network of size `M ∈ [N, N^1.05]` (counting exterior bits) has both of the following:
  * (i) a trivalent network for `d ≤ N^κ` copies of size at most `d·(M·w^(−α) + e·w^(α/4))`;
  * (ii) a wide network for `d` copies of size at most `C·d·(M·w^(−α) + e)`.

  Here `e` is the number of exterior bits.

**The argument** (`hard_of_resists`). Suppose Hard fails. Take `C` and `α` from Descent, and take `k`, `δ` and `U` from `Resists(2C)`. Let `b = α/2`, fix `J > (k+1)/b`, and set `κ = min(δ, 1/40)/J`. Pick a `w` that is large and also one of the descent lengths.

Induction on `j ≤ J`: there are `t ≤ N^(jκ)` copies of `U` with a network of size `u` such that

`u + t·N ≤ t·N·w^(k+1−jb)`.

* *Base case.* `t = 1`, and the network for `U` has size `≤ N·w^k`.
* *Inductive step.* Let `M = u + tN`.
  * First, apply version (ii). If `t·N > M·w^(−α)`, the wide network for `t·d` copies would cost `≤ 2C·N·t·d`, which contradicts Resists. Hence `t·N ≤ M·w^(−α)`.
  * Then apply version (i). The exterior term `e·w^(α/4) ≤ t·N·w^(α/4)` is absorbed (`absorb`), so the new size is at most `d·M·w^(−b)`.
  * The copy count grows by `d ≤ N^κ`, and the total stays `≤ N^δ`.
* *Conclusion.* After `J` steps, `u + tN ≤ tN·w^(k+1−Jb) < tN`. This is impossible because `u ≥ 0`.

This is a clean diagonal contradiction: a speedup theorem against a hierarchy theorem. All of the difficulty is in the two inputs.

### Level 3. Descent from ¬Hard (BatchDescent, about 18k lines; NOT read by us)

What the statements say:

* `frequent_tags` (Dictionary.lean:378): if Hard fails, then for every `ε > 0` there are infinitely many `w` with tag networks of size at most `w^ε·2^w·w`.
* `Compilation F` (Encoded.lean:17): every network of size `M ∈ [2^w, 2^(1.05w)]` can be compiled into `d` copies that use full-length sorting gates and cheap short tables, with cost `≤ K·d·(M·w^(−a) + e)`.
* `encoded` (Compilation.lean:867) builds this from ¬Hard. It does so through `Encoded F` (Encoded.lean:496), a `Recipe` with transfer schedules over "beats", resets and trails.

Informally: if permutation routing were nearly linear, you could batch many copies of any network and route their wires cheaply, which saves a `w^(−a)` factor per copy. This corresponds to the paper's citation `[42, Proposition 14.1]` ("descent with tagged permutations"). The import closure of this level includes the Sphere, Spectral and TensorSpectrum geometry modules.

### Level 4. Resists, unconditional (Processor about 10k lines, Diagonal about 4.5k; NOT read by us)

* `resists_of_programmable` (Broadcast.lean:813): if a quasi-linear "universal processor" exists (`Programmable`), then Resists holds. The processor is a tensor `U` of size `N·w^k` that, given an encoded report of any small "machine diagram" on its tape, `Programs` the diagram and can be made to disagree with it (`S.diagonal`).
* `control` (Resistance.lean:24) proves `ControlBound` without complexity assumptions. Its docstring says "The controller and its size bound require no complexity assumptions."

This gives, unconditionally, a quasi-linear tensor whose `d`-fold power cannot be computed in linear size `C·N·d` for any fixed `C`, even by networks that share work across the copies. **We consider this the most surprising ingredient.** It is a direct product type lower bound obtained by diagonalization, and it is where an expert should look first.

## 5. Precisely what follows, and what does not

**New Lean theorem `circuit_lower`** (ListDistinct.lean:368; axioms: standard only).

*Circuit model* (ListDistinct.lean:232 to 248):
* A `Gate` is any `op : Bool → Bool → Bool` together with two positions `i, j`.
* `run` keeps a list of values, newest first. Each gate appends `op(s[i], s[j])`. Values can be read any number of times, so fan-out is unbounded.
* `WF` requires that gates read only existing values. The output is the last value computed.
* The inputs are `inputBits`, the bits of the input bundle from left to right (`inputBits_pair`, `length_inputBits`).

This is the standard B₂ circuit model with fan-in 2.

*Statement.* For every finite field `F` there is `σ > 0` such that for all large `w`:

```
∀ gs, WF gs n → (∀ x, output gs (inputBits x) = decide (records of x pairwise distinct)) →
   n·(w^σ − 3) < 3·(2n + 4·|gs| + 1),        n = listBits w = 2w·2^w.
```

Hence `|gs| > (n·w^σ − 9n − 3)/12`, which is `Ω(n·(log n)^σ)` since `w = log₂ n − O(log log n)`. Take `F = ZMod 2`.

*How it is proved.*
1. `circuit_dnet` (ListDistinct.lean:350) turns a program with `s` gates on `n` inputs into a deterministic trivalent network with at most `2n + 4s` vertices.
   * Each gate costs 3 vertices: two copy vertices and the gate table.
   * Pass-through wires cost nothing, because of `applyFst` (ListDistinct.lean:142). That lemma uses `Net.trace` to attach a small network to one output bundle without identity vertices on the others.
   * Reading the input costs `n`, and discarding the unused values at the end costs at most `n + s`.
2. `pin` adds one vertex that turns the output bit into the 0/1 tensor.
3. Then `deterministic_lower` (ListDistinct.lean:100) and `one_list_vertices` (ListDistinct.lean:54) apply `manyList` with `t = 1`.

**What follows** (conditional only on the soundness of the Lean development and the Lean kernel):
1. Element distinctness of `m = 2^w` strings of `2 log₂ m` bits needs Boolean circuits of size `Ω(n·(log n)^σ)` over the full binary basis, for some unspecified `σ > 0`. To our knowledge the best previously known explicit lower bound for general B₂ circuits is linear: `4n − O(log n)` (Mishra and Santhanam, ECCC TR26-260, revised version, https://eccc.weizmann.ac.il/report/2026/260/), improving `3.5n − o(n)` in the first version of that report, which in turn improved `3.1n − o(n)` (Li and Yang, STOC 2022). For element distinctness specifically, the known lower bounds we are aware of are time space tradeoffs for branching programs (Ajtai; Beame, Saks, Sun and Vee, JACM 2003), not superlinear size bounds for general circuits.
2. The same holds for any model that compiles into `Net` with linear overhead. This includes exact "sum over guesses in `F`" circuits, for example parity-of-witnesses circuits over `F_2`. We did not formalize this; it follows from `trace`.
3. Many-list form: networks that test `t ≤ 2^(w^(1+η))` independent lists cannot share work below `t·n·w^η`.

**What does not follow:**
1. **No explicit σ.** `Tagged.Hard` is reached by contradiction (`hard_of_resists` begins with `by_contra bad`, Broadcast.lean:557), and `frequent_tags` is also by contradiction. Nothing in the Lean proof yields a numerical σ or threshold. `manyList` takes `η = σ_Hard/15`.
2. **No new Turing machine or RAM time bounds.** Time `T` gives circuits of size `O(T log T)`, so `σ ≤ 1` gives nothing beyond linear time.
3. **Nothing about P vs NP, formulas, depth or randomized computation.** Correctness must be exact on every input.
4. **Not a sorting lower bound in comparison models.** `Ω(n log n)` for comparison and algebraic decision trees (Ben-Or) is classical and is a different model.
5. **Independent of matrix multiplication.** Nothing in `manyList` depends on ω. Matrix multiplication enters only in `Iteration.incompatible` (Seed + ManyList + Compression ⇒ False) and `Rounds/Installation.lean:22` (ω < 9/4 ⇒ Compression).
6. **Not checked with a second kernel by us.** Our file was checked only by the standard Lean 4.34.1 kernel. Carlos Toledo's three-kernel audit covered `square_exponent`, whose import closure contains the module `BatchDescent.Hard`. Our 240 new lines were not part of that audit.

## 6. Gaps between Lean and the paper

| # | Paper (Section 2.1, Theorem 2.2; Section 4) | Lean | Assessment |
|---|---|---|---|
| 1 | Volume = vertices plus all wires, including exterior; bound `vol > t·n_w·w^σ`. | `m` = vertices plus exterior bits; bound `t·n·w^σ < 3m`. | Equivalent up to constants, since in a trivalent network #wires ≤ (3v+e)/2. No gap. |
| 2 | `1 ≤ t ≤ 2^w`. | `t ≤ 2w·2^w` (`manyList`); `t ≤ 2^(w^(1+η))` (`manyList_full`). | Lean is stronger. |
| 3 | "constant σ > 0 depending only on k", k a finite field. | `∃ σ` for each `[Field F] [Finite F]`. | Matches. |
| 4 | List of `2^w` words of `2w` bits; lists may share wiring. | `lists w t = t` copies of `tree w (word 2w)`; one `Net` on all lists. | Matches. |
| 5 | Section 4 proof splits into "fields without ports" (spectral Lemma 4.1, any σ < 1/2) and "finite fields with ports" (signed counting tensor `U*_ℓ` plus companion `[43, Thm 12.1]`, exact batch bound `vol > jℓ^(1+δ)` for `j ≤ 2^(ℓ^ξ)`). | `hard` uses one route for every finite field: Descent plus `Resists`, with no ports case split at the top (Hard.lean:17). The batch lower bound used is `Resists` (linear `C·N·d`, `d ≤ N^δ`, proved through a universal processor), not the paper's `U*_ℓ` statement. | **Real gap for readers.** The paper's prose does not describe the formal proof. A human check must follow the Lean route (Section 4 above), not Section 4 of the paper. |
| 6 | Tag(h,h) with h = w − 1; reduction via two `D_w` tests (paper 4.1). | Same idea (`cancel`, `tag_of_distinct`), plus slices, sort lifts and `tag_of_sort` to merge the batch into one instance. | Lean is more detailed. Consistent. |
| 7 | Boolean circuits are used only for the upper bound (Prop. 2.3: "use the zero-one table of each gate, copy bits at fan-outs"). | Upstream Lean has no Boolean circuit statement. | Filled by our `circuit_lower`. The paper's text does not state the superlinear Boolean consequence. |
| 8 | ω enters through Theorem 2.1 (compression). | `Compression` is separate (ListBounds.lean:23); `manyList` does not use it. | Consistent. The list bound stands alone. |

## 7. Open items (honest next steps)

1. Read Level 4 (`Processor/Resistance.lean`, `Diagonal/Broadcast.lean:700 to 870`, `Processor/DispatchSize.lean`) and Level 3 (`BatchDescent/*`) as human mathematics. Mark every step that is not obvious.
2. Done in part: `lake env leanchecker ListDistinct` replays every declaration of this module through the Lean kernel and passes (`leanchecker.log`). Still open: a `--fresh` replay of the whole import closure, and a second independent kernel such as nanoda.
3. Ask an expert in circuit complexity whether a diagonal "direct product" bound as in `Resists` contradicts any known barrier.
4. Try to extract an explicit σ by making `hard_of_resists` constructive.
