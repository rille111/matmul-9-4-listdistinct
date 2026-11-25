import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Hard
import OAI.LinearAlgebra.MatrixExponent.Distinctness

/-!
# List distinctness lower bound: standalone restatement and corollaries

Independent restatement (Rickard Robin, 2026-11-25) of the many-list
lower bound `OAI.LinearAlgebra.MatrixExponent.BatchDescent.manyList`
from openai/math (paper: "The matrix multiplication exponent is nine
fourths", Theorem 2.2).

Sections 1 to 5 add no new mathematics. Section 6 is a new (routine) formal
derivation: Boolean straight-line programs embed into the network model with
linear overhead, so the bound becomes a Boolean circuit lower bound. The point is
1. to state the bound with the OAI wrapper predicates (`ManyList`,
   `Realizes`, `listBits`) unfolded, so a reader only has to trust the
   network model `Net` and the target tensor `distinctPower`;
2. to derive the single-list and the deterministic-gate ("Boolean
   network") forms that the superlinear-lower-bound reading relies on;
3. to record the matching O(n w^2) upper bound, so the bound is visibly
   non-vacuous;
4. to print the axioms of each statement;
5. to prove, in Lean, the Boolean circuit corollary `circuit_lower`.

Build: lake env lean ListDistinct.lean inside a checkout of openai/math's Lean
project (Lean v4.34.1, Mathlib d13f23b7) with all OAI modules built.
-/

namespace ListDistinctExposition

open OAI.LinearAlgebra.MatrixExponent Filter

/-! ## 1. The bound with wrappers unfolded -/

/-- `BatchDescent.manyList` with `ManyList`, `Realizes`, `listBits` unfolded.
`lists w t` is `t` independent lists, each a binary tree of `2^w` records of
`2*w` bits. `distinctPower F w t x` is the product over the `t` lists of the
indicator "the records of this list are pairwise distinct". `v` counts vertices
(tables of arity at most 3); the size `m` adds the `t * 2w * 2^w` exterior bits. -/
theorem manyList_unfolded (F : Type) [Field F] [Finite F] :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
      1 ≤ t → t ≤ 2 * w * 2 ^ w →
      (∃ v, Net F (lists w t) .unit (fun x _ => distinctPower F w t x) v ∧
        m = v + t * (2 * w * 2 ^ w)) →
      (t : ℝ) * ((2 * w * 2 ^ w : ℕ) : ℝ) * (w : ℝ) ^ σ < 3 * m :=
  BatchDescent.manyList F

/-- The stronger version proved in the same file: batch sizes up to
`2^(w^(1+η))`, and no factor 3. -/
theorem manyList_full_unfolded (F : Type) [Field F] [Finite F] :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ w : ℕ in atTop, ∀ t m : ℕ,
      1 ≤ t → (t : ℝ) ≤ (2 : ℝ) ^ ((w : ℝ) ^ (1 + η)) →
      (∃ v, Net F (lists w t) .unit (fun x _ => distinctPower F w t x) v ∧
        m = v + t * (2 * w * 2 ^ w)) →
      (t : ℝ) * ((2 * w * 2 ^ w : ℕ) : ℝ) * (w : ℝ) ^ η < m :=
  BatchDescent.manyList_full F

/-! ## 2. One list, counted in vertices -/

theorem one_list_vertices (F : Type) [Field F] [Finite F] :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ v : ℕ,
      Net F (lists w 1) .unit (fun x _ => distinctPower F w 1 x) v →
      ((listBits w : ℕ) : ℝ) * ((w : ℝ) ^ σ - 3) < 3 * v := by
  obtain ⟨σ, hσ, h⟩ := BatchDescent.manyList F
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [h, eventually_ge_atTop 1] with w hw hw1 v hv
  have hL : 1 ≤ listBits w := by
    unfold listBits
    exact Nat.mul_pos (Nat.mul_pos two_pos hw1) (Nat.two_pow_pos w)
  have key := hw 1 (v + 1 * listBits w) le_rfl hL ⟨v, hv, rfl⟩
  push_cast at key
  have e : ((listBits w : ℕ) : ℝ) * ((w : ℝ) ^ σ - 3)
      = 1 * (listBits w : ℝ) * (w : ℝ) ^ σ - 3 * (listBits w : ℝ) := by ring
  rw [e]
  linarith

/-! ## 3. Deterministic gate networks

`DNet F a b f m` (OAI.FunctionNetwork) says the 0/1 graph tensor of the
function `f` has a network with at most `m` vertices. Any fan-in-2 Boolean
gate and any fan-out-2 copy is a single table vertex, see `gate` and `copy`
below. -/

theorem gate (F : Type) [Field F] (op : Bool → Bool → Bool) :
    DNet F (.pair .bit .bit) .bit (fun x => op x.1 x.2) 1 :=
  DNet.table F _ _ _ (by decide)

theorem copy (F : Type) [Field F] :
    DNet F .bit (.pair .bit .bit) (fun x => (x, x)) 1 :=
  DNet.table F _ _ _ (by decide)

/-- Turning a deterministic network with one output bit into the 0/1 tensor
costs one more vertex (same proof as the private `pin` in Distinctness.lean). -/
theorem pin (F : Type) [Field F] {a : Wire} {f : Val a → Bool} {m : ℕ}
    (h : DNet F a .bit f m) :
    ∃ v ≤ m + 1, Net F a .unit (fun x _ => if f x = true then 1 else 0) v := by
  obtain ⟨v, hv, h⟩ := h
  refine ⟨v + 1, Nat.add_le_add_right hv 1, ?_⟩
  have ht := Net.table (F := F) .bit .unit (fun b _ => if b = true then 1 else 0) (by decide)
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using h.comp ht

/-- Any deterministic trivalent network computing element distinctness of
`2^w` records of `2w` bits needs more than `listBits w * (w^σ - 3)/3 - 1`
vertices. -/
theorem deterministic_lower (F : Type) [Field F] [Finite F] :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ m : ℕ,
      DNet F (tree w (word (2 * w))) .bit (fun x => decide (flatten w x).Nodup) m →
      ((listBits w : ℕ) : ℝ) * ((w : ℝ) ^ σ - 3) < 3 * ((m : ℝ) + 1) := by
  obtain ⟨σ, hσ, h⟩ := one_list_vertices F
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [h] with w hw m hm
  obtain ⟨v, hv, hn⟩ := pin F hm
  have hn' : Net F (lists w 1) .unit (fun x _ => distinctPower F w 1 x) v := by
    simpa only [distinctPower, mul_one, decide_eq_true_eq] using hn.pre (.unit _)
  have := hw v hn'
  have hv' : (v : ℝ) ≤ m + 1 := by exact_mod_cast hv
  linarith

/-! ## 4. Matching upper bound (non-vacuity) -/

theorem upper (F : Type) [Field F] :
    ∃ C : ℝ, ∀ᶠ w : ℕ in atTop, ∃ m : ℕ,
      Realizes F w 1 m ∧ (m : ℝ) ≤ C * listBits w * (w : ℝ) ^ 2 :=
  seed F

/-! ## 5. The hypothesis the bound is derived from -/

theorem tagged_hard (F : Type) [Field F] [Finite F] :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ m,
      Net F (Tagged.inputs w (word w)) .unit (Tagged.tag F w (word w)) m →
      (2 : ℝ) ^ w * w * (w : ℝ) ^ σ ≤ m :=
  BatchDescent.hard F


/-! ## 6. Boolean circuits (straight-line programs) embed with linear overhead

This section is new (not in openai/math). It turns `deterministic_lower` into a
statement about ordinary fan-in-2 Boolean circuits over the full binary basis
with unbounded fan-out. The key device is `applyFst`: using `Net.trace`, a small
network can be attached to one output bundle without paying for identity wires
on the other bundles. -/

section Circuits

variable {F : Type} [Field F]

theorem applyFst {X b c r : Wire} {f : Val X → Val (.pair b r)} {h : Val b → Val c} {m n : ℕ}
    (N : DNet F X (.pair b r) f m) (g : DNet F b c h n) :
    DNet F X (.pair c r) (fun x => (h (f x).1, (f x).2)) (m + n) := by
  obtain ⟨v, hv, N⟩ := N
  obtain ⟨u, hu, G⟩ := g
  have σR : Rewire (.pair (.pair c r) b) (.pair (.pair b r) c)
      (fun y => ((y.2, y.1.2), y.1.1)) :=
    (Rewire.assoc c r b).comp ((Rewire.swap c (.pair r b)).comp ((Rewire.swap r b).par (Rewire.id c)))
  have T := ((N.par G).post σR).trace
  refine ⟨v + u, Nat.add_le_add hv hu, ?_⟩
  convert T using 1
  funext x y
  obtain ⟨y1, y2⟩ := y
  simp only
  rw [Finset.sum_eq_single (f x).1]
  · by_cases e2 : (f x).2 = y2
    · subst e2
      by_cases e1 : h (f x).1 = y1
      · subst e1
        simp
      · have h2 : ¬ (h (f x).1, (f x).2) = (y1, (f x).2) := fun he => e1 (congrArg Prod.fst he)
        simp [e1, h2]
    · have h1 : ¬ f x = ((f x).1, y2) := fun he => e2 (by rw [he])
      have h2 : ¬ (h (f x).1, (f x).2) = (y1, y2) := fun he => e2 (congrArg Prod.snd he)
      simp [h1, h2]
  · intro z _ hz
    have : ¬ f x = (z, y2) := fun he => hz (by rw [he])
    simp [this]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-! ### Words as lists -/

def toL : (k : ℕ) → Val (word k) → List Bool
  | 0, _ => []
  | k + 1, x => x.1 :: toL k x.2

def getW : (k : ℕ) → ℕ → Val (word k) → Bool
  | 0, _, _ => false
  | _ + 1, 0, x => x.1
  | k + 1, i + 1, x => getW k i x.2

theorem getW_eq : (k i : ℕ) → (x : Val (word k)) → getW k i x = (toL k x).getD i false
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | k + 1, i + 1, x => getW_eq k i x.2

def eraseW : (k : ℕ) → ℕ → Val (word (k + 1)) → Val (word k)
  | _, 0, x => x.2
  | 0, _ + 1, _ => ()
  | k + 1, i + 1, x => (x.1, eraseW k i x.2)

def insertW : (k : ℕ) → ℕ → Bool → Val (word k) → Val (word (k + 1))
  | _, 0, b, x => (b, x)
  | 0, _ + 1, b, x => (b, x)
  | k + 1, i + 1, b, x => (x.1, insertW k i b x.2)

theorem insert_erase : (k i : ℕ) → i ≤ k → (x : Val (word (k + 1))) →
    insertW k i (getW (k + 1) i x) (eraseW k i x) = x
  | k, 0, _, _ => by cases k <;> rfl
  | 0, _ + 1, h, _ => absurd h (by omega)
  | k + 1, i + 1, h, x => by
    change (x.1, insertW k i (getW (k + 1) i x.2) (eraseW k i x.2)) = x
    rw [insert_erase k i (by omega) x.2]

theorem rewire_pull : (k i : ℕ) → i ≤ k →
    Rewire (word (k + 1)) (.pair .bit (word k)) (fun x => (getW (k + 1) i x, eraseW k i x))
  | k, 0, _ => by cases k <;> exact Rewire.id _
  | 0, _ + 1, h => absurd h (by omega)
  | k + 1, i + 1, h =>
    (((Rewire.id .bit).par (rewire_pull k i (by omega))).comp (Rewire.assoc' .bit .bit (word k))).comp
      (((Rewire.swap .bit .bit).par (Rewire.id (word k))).comp (Rewire.assoc .bit .bit (word k)))

theorem rewire_push : (k i : ℕ) → i ≤ k →
    Rewire (.pair .bit (word k)) (word (k + 1)) (fun p => insertW k i p.1 p.2)
  | k, 0, _ => by cases k <;> exact Rewire.id _
  | 0, _ + 1, h => absurd h (by omega)
  | k + 1, i + 1, h =>
    ((Rewire.assoc' .bit .bit (word k)).comp ((Rewire.swap .bit .bit).par (Rewire.id (word k)))).comp
      ((Rewire.assoc .bit .bit (word k)).comp ((Rewire.id .bit).par (rewire_push k i (by omega))))

/-- Copy the value at position `i` to the front, at the cost of one vertex. -/
theorem copyAt {X : Wire} {k m : ℕ} {f : Val X → Val (word (k + 1))} (i : ℕ) (hi : i ≤ k)
    (N : DNet F X (word (k + 1)) f m) :
    DNet F X (word (k + 2)) (fun x => (getW (k + 1) i (f x), f x)) (m + 1) := by
  have A := applyFst (N.post (rewire_pull k i hi)) (DNet.table F .bit (.pair .bit .bit) (fun z => (z, z)) (by decide))
  have B := A.post ((Rewire.assoc .bit .bit (word k)).comp ((Rewire.id .bit).par (rewire_push k i hi)))
  convert B using 2 with x
  simp only [insert_erase k i hi]

structure Gate where
  op : Bool → Bool → Bool
  i : ℕ
  j : ℕ

/-- A straight-line program. The value list is kept newest first; gate inputs
are positions in the current list. Every value may be read any number of times. -/
def run : List Gate → List Bool → List Bool
  | [], s => s
  | g :: gs, s => run gs (g.op (s.getD g.i false) (s.getD g.j false) :: s)

/-- Gates only read existing values. -/
def WF : List Gate → ℕ → Prop
  | [], _ => True
  | g :: gs, k => g.i < k ∧ g.j < k ∧ WF gs (k + 1)

def output (gs : List Gate) (s : List Bool) : Bool := (run gs s).headD false

theorem gateStep {X : Wire} {k m : ℕ} {f : Val X → Val (word (k + 1))} (g : Gate)
    (hi : g.i ≤ k) (hj : g.j ≤ k) (N : DNet F X (word (k + 1)) f m) :
    DNet F X (word (k + 2))
      (fun x => (g.op (getW (k + 1) g.i (f x)) (getW (k + 1) g.j (f x)), f x)) (m + 3) := by
  have c1 := copyAt g.i hi N
  have c2 := copyAt (g.j + 1) (by omega) c1
  have c3 := applyFst (c2.post (Rewire.assoc' .bit .bit (word (k + 1))))
    (DNet.table F (.pair .bit .bit) .bit (fun p => g.op p.2 p.1) (by decide))
  exact c3

theorem simulate {X : Wire} : (gs : List Gate) → (k m : ℕ) → (f : Val X → Val (word (k + 1))) →
    DNet F X (word (k + 1)) f m → WF gs (k + 1) →
    ∃ k' g, k' = k + gs.length ∧ DNet F X (word (k' + 1)) g (m + 3 * gs.length) ∧
      ∀ x, toL (k' + 1) (g x) = run gs (toL (k + 1) (f x))
  | [], k, m, f, N, _ => ⟨k, f, rfl, N, fun _ => rfl⟩
  | g :: gs, k, m, f, N, hw => by
    obtain ⟨hi, hj, hw'⟩ := hw
    have S := gateStep g (by omega) (by omega) N
    obtain ⟨k', g', hk, N', hg⟩ := simulate gs (k + 1) (m + 3) _ S hw'
    refine ⟨k', g', by simp [hk]; omega, N'.mono (by simp; ring_nf; omega), fun x => ?_⟩
    rw [hg x]
    simp only [run, toL, getW_eq]

/-! ### Reading the input bits into a word -/

def wl : Wire → ℕ
  | .bit => 1
  | .unit => 0
  | .pair a b => wl b + wl a

def app : (p q : ℕ) → Val (.pair (word p) (word q)) → Val (word (q + p))
  | 0, _, x => x.2
  | p + 1, q, x => (x.1.1, app p q (x.1.2, x.2))

theorem rewire_app : (p q : ℕ) → Rewire (.pair (word p) (word q)) (word (q + p)) (app p q)
  | 0, q => (Rewire.swap .unit (word q)).comp (Rewire.unit (word q))
  | p + 1, q => (Rewire.assoc .bit (word p) (word q)).comp ((Rewire.id .bit).par (rewire_app p q))

theorem toL_app : (p q : ℕ) → (x : Val (.pair (word p) (word q))) →
    toL (q + p) (app p q x) = toL p x.1 ++ toL q x.2
  | 0, _, _ => rfl
  | p + 1, q, x => by
    change x.1.1 :: toL (q + p) (app p q (x.1.2, x.2)) = x.1.1 :: (toL p x.1.2 ++ toL q x.2)
    rw [toL_app p q]

def toW : (a : Wire) → Val a → Val (word (wl a))
  | .bit, x => (x, ())
  | .unit, _ => ()
  | .pair a b, x => app (wl a) (wl b) (toW a x.1, toW b x.2)

theorem rewire_toW : (a : Wire) → Rewire a (word (wl a)) (toW a)
  | .bit => Rewire.unit' .bit
  | .unit => Rewire.id .unit
  | .pair a b => ((rewire_toW a).par (rewire_toW b)).comp (rewire_app (wl a) (wl b))

/-- The input bits of a bundle, left to right. -/
def inputBits (a : Wire) (x : Val a) : List Bool := toL (wl a) (toW a x)

theorem inputBits_pair (a b : Wire) (x : Val (.pair a b)) :
    inputBits (.pair a b) x = inputBits a x.1 ++ inputBits b x.2 :=
  toL_app (wl a) (wl b) _

theorem wl_eq_wd : (a : Wire) → wl a = wd a
  | .bit => rfl
  | .unit => rfl
  | .pair a b => by simp only [wl, wd, wl_eq_wd a, wl_eq_wd b]; omega

theorem length_inputBits (a : Wire) (x : Val a) : (inputBits a x).length = wd a := by
  rw [← wl_eq_wd]
  unfold inputBits
  generalize toW a x = y
  generalize wl a = k at y
  induction k with
  | zero => rfl
  | succ k ih => simp [toL, ih]

theorem run_dnet {X : Wire} (gs : List Gate) (n : ℕ) (φ : Val X → Val (word n))
    (hφ : Rewire X (word n) φ) (hn : 1 ≤ n) (hw : WF gs n) :
    DNet F X .bit (fun x => output gs (toL n (φ x))) (wd X + n + 4 * gs.length) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have I : DNet F X (word (k + 1)) φ (wd X) := (DNet.id F X).post hφ
  obtain ⟨k', g, hk, N, hg⟩ := simulate gs k (wd X) φ I hw
  have A := applyFst (N.post (Rewire.swap .bit (word k'))) (DNet.discard F (word k'))
  have B := A.post ((Rewire.swap .unit .bit).comp (Rewire.unit .bit))
  have hout : ∀ x, (g x).1 = output gs (toL (k + 1) (φ x)) := by
    intro x
    unfold output
    rw [← hg x]
    rfl
  have hc : wd X + 3 * gs.length + wd (word k') ≤ wd X + (k + 1) + 4 * gs.length := by
    rw [wd_word, hk]
    omega
  have B' : DNet F X .bit (fun x => output gs (toL (k + 1) (φ x)))
      (wd X + 3 * gs.length + wd (word k')) := by
    convert B using 2 with x
    exact (hout x).symm
  exact B'.mono hc

/-- Every Boolean straight-line program with `n ≥ 1` inputs and `s` gates gives a
deterministic trivalent network with at most `2n + 4s` vertices. -/
theorem circuit_dnet {X : Wire} (gs : List Gate) (hX : 1 ≤ wd X) (hw : WF gs (wd X)) :
    DNet F X .bit (fun x => output gs (inputBits X x)) (2 * wd X + 4 * gs.length) := by
  have h := run_dnet (F := F) gs (wl X) (toW X) (rewire_toW X) (by rw [wl_eq_wd]; exact hX)
    (by rw [wl_eq_wd]; exact hw)
  exact h.mono (by rw [wl_eq_wd]; omega)

end Circuits

theorem wd_tree_list (w : ℕ) : wd (tree w (word (2 * w))) = listBits w := by
  have := wd_lists w 1
  simpa [lists, wd] using this

/-- **Boolean circuit form.** For every finite field `F` there is `σ > 0` such
that, for all large `w`, every fan-in-2 Boolean straight-line program (any
binary gates, unbounded fan-out) with `s` gates that decides whether `2^w`
records of `2w` bits are pairwise distinct satisfies
`n * (w^σ - 3) < 3 * (2n + 4s + 1)`, where `n = 2w * 2^w` is the number of
input bits. Hence `s = Ω(n * (log n)^σ)`. -/
theorem circuit_lower (F : Type) [Field F] [Finite F] :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ w : ℕ in atTop, ∀ gs : List Gate,
      WF gs (listBits w) →
      (∀ x : Val (tree w (word (2 * w))),
        output gs (inputBits _ x) = decide (flatten w x).Nodup) →
      ((listBits w : ℕ) : ℝ) * ((w : ℝ) ^ σ - 3)
        < 3 * (2 * (listBits w : ℝ) + 4 * gs.length + 1) := by
  obtain ⟨σ, hσ, h⟩ := deterministic_lower F
  refine ⟨σ, hσ, ?_⟩
  filter_upwards [h, eventually_ge_atTop 1] with w hw hw1 gs hwf hc
  have hT := wd_tree_list w
  have hL : 1 ≤ listBits w := by
    unfold listBits
    exact Nat.mul_pos (Nat.mul_pos two_pos hw1) (Nat.two_pow_pos w)
  have D := circuit_dnet (F := F) (X := tree w (word (2 * w))) gs (by rw [hT]; exact hL)
    (by rw [hT]; exact hwf)
  have D' : DNet F (tree w (word (2 * w))) .bit (fun x => decide (flatten w x).Nodup)
      (2 * wd (tree w (word (2 * w))) + 4 * gs.length) := by
    convert D using 2 with x
    exact (hc x).symm
  have := hw _ D'
  rw [hT] at this
  push_cast at this
  linarith

end ListDistinctExposition

#print axioms ListDistinctExposition.manyList_unfolded
#print axioms ListDistinctExposition.manyList_full_unfolded
#print axioms ListDistinctExposition.one_list_vertices
#print axioms ListDistinctExposition.gate
#print axioms ListDistinctExposition.copy
#print axioms ListDistinctExposition.pin
#print axioms ListDistinctExposition.deterministic_lower
#print axioms ListDistinctExposition.upper
#print axioms ListDistinctExposition.tagged_hard
#print axioms OAI.LinearAlgebra.MatrixExponent.BatchDescent.manyList
#print axioms OAI.LinearAlgebra.MatrixExponent.BatchDescent.hard
#check @ListDistinctExposition.deterministic_lower
#check @ListDistinctExposition.circuit_lower
#print axioms ListDistinctExposition.circuit_dnet
#print axioms ListDistinctExposition.circuit_lower
#print ListDistinctExposition.run
#print ListDistinctExposition.WF
#print ListDistinctExposition.output
#print OAI.LinearAlgebra.MatrixExponent.Net
#print OAI.LinearAlgebra.MatrixExponent.Realizes
#print OAI.LinearAlgebra.MatrixExponent.ManyList
#print OAI.LinearAlgebra.MatrixExponent.Tagged.Hard
