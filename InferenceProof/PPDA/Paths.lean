module

public import InferenceProof.PPDA.Basic

set_option linter.style.header false

/-!
# First-return decomposition of terminating pushdown paths

Finite paths to the empty stack are in bijection with forests of summary
derivations. A binary node records the unique intermediate state at which the
first pushed symbol has been removed. Zero-coeff table entries are allowed
in the path type; they contribute zero to weighted sums.
-/

@[expose] public section

namespace InferenceProof.PPDA

variable {Q Γ : Type*}

/-- Small-step paths from `(p, stack)` to `(q, [])`, recording every table entry. -/
inductive Path : Q → List Γ → Q → Type _ where
  | nil (q : Q) : Path q [] q
  | pop {p q r X stack} (rest : Path r stack q) : Path p (X :: stack) q
  | one {p q r X Y stack} (rest : Path r (Y :: stack) q) : Path p (X :: stack) q
  | two {p q r X Y Z stack} (rest : Path r (Y :: Z :: stack) q) : Path p (X :: stack) q

/-- A derivation of the summary variable `[p X | q]`. -/
inductive Tree : Q → Γ → Q → Type _ where
  | pop {p X q} : Tree p X q
  | one {p X q r Y} (child : Tree r Y q) : Tree p X q
  | two {p X q r Y Z t} (left : Tree r Y t) (right : Tree t Z q) : Tree p X q

/-- One summary derivation for each symbol in the initial stack, in pop order. -/
inductive Forest : Q → List Γ → Q → Type _ where
  | nil (q : Q) : Forest q [] q
  | cons {p X t stack q} (head : Tree p X t) (tail : Forest t stack q) :
      Forest p (X :: stack) q

/-- First-return parsing of a terminating small-step path. -/
def Path.toForest {p : Q} {stack : List Γ} {q : Q} : Path p stack q → Forest p stack q
  | .nil q => .nil q
  | .pop rest => .cons .pop rest.toForest
  | .one rest => match rest.toForest with
      | .cons child tail => .cons (.one child) tail
  | .two rest => match rest.toForest with
      | .cons left (.cons right tail) => .cons (.two left right) tail

/-- Execute a summary derivation above an arbitrary remaining stack and path. -/
def Tree.prepend {p : Q} {X : Γ} {q : Q} (tree : Tree p X q)
    {stack : List Γ} {target : Q} (rest : Path q stack target) : Path p (X :: stack) target :=
  match tree with
  | .pop => .pop rest
  | .one child => .one (child.prepend rest)
  | .two left right => .two (left.prepend (right.prepend rest))

/-- Linearize the forest into the original small-step order. -/
def Forest.toPath {p : Q} {stack : List Γ} {q : Q} : Forest p stack q → Path p stack q
  | .nil q => .nil q
  | .cons tree tail => tree.prepend tail.toPath

theorem Tree.toForest_prepend {p : Q} {X : Γ} {q : Q} (tree : Tree p X q)
    {stack : List Γ} {target : Q} (rest : Path q stack target) :
    (tree.prepend rest).toForest = .cons tree rest.toForest := by
  induction tree generalizing stack target with
  | pop => rfl
  | one child ih => simp only [Tree.prepend, Path.toForest, ih]
  | two left right ihl ihr => simp only [Tree.prepend, Path.toForest, ihl, ihr]

theorem Forest.toForest_toPath {p : Q} {stack : List Γ} {q : Q}
    (forest : Forest p stack q) : forest.toPath.toForest = forest := by
  induction forest with
  | nil => rfl
  | cons tree tail ih => simp only [Forest.toPath, Tree.toForest_prepend, ih]

theorem Path.toPath_toForest {p : Q} {stack : List Γ} {q : Q}
    (path : Path p stack q) : path.toForest.toPath = path := by
  induction path with
  | nil => rfl
  | pop rest ih => simp only [Path.toForest, Forest.toPath, Tree.prepend, ih]
  | one rest ih =>
    cases h : rest.toForest with
    | cons child tail =>
      simp only [h, Forest.toPath] at ih
      simp only [Path.toForest, h, Forest.toPath, Tree.prepend, ih]
  | two rest ih =>
    cases h : rest.toForest with
    | cons left tail =>
      cases tail with
      | cons right tail =>
        simp only [h, Forest.toPath] at ih
        simp only [Path.toForest, h, Forest.toPath, Tree.prepend, ih]

/-- The first-return decomposition is lossless and has no path multiplicities. -/
def pathForestEquiv (p : Q) (stack : List Γ) (q : Q) : Path p stack q ≃ Forest p stack q where
  toFun := Path.toForest
  invFun := Forest.toPath
  left_inv := Path.toPath_toForest
  right_inv := Forest.toForest_toPath

open scoped ENNReal

variable (coeff : Q → Γ → Q → Replacement Γ → ℝ≥0∞)

/-- Product of coefficients along a terminating small-step path. -/
noncomputable def Path.weight {p : Q} {stack : List Γ} {q : Q} : Path p stack q → ℝ≥0∞
  | .nil _ => 1
  | .pop (p := p) (X := X) (r := r) rest => coeff p X r .pop * rest.weight
  | .one (p := p) (X := X) (r := r) (Y := Y) rest =>
      coeff p X r (.one Y) * rest.weight
  | .two (p := p) (X := X) (r := r) (Y := Y) (Z := Z) rest =>
      coeff p X r (.two Y Z) * rest.weight

/-- Product of coefficients in a summary derivation. -/
noncomputable def Tree.weight {p : Q} {X : Γ} {q : Q} : Tree p X q → ℝ≥0∞
  | .pop (p := p) (X := X) (q := q) => coeff p X q .pop
  | .one (p := p) (X := X) (r := r) (Y := Y) child =>
      coeff p X r (.one Y) * child.weight
  | .two (p := p) (X := X) (r := r) (Y := Y) (Z := Z) left right =>
      coeff p X r (.two Y Z) * left.weight * right.weight

/-- Product of successive summary-derivation weights. -/
noncomputable def Forest.weight {p : Q} {stack : List Γ} {q : Q} : Forest p stack q → ℝ≥0∞
  | .nil _ => 1
  | .cons tree tail => tree.weight coeff * tail.weight

theorem Tree.weight_prepend {p : Q} {X : Γ} {q : Q} (tree : Tree p X q)
    {stack : List Γ} {target : Q} (rest : Path q stack target) :
    (tree.prepend rest).weight coeff = tree.weight coeff * rest.weight coeff := by
  induction tree generalizing stack target with
  | pop => rfl
  | one child ih => simp only [Tree.prepend, Path.weight, Tree.weight, ih, mul_assoc]
  | two left right ihl ihr =>
    simp only [Tree.prepend, Path.weight, Tree.weight, ihl, ihr, mul_assoc]

theorem Forest.weight_toPath {p : Q} {stack : List Γ} {q : Q}
    (forest : Forest p stack q) : forest.toPath.weight coeff = forest.weight coeff := by
  induction forest with
  | nil => rfl
  | cons tree tail ih => simp only [Forest.toPath, Tree.weight_prepend, Forest.weight, ih]

theorem Path.weight_toForest {p : Q} {stack : List Γ} {q : Q}
    (path : Path p stack q) : path.toForest.weight coeff = path.weight coeff := by
  rw [← Forest.weight_toPath, Path.toPath_toForest]

/-- First-return decomposition preserves the entire sum, not just individual paths. -/
theorem sum_path_eq_sum_forest (p : Q) (stack : List Γ) (q : Q) :
    (∑' path : Path p stack q, path.weight coeff) =
      ∑' forest : Forest p stack q, forest.weight coeff := by
  rw [← (pathForestEquiv p stack q).tsum_eq (fun forest => forest.weight coeff)]
  exact tsum_congr fun path => (path.weight_toForest coeff).symm

end InferenceProof.PPDA
