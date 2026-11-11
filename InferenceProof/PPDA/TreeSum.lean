module

public import InferenceProof.PPDA.Paths
public import InferenceProof.PPDA.Kleene

set_option linter.style.header false

/-!
# Bounded summary derivations

Bounding derivation height, rather than full-stack path length, gives exactly
the finite iterations of the quadratic polynomial system.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

variable {Q Γ : Type*}

/-- The height of a summary derivation, counting its root. -/
def Tree.height {p : Q} {X : Γ} {q : Q} : Tree p X q → ℕ
  | .pop => 1
  | .one child => child.height + 1
  | .two left right => max left.height right.height + 1

theorem Tree.height_pos {p : Q} {X : Γ} {q : Q} (tree : Tree p X q) : 0 < tree.height := by
  cases tree <;> exact Nat.zero_lt_succ _

/-- Trees of height at most the polynomial-iteration bound. -/
abbrev BoundedTree (n : ℕ) (p : Q) (X : Γ) (q : Q) :=
  {tree : Tree p X q // tree.height ≤ n}

instance (p : Q) (X : Γ) (q : Q) : IsEmpty (BoundedTree 0 p X q) :=
  ⟨fun tree => (Nat.not_lt_of_ge tree.2) tree.1.height_pos⟩

/-- The disjoint constant, linear and quadratic cases of one tree expansion. -/
abbrev TreeExpansion (n : ℕ) (_p : Q) (_X : Γ) (q : Q) :=
  Unit ⊕ ((Σ r : Q, Σ Y : Γ, BoundedTree n r Y q) ⊕
    (Σ r : Q, Σ Y : Γ, Σ Z : Γ, Σ t : Q, BoundedTree n r Y t × BoundedTree n t Z q))

/-- Removing the root decreases the height bound by one. -/
def boundedTreeEquiv (n : ℕ) (p : Q) (X : Γ) (q : Q) :
    BoundedTree (n + 1) p X q ≃ TreeExpansion n p X q where
  toFun tree := match tree with
    | ⟨.pop, _⟩ => .inl Unit.unit
    | ⟨.one (r := r) (Y := Y) child, h⟩ =>
        .inr (.inl ⟨r, Y, child, Nat.le_of_succ_le_succ h⟩)
    | ⟨.two (r := r) (Y := Y) (Z := Z) (t := t) left right, h⟩ =>
        .inr (.inr ⟨r, Y, Z, t,
          ⟨left, (Nat.le_max_left _ _).trans (Nat.le_of_succ_le_succ h)⟩,
          ⟨right, (Nat.le_max_right _ _).trans (Nat.le_of_succ_le_succ h)⟩⟩)
  invFun expansion := match expansion with
    | .inl _ => ⟨.pop, Nat.succ_le_succ (Nat.zero_le n)⟩
    | .inr (.inl ⟨_, _, child⟩) => ⟨.one child.1, Nat.succ_le_succ child.2⟩
    | .inr (.inr ⟨_, _, _, _, left, right⟩) =>
        ⟨.two left.1 right.1, Nat.succ_le_succ (max_le left.2 right.2)⟩
  left_inv tree := by
    rcases tree with ⟨tree, h⟩
    cases tree <;> rfl
  right_inv expansion := by
    rcases expansion with ⟨⟨⟩⟩ | ⟨⟨r, Y, child⟩ | ⟨r, Y, Z, t, left, right⟩⟩ <;> rfl

variable (coeff : Q → Γ → Q → Replacement Γ → ℝ≥0∞)

/-- The sum of weights of all summary derivations below a height bound. -/
noncomputable def boundedSum (n : ℕ) : Summary Q Γ :=
  fun p X q => ∑' tree : BoundedTree n p X q, tree.1.weight coeff

theorem boundedSum_zero : boundedSum coeff 0 = ⊥ := by
  funext p X q
  exact tsum_empty

theorem boundedSum_succ [Fintype Q] [Fintype Γ] (n : ℕ) :
    boundedSum coeff (n + 1) = polynomial coeff (boundedSum coeff n) := by
  classical
  funext p X q
  unfold boundedSum
  let w : TreeExpansion n p X q → ℝ≥0∞ := fun
    | .inl _ => coeff p X q .pop
    | .inr (.inl ⟨r, Y, child⟩) => coeff p X r (.one Y) * child.1.weight coeff
    | .inr (.inr ⟨r, Y, Z, t, left, right⟩) =>
        coeff p X r (.two Y Z) * left.1.weight coeff * right.1.weight coeff
  have hw (e : TreeExpansion n p X q) :
      ((boundedTreeEquiv n p X q).symm e).1.weight coeff = w e := by
    rcases e with ⟨⟨⟩⟩ | ⟨⟨r, Y, child⟩ | ⟨r, Y, Z, t, left, right⟩⟩ <;> rfl
  rw [← (boundedTreeEquiv n p X q).symm.tsum_eq]
  trans (∑' e : TreeExpansion n p X q, w e)
  · exact tsum_congr hw
  · rw [ENNReal.summable.tsum_sum ENNReal.summable,
      ENNReal.summable.tsum_sum ENNReal.summable]
    simp only [w, ENNReal.tsum_sigma', ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    simp_rw [ENNReal.tsum_mul_left]
    simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
    dsimp only [polynomial, boundedSum]
    simp_rw [mul_assoc]
    ac_rfl

/-- Bounded derivation sums are the actual polynomial approximations. -/
theorem boundedSum_eq_approximation [Fintype Q] [Fintype Γ] (n : ℕ) :
    boundedSum coeff n = approximation coeff n := by
  induction n with
  | zero => exact boundedSum_zero coeff
  | succ n ih => rw [boundedSum_succ, approximation_succ, ih]

/-- Every finite collection of derivations has a common height bound. -/
theorem sum_tree_eq_iSup_boundedSum (p : Q) (X : Γ) (q : Q) :
    (∑' tree : Tree p X q, tree.weight coeff) = ⨆ n, boundedSum coeff n p X q := by
  classical
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    let n := s.sup (fun tree => tree.height)
    let lift : ↥s → BoundedTree n p X q :=
      fun tree => ⟨tree.1, Finset.le_sup tree.2⟩
    have hinj : Function.Injective lift := fun a b h =>
      Subtype.ext (congrArg (fun c : BoundedTree n p X q => c.1) h)
    calc
      (∑ tree ∈ s, tree.weight coeff) = ∑' tree : ↥s, tree.1.weight coeff :=
        (Finset.tsum_subtype s (fun tree => tree.weight coeff)).symm
      _ ≤ boundedSum coeff n p X q :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (fun tree => tree.1.weight coeff)
      _ ≤ ⨆ n, boundedSum coeff n p X q := le_iSup (fun k => boundedSum coeff k p X q) n
  · refine iSup_le fun n => ?_
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
      (fun tree : Tree p X q => tree.weight coeff)

/-- The least polynomial solution equals the full sum of summary derivations. -/
theorem leastSolution_eq_sum_tree [Fintype Q] [Fintype Γ] (p : Q) (X : Γ) (q : Q) :
    leastSolution coeff p X q = ∑' tree : Tree p X q, tree.weight coeff := by
  rw [sum_tree_eq_iSup_boundedSum, leastSolution_eq_iSup_approximation]
  simp only [iSup_apply, boundedSum_eq_approximation]

/-- A forest over one symbol is precisely one summary derivation. -/
def singletonForestEquiv (p : Q) (X : Γ) (q : Q) : Forest p [X] q ≃ Tree p X q where
  toFun forest := match forest with | .cons tree (.nil _) => tree
  invFun tree := .cons tree (.nil q)
  left_inv forest := by
    cases forest with
    | cons tree tail => cases tail; rfl
  right_inv _ := rfl

/-- Equivalence of the quadratic least solution and the pPDA path-sum semantics. -/
theorem leastSolution_eq_sum_path [Fintype Q] [Fintype Γ] (p : Q) (X : Γ) (q : Q) :
    leastSolution coeff p X q = ∑' path : Path p [X] q, path.weight coeff := by
  rw [sum_path_eq_sum_forest, leastSolution_eq_sum_tree]
  rw [← (singletonForestEquiv p X q).symm.tsum_eq (fun forest => forest.weight coeff)]
  apply tsum_congr
  intro tree
  exact (mul_one (tree.weight coeff)).symm

/-- The background section's termination equations compute the actual pPDA
termination-path weights, including arbitrary stack growth and recursion.
-/
theorem Automaton.terminationProbability_eq_sum_path
    [Fintype Q] [Fintype Γ] (A : Automaton Q Γ) (p : Q) (X : Γ) (q : Q) :
    A.terminationProbability p X q = ∑' path : Path p [X] q, path.weight A.weight :=
  leastSolution_eq_sum_path A.weight p X q

end InferenceProof.PPDA
