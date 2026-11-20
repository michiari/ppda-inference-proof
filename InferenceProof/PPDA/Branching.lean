module

public import InferenceProof.PPDA.Paths

set_option linter.style.header false

/-!
# Rule-labelled pushdown paths

Summing the labels of enabled rules gives the transition coefficients.
The path correspondence preserves total mass when passing between rule labels
and those coefficients.
-/

@[expose] public section

open scoped ENNReal

namespace InferenceProof.PPDA

universe u

variable {Q Γ : Type*}

/-- Terminating pushdown paths retaining the individual transition instance. -/
inductive BranchPath (Edge : Q → Γ → Q → Replacement Γ → Type u) :
    Q → List Γ → Q → Type _ where
  | nil (q : Q) : BranchPath Edge q [] q
  | pop {p X r stack q} (edge : Edge p X r .pop) (rest : BranchPath Edge r stack q) :
      BranchPath Edge p (X :: stack) q
  | one {p X r Y stack q} (edge : Edge p X r (.one Y))
      (rest : BranchPath Edge r (Y :: stack) q) : BranchPath Edge p (X :: stack) q
  | two {p X r Y Z stack q} (edge : Edge p X r (.two Y Z))
      (rest : BranchPath Edge r (Y :: Z :: stack) q) : BranchPath Edge p (X :: stack) q

variable (Edge : Q → Γ → Q → Replacement Γ → Type u)

/-- The rule-instance choices decorating an unlabelled pushdown path. -/
def Decorations {p : Q} {stack : List Γ} {q : Q} : Path p stack q → Type u
  | .nil _ => PUnit.{u + 1}
  | .pop (p := p) (X := X) (r := r) rest => Edge p X r .pop × Decorations rest
  | .one (p := p) (X := X) (r := r) (Y := Y) rest =>
      Edge p X r (.one Y) × Decorations rest
  | .two (p := p) (X := X) (r := r) (Y := Y) (Z := Z) rest =>
      Edge p X r (.two Y Z) × Decorations rest

def BranchPath.forget {p : Q} {stack : List Γ} {q : Q} :
    BranchPath Edge p stack q → Σ path : Path p stack q, Decorations Edge path
  | .nil q => ⟨.nil q, PUnit.unit⟩
  | .pop edge rest => ⟨.pop rest.forget.1, edge, rest.forget.2⟩
  | .one edge rest => ⟨.one rest.forget.1, edge, rest.forget.2⟩
  | .two edge rest => ⟨.two rest.forget.1, edge, rest.forget.2⟩

def BranchPath.restore {p : Q} {stack : List Γ} {q : Q} (path : Path p stack q) :
    Decorations Edge path → BranchPath Edge p stack q :=
  match path with
  | .nil q => fun _ => .nil q
  | .pop rest => fun d => .pop d.1 (restore rest d.2)
  | .one rest => fun d => .one d.1 (restore rest d.2)
  | .two rest => fun d => .two d.1 (restore rest d.2)

theorem BranchPath.restore_forget {p : Q} {stack : List Γ} {q : Q}
    (path : BranchPath Edge p stack q) : restore Edge path.forget.1 path.forget.2 = path := by
  induction path with
  | nil => rfl
  | pop edge rest ih => exact congrArg (BranchPath.pop edge) ih
  | one edge rest ih => exact congrArg (BranchPath.one edge) ih
  | two edge rest ih => exact congrArg (BranchPath.two edge) ih

theorem BranchPath.forget_restore {p : Q} {stack : List Γ} {q : Q}
    (path : Path p stack q) (d : Decorations Edge path) :
    (restore Edge path d).forget = ⟨path, d⟩ := by
  induction path with
  | nil => cases d; rfl
  | @pop p q r X stack rest ih =>
    exact congrArg (fun z : Σ path : Path r stack q, Decorations Edge path =>
      (⟨Path.pop z.1, d.1, z.2⟩ : Σ path : Path p (X :: stack) q,
        Decorations Edge path)) (ih d.2)
  | @one p q r X Y stack rest ih =>
    exact congrArg (fun z : Σ path : Path r (Y :: stack) q, Decorations Edge path =>
      (⟨Path.one z.1, d.1, z.2⟩ : Σ path : Path p (X :: stack) q,
        Decorations Edge path)) (ih d.2)
  | @two p q r X Y Z stack rest ih =>
    exact congrArg (fun z : Σ path : Path r (Y :: Z :: stack) q, Decorations Edge path =>
      (⟨Path.two z.1, d.1, z.2⟩ : Σ path : Path p (X :: stack) q,
        Decorations Edge path)) (ih d.2)

def branchPathEquiv (p : Q) (stack : List Γ) (q : Q) :
    BranchPath Edge p stack q ≃ (Σ path : Path p stack q, Decorations Edge path) where
  toFun := BranchPath.forget Edge
  invFun d := BranchPath.restore Edge d.1 d.2
  left_inv := BranchPath.restore_forget Edge
  right_inv d := BranchPath.forget_restore Edge d.1 d.2

variable (edgeWeight : ∀ {p X r w}, Edge p X r w → ℝ≥0∞)

noncomputable def BranchPath.weight {p : Q} {stack : List Γ} {q : Q} :
    BranchPath Edge p stack q → ℝ≥0∞
  | .nil _ => 1
  | .pop edge rest => edgeWeight edge * rest.weight
  | .one edge rest => edgeWeight edge * rest.weight
  | .two edge rest => edgeWeight edge * rest.weight

noncomputable def aggregatedWeight (p : Q) (X : Γ) (r : Q) (w : Replacement Γ) : ℝ≥0∞ :=
  ∑' edge : Edge p X r w, edgeWeight edge

theorem sum_decorations {p : Q} {stack : List Γ} {q : Q} (path : Path p stack q) :
    (∑' d : Decorations Edge path, (BranchPath.restore Edge path d).weight Edge edgeWeight) =
      path.weight (aggregatedWeight Edge edgeWeight) := by
  induction path with
  | nil => simp only [Decorations, BranchPath.restore, BranchPath.weight,
      Path.weight, tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
  | pop rest ih =>
    change (∑' d : _ × _, edgeWeight d.1 *
      (BranchPath.restore Edge rest d.2).weight Edge edgeWeight) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rfl
  | one rest ih =>
    change (∑' d : _ × _, edgeWeight d.1 *
      (BranchPath.restore Edge rest d.2).weight Edge edgeWeight) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rfl
  | two rest ih =>
    change (∑' d : _ × _, edgeWeight d.1 *
      (BranchPath.restore Edge rest d.2).weight Edge edgeWeight) = _
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right]
    rfl

/-- Branch aggregation commutes with summing all finite terminating paths. -/
theorem sum_branchPath_eq_sum_path (p : Q) (stack : List Γ) (q : Q) :
    (∑' path : BranchPath Edge p stack q, path.weight Edge edgeWeight) =
      ∑' path : Path p stack q, path.weight (aggregatedWeight Edge edgeWeight) := by
  rw [← (branchPathEquiv Edge p stack q).symm.tsum_eq]
  rw [ENNReal.tsum_sigma']
  exact tsum_congr fun path => sum_decorations Edge edgeWeight path

end InferenceProof.PPDA
