module

public import Mathlib.Data.Fin.Basic

set_option linter.style.header false

/-!
# Syntax of cpGCL

This file formalizes Section 3 of `paper/3-cprGCL.tex`. Variables and function
names range over finite sets; values range over `{0, ..., M}`. The paper leaves
the arithmetic operators unspecified, so their symbols are parameters of the
syntax and their interpretations are supplied separately.
-/

@[expose] public section

namespace InferenceProof

/-- The finite domains and the arithmetic operator symbols of a language. -/
structure Signature where
  variableCount : ℕ
  functionCount : ℕ
  maxValue : ℕ
  UnaryOp : Type
  BinaryOp : Type

abbrev Var (S : Signature) := Fin S.variableCount
abbrev FunctionName (S : Signature) := Fin S.functionCount
abbrev Value (S : Signature) := Fin (S.maxValue + 1)

/-- Arithmetic expressions also serve as guards: zero is false, nonzero is true. -/
inductive Expr (S : Signature) where
  | const (value : Value S)
  | var (name : Var S)
  | unary (op : S.UnaryOp) (arg : Expr S)
  | binary (op : S.BinaryOp) (left right : Expr S)

/-- Source statements and blocks (represented using binary sequencing).

In `randomAssign x e₁ e₂ e₃ e₄`, the probability of assigning `e₁` is
`e₂ / e₃`; otherwise `e₄` is assigned. Calls implicitly pass exactly the
callee's designated parameter variables, as required by the paper's restriction.
`observe` is unconditional rejection; `observe(b)` is derived syntax below.
-/
inductive Stmt (S : Signature) where
  | assign (target : Var S) (value : Expr S)
  | randomAssign (target : Var S) (left numerator denominator right : Expr S)
  | call (target : Var S) (callee : FunctionName S)
  | sampleQuery (target : Var S) (callee : FunctionName S)
  | ite (guard : Expr S) (thenBranch elseBranch : Stmt S)
  | while (guard : Expr S) (body : Stmt S)
  | observe
  | skip
  | seq (first rest : Stmt S)

/-- The paper's abbreviation `observe(b)`. -/
def Stmt.observeIf {S : Signature} (guard : Expr S) : Stmt S :=
  .ite guard .skip .observe

/-- A function body excludes its final, implicit `return out` statement. -/
structure FunctionDef (S : Signature) where
  parameters : List (Var S)
  out : Var S
  body : Stmt S

/-- A finite function table, with a main function and the dummy assignment variable. -/
structure Program (S : Signature) where
  functions : FunctionName S → FunctionDef S
  main : FunctionName S
  dummy : Var S

/-- The distinguished main function is `f₀` and takes no parameters. -/
def Program.WellFormed {S : Signature} (P : Program S) : Prop :=
  P.main.val = 0 ∧ (P.functions P.main).parameters = []

end InferenceProof
