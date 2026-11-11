module

public import InferenceProof.OperationalSemantics
public import Mathlib.Data.Finset.Union

set_option linter.style.header false

/-!
# Finite control locations

A continuation-passing traversal of each finite source body enumerates the
runtime code locations, including loop back edges. Recursion enters a function's
fixed body location rather than extending the current code.
-/

@[expose] public section

namespace InferenceProof.PPDA

variable {S : Signature}

theorem append_assoc (a b c : Code S) : (a.append b).append c = a.append (b.append c) := by
  induction a with
  | seq first rest ihf ihr => exact congrArg (Code.seq first) ihr
  | _ => rfl

/-- Compile a source block with its remaining code made explicit. -/
def compile (C : Stmt S) (k : Code S) : Code S := (Code.ofStmt C).append k

theorem compile_seq (a b : Stmt S) (k : Code S) :
    compile (.seq a b) k = compile a (compile b k) := append_assoc _ _ _

open scoped Classical in
/-- A finite set of code locations, including the final continuation. -/
noncomputable def locations : Stmt S → Code S → Finset (Code S)
  | .seq a b, k => locations a (compile b k) ∪ locations b k
  | .ite b t e, k => insert (compile (.ite b t e) k) (locations t k ∪ locations e k)
  | .while b body, k =>
      insert (compile (.while b body) k) (locations body (compile (.while b body) k) ∪ {k})
  | C, k => {compile C k, k}

theorem compile_mem_locations (C : Stmt S) (k : Code S) : compile C k ∈ locations C k := by
  classical
  induction C generalizing k with
  | seq a b iha ihb =>
    rw [compile_seq]
    exact Finset.mem_union_left _ (iha _)
  | ite => exact Finset.mem_insert_self _ _
  | «while» => exact Finset.mem_insert_self _ _
  | _ => exact Finset.mem_insert_self _ _

theorem continuation_mem_locations (C : Stmt S) (k : Code S) : k ∈ locations C k := by
  classical
  induction C generalizing k with
  | seq a b iha ihb => exact Finset.mem_union_right _ (ihb _)
  | ite b t e iht ihe => exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (iht _))
  | «while» =>
    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  | _ => exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The store-independent successor locations of a runtime instruction belong
to `U`. Calls, returns, queries and errors additionally use the function table
and saved continuations, handled by the stack invariant.
-/
def LocalClosed (U : Finset (Code S)) : Code S → Prop
  | .done | .ret _ | .endQuery => True
  | .seq (.stmt (.ite _ t e)) k => k ∈ U ∧ compile t k ∈ U ∧ compile e k ∈ U
  | .seq (.stmt (.while b body)) k =>
      k ∈ U ∧ compile body (.seq (.stmt (.while b body)) k) ∈ U
  | .seq (.stmt (.seq _ _)) _ => False
  | .seq (.stmt _) k => k ∈ U
  | _ => False

theorem locations_closed (C : Stmt S) (k : Code S) (U : Finset (Code S))
    (hk : LocalClosed U k) (hsub : locations C k ⊆ U) :
    ∀ c ∈ locations C k, LocalClosed U c := by
  classical
  induction C generalizing k with
  | seq a b iha ihb =>
    have ha : locations a (compile b k) ⊆ U :=
      fun _ h => hsub (Finset.mem_union_left _ h)
    have hb : locations b k ⊆ U := fun _ h => hsub (Finset.mem_union_right _ h)
    intro c hc
    rcases Finset.mem_union.mp hc with h | h
    · exact iha _ (ihb k hk hb _ (compile_mem_locations b k)) ha c h
    · exact ihb k hk hb c h
  | ite b t e iht ihe =>
    have ht : locations t k ⊆ U :=
      fun _ h => hsub (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have he : locations e k ⊆ U :=
      fun _ h => hsub (Finset.mem_insert_of_mem (Finset.mem_union_right _ h))
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | h
    · exact ⟨ht (continuation_mem_locations t k), ht (compile_mem_locations t k),
        he (compile_mem_locations e k)⟩
    · rcases Finset.mem_union.mp h with h | h
      · exact iht k hk ht c h
      · exact ihe k hk he c h
  | «while» b body ih =>
    have hb : locations body (compile (.while b body) k) ⊆ U :=
      fun _ h => hsub (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
    have hkU : k ∈ U := hsub (continuation_mem_locations (.while b body) k)
    have hloop : LocalClosed U (compile (.while b body) k) :=
      ⟨hkU, hb (compile_mem_locations body _)⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | h
    · exact hloop
    · rcases Finset.mem_union.mp h with h | h
      · exact ih _ hloop hb c h
      · exact (Finset.mem_singleton.mp h) ▸ hk
  | _ =>
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | h
    · exact hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self k))
    · exact (Finset.mem_singleton.mp h) ▸ hk

open scoped Classical in
/-- A finite closed set of control locations for the program and initial block. -/
noncomputable def codeSet (P : Program S) (C : Stmt S) : Finset (Code S) :=
  locations C .done ∪
    Finset.univ.biUnion (fun f => locations (P.functions f).body (.ret (P.functions f).out)) ∪
    {Code.done, Code.endQuery} ∪
    (Finset.univ : Finset (Var S × FunctionName S)).image
      (fun xf => Code.seq (.stmt (.call xf.1 xf.2)) .endQuery)

theorem locations_subset_codeSet (P : Program S) (C : Stmt S) :
    locations C .done ⊆ codeSet P C := by
  classical
  intro c hc
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hc))

theorem body_locations_subset_codeSet (P : Program S) (C : Stmt S) (f : FunctionName S) :
    locations (P.functions f).body (.ret (P.functions f).out) ⊆ codeSet P C := by
  classical
  intro c hc
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, hc⟩)))

theorem done_mem_codeSet (P : Program S) (C : Stmt S) : Code.done ∈ codeSet P C :=
  locations_subset_codeSet P C (continuation_mem_locations C .done)

theorem endQuery_mem_codeSet (P : Program S) (C : Stmt S) : Code.endQuery ∈ codeSet P C := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _)))

theorem queryCall_mem_codeSet (P : Program S) (C : Stmt S) (x : Var S) (f : FunctionName S) :
    Code.seq (.stmt (.call x f)) .endQuery ∈ codeSet P C := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x, f), Finset.mem_univ _, rfl⟩)

theorem codeSet_closed (P : Program S) (C : Stmt S) :
    ∀ c ∈ codeSet P C, LocalClosed (codeSet P C) c := by
  classical
  intro c hc
  rcases Finset.mem_union.mp hc with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact locations_closed C .done _ trivial (locations_subset_codeSet P C) c h
      · obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp h
        exact locations_closed (P.functions f).body (.ret (P.functions f).out) _ trivial
          (body_locations_subset_codeSet P C f) c hf
    · rcases Finset.mem_insert.mp h with rfl | h
      · trivial
      · cases Finset.mem_singleton.mp h; trivial
  · obtain ⟨⟨x, f⟩, _, rfl⟩ := Finset.mem_image.mp h
    exact endQuery_mem_codeSet P C

end InferenceProof.PPDA
