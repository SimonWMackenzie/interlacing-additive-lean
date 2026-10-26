import CurrentAdditive.IntegerBitSupport

/-! Pure semantics of a fixed-count controller for the literal independence
compression loop. Failed materialized updates use a total default, but that
default is proved unreachable for positive sources with a constant feature. -/
namespace CurrentAdditive.CodeDCompressionIteration

open IndependentSupport SequentialCode SequentialSourceCode IntegerBitSupport

def onePass? {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Option (Array (α × ℚ)) :=
  match sourceFreeColumn n φ source with
  | none => some source
  | some _ => compressSourceOnceMaterialized n φ source

def onePass {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) : Array (α × ℚ) :=
  (onePass? n φ source).getD source

theorem onePass_of_none {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source : Array (α × ℚ)) (hfree : sourceFreeColumn n φ source = none) :
    onePass n φ source = source := by
  simp [onePass, onePass?, hfree]

theorem onePass_of_step {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source next : Array (α × ℚ))
    (f : Fin (SequentialCode.columnCount (featureRows n φ source)))
    (hfree : sourceFreeColumn n φ source = some f)
    (hstep : compressSourceOnceMaterialized n φ source = some next) :
    onePass n φ source = next := by
  simp [onePass, onePass?, hfree, hstep]

/-- The total default is unreachable on the mathematical domain used by Code D. -/
theorem onePass?_eq_some {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) :
    onePass? n φ source = some (onePass n φ source) := by
  cases hf : sourceFreeColumn n φ source with
  | none => simp [onePass?, onePass, hf]
  | some f =>
      obtain ⟨next, hs⟩ := compressSourceOnce_total_of_free n φ source
        hn hconstant ⟨f, hf⟩ hpositive
      simp [onePass?, onePass, hf, hs]

theorem onePass_positive {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) :
    SourcePositive (onePass n φ source) := by
  cases hf : sourceFreeColumn n φ source with
  | none => simpa [onePass_of_none n φ source hf] using hpositive
  | some f =>
      obtain ⟨next, hs⟩ := compressSourceOnce_total_of_free n φ source
        hn hconstant ⟨f, hf⟩ hpositive
      rw [onePass_of_step n φ source next f hf hs]
      exact compressSourceOnceMaterialized_positive n φ source next hs

theorem onePass_eq_self_iff {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) :
    onePass n φ source = source ↔ sourceFreeColumn n φ source = none := by
  constructor
  · intro heq
    cases hf : sourceFreeColumn n φ source with
    | none => rfl
    | some f =>
        obtain ⟨next, hs⟩ := compressSourceOnce_total_of_free n φ source
          hn hconstant ⟨f, hf⟩ hpositive
        have hsmall := compressSourceOnceMaterialized_size_lt n φ source next hs
        rw [onePass_of_step n φ source next f hf hs] at heq
        rw [heq] at hsmall
        omega
  · exact onePass_of_none n φ source

/-- Every controller prefix has a literal trace; identity passes add no
elimination steps. The statement also covers passes after independence. -/
theorem iterate_trace {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) (t : Nat) :
    ∃ e, e ≤ t ∧ EliminationTrace n φ e source ((onePass n φ)^[t] source) := by
  induction t generalizing source with
  | zero => exact ⟨0, Nat.le_refl _, .refl source⟩
  | succ t ih =>
      cases hf : sourceFreeColumn n φ source with
      | none =>
          have hi := Function.iterate_fixed (onePass_of_none n φ source hf) (t+1)
          rw [hi]
          exact ⟨0, Nat.zero_le _, .refl source⟩
      | some f =>
          obtain ⟨next, hs⟩ := compressSourceOnce_total_of_free n φ source
            hn hconstant ⟨f, hf⟩ hpositive
          have hp := compressSourceOnceMaterialized_positive n φ source next hs
          obtain ⟨e, he, htrace⟩ := ih next hp
          rw [Function.iterate_succ_apply, onePass_of_step n φ source next f hf hs]
          exact ⟨e+1, Nat.succ_le_succ he,
            .step source next _ f e hf hs htrace⟩

theorem iterate_positive {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) (t : Nat) :
    SourcePositive ((onePass n φ)^[t] source) := by
  induction t with
  | zero => exact hpositive
  | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact onePass_positive n φ hn hconstant _ ih

/-- This comparison uses only a successful pure evaluation of the original
loop; no physical machine or execution supplier occurs in its statement. -/
theorem iterate_eq_of_compress {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ)) (fuel : Nat)
    (hcompress : compressUntilIndependent n φ source fuel = some out) :
    (onePass n φ)^[fuel] source = out := by
  induction fuel generalizing source with
  | zero =>
      cases hf : sourceFreeColumn n φ source with
      | none => simpa [compressUntilIndependent, hf] using hcompress
      | some f => simp [compressUntilIndependent, hf] at hcompress
  | succ fuel ih =>
      cases hf : sourceFreeColumn n φ source with
      | none =>
          have hs : source = out := by
            simpa [compressUntilIndependent, hf] using hcompress
          exact (Function.iterate_fixed (onePass_of_none n φ source hf) (fuel+1)).trans hs
      | some f =>
          cases hs : compressSourceOnceMaterialized n φ source with
          | none => simp [compressUntilIndependent, hf, hs] at hcompress
          | some next =>
              have hrest : compressUntilIndependent n φ next fuel = some out := by
                simpa [compressUntilIndependent, hf, hs] using hcompress
              rw [Function.iterate_succ_apply, onePass_of_step n φ source next f hf hs]
              exact ih next hrest

/-- Source-size fuel yields the original algorithm's exact output, without
assuming an output or a successful controller run. -/
theorem source_size_iteration {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) :
    compressUntilIndependent n φ source source.size =
      some ((onePass n φ)^[source.size] source) := by
  obtain ⟨out, hout⟩ := compressUntilIndependent_total n φ hn hconstant
    source hpositive source.size (Nat.le_refl _)
  rw [iterate_eq_of_compress n φ source out source.size hout]
  exact hout

/-- Independence persists through all unused fixed-count controller passes. -/
theorem source_size_stopped {α : Type*} (n : Nat) (φ : α → Fin n → ℚ)
    (hn : 0 < n) (hconstant : ∃ j : Fin n, ∀ x, φ x j = 1)
    (source : Array (α × ℚ)) (hpositive : SourcePositive source) :
    sourceFreeColumn n φ ((onePass n φ)^[source.size] source) = none := by
  obtain ⟨e, _, _, hnone⟩ := IntegerBitSupport.compressUntilIndependent_trace n φ
    source _ source.size (source_size_iteration n φ hn hconstant source hpositive)
  exact hnone

#print axioms onePass?_eq_some
#print axioms onePass_eq_self_iff
#print axioms iterate_trace
#print axioms source_size_iteration
#print axioms source_size_stopped

end CurrentAdditive.CodeDCompressionIteration
