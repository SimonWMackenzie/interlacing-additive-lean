import EthInapproximability.CurrentPaper.GenericPrefixAmbientInstall
import EthInapproximability.CurrentPaper.SourceGenericPrefixCompositePolynomial

/-!
# One fixed-`(a,q)` ambient prefix program (unit 1, segment 1)

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B's
bit-model implementation; ledger CP-SOURCE-EFFECTIVE, generic alphabet.

ONE fixed program on the ambient bank `PrefixAmbientCopy.Stack q`, whose raw
part is the first-row controller bank. It

1. physically copies the unary vertex word `true^n` from the staged writer
   vertex cell into the side work bank (`PrefixAmbientWork.nProgram`);
2. runs the checked generic prefix work program
   (`PrefixComposite.program a q`: every at-least-one chain, the transfer,
   then every ordered pair `(s,t) : Fin a × Fin a` including diagonals);
3. physically copies the reversed prefix clause bytes and the unary clause
   count back into the staged writer `saved`/`count` cells
   (`PrefixAmbientInstall.program q`).

All three handoffs are charged. The alphabet is an arbitrary fixed `a`; no
`a = 2`, positivity, supplied output, prepared bank or runtime premise is used.
The finite control depends only on `(a,q)`; `n` and all words are physically
processed.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.PrefixAmbientProgram

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericPrefixMachine
open PrefixAmbientCopy PrefixAmbientSeed PrefixAmbientWork PrefixAmbientInstall
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF SourceGenericPrefix
open scoped Classical

/-- Work phase followed by the install phase. -/
noncomputable def tailProgram (a q : Nat) :=
  BitMachineRawSequence.program (workProgram a q) (PrefixAmbientInstall.program q)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((((AtLeastLoopCallback.callback a q).initial, none), ((none, none), none)),
      ((PairVertexLoopCallback.routine a q).initial, none))
    (none, none)

/-- The single fixed-`(a,q)` ambient prefix program: unary `n` copy, generic
prefix work, then saved/count install. -/
noncomputable def program (a q : Nat) :=
  BitMachineRawSequence.program (nProgram q) (tailProgram a q)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inr .copyScan))))
    none
    (((((AtLeastLoopCallback.callback a q).initial, none), ((none, none), none)),
      ((PairVertexLoopCallback.routine a q).initial, none)), (none, none))

/-- Exact charged clock: the `2*n+2` unary copy, the whole prefix work cost,
both copy-backs, and the three sequencing handoffs. -/
noncomputable def cost (n a q : Nat) : Nat :=
  (2*n+2) +
    (PrefixComposite.cost n a q [] [] [] +
      (2*(savedWord n a q).length + 2 + (2*(countWord n a).length+2) + 1) + 1) + 1

/-- The ambient prefix program, from the staged first-row bank `U` (with
unary vertex `true^n` and blank writer `saved`/`count`), reaches exactly the
bank `installed U n a`. -/
theorem run {q : Nat} (a n : Nat)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (hvertex : U (.inr SourceClauseRowWriterOperands.vertex) =
      List.replicate n true)
    (hsaved : U (.inr SourceClauseRowWriterCleanup.savedCell) = [])
    (hcount : U (.inr SourceClauseRowWriterCleanup.countCell) = []) :
    ∃ T ≤ cost n a q,
      ((advance (program a q))^[T])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,
            (((((AtLeastLoopCallback.callback a q).initial, none),
                ((none, none), none)),
              ((PairVertexLoopCallback.routine a q).initial, none)),
              (none, none))),
          initial U⟩ :
          TM2.Cfg (fun _ : PrefixAmbientCopy.Stack q => Bool) _ _) =
        ⟨none,
          (none,
            (((((AtLeastLoopCallback.callback a q).initial, none),
                ((none, none), none)),
              ((PairVertexLoopCallback.routine a q).initial, none)),
              (none, none))),
          installed U n a⟩ := by
  obtain ⟨t1, ht1, h1⟩ := PrefixAmbientWork.work_run U n a
  obtain ⟨t2, ht2, h2⟩ :=
    PrefixAmbientInstall.installed_run U n a hsaved hcount
  obtain ⟨u, hu, hU⟩ := BitMachineRawSequence.runs
    (workProgram a q) (PrefixAmbientInstall.program q)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.inr .copyScan)))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((((AtLeastLoopCallback.callback a q).initial, none), ((none, none), none)),
      ((PairVertexLoopCallback.routine a q).initial, none))
    ((((AtLeastLoopCallback.callback a q).initial, none), ((none, none), none)),
      ((PairVertexLoopCallback.routine a q).initial, none))
    (none, none) (none, none)
    (seed U n) (worked U n a) (installed U n a) t1 t2 h1 h2
  have h0 := PrefixAmbientWork.seed_run U n hvertex
  obtain ⟨T, hT, hR⟩ := BitMachineRawSequence.runs
    (nProgram q) (tailProgram a q)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel (.inr .copyScan))))
    none none
    (((((AtLeastLoopCallback.callback a q).initial, none), ((none, none), none)),
      ((PairVertexLoopCallback.routine a q).initial, none)), (none, none))
    (((((AtLeastLoopCallback.callback a q).initial, none), ((none, none), none)),
      ((PairVertexLoopCallback.routine a q).initial, none)), (none, none))
    (initial U) (seed U n) (installed U n a) (2*n+2) u h0 hU
  refine ⟨T, ?_, hR⟩
  unfold cost
  omega

/-- Raw-bank projection of the exit bank: the staged controller bank with
exactly the reversed generic prefix bytes and unary prefix count installed in
the writer `saved`/`count` cells; every other raw cell is unchanged. -/
theorem run_raw {q : Nat} (a n : Nat)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (x : SourceCSPFirstRowController.Stack q) :
    installed U n a (rawEmbedding q x) =
      Function.update
        (Function.update U (.inr SourceClauseRowWriterCleanup.savedCell)
          ((PrefixCompositeEndpoint.sourceFields n a q).reverse))
        (.inr SourceClauseRowWriterCleanup.countCell)
        (List.replicate ((3*a+2+8*(a*a))*n) true) x :=
  installed_raw U n a x

/-! ## Length of the installed words and a closed polynomial clock -/

theorem prefix_valid (n a q : Nat) :
    ∀ d ∈ atLeastChains n a q ++ pairChains n a q,
      d.Valid (SourceGenericPairEnumeration.variableBound n a q) := by
  have hw : a ≤ width a q := le_max_left _ _
  intro d hd
  rcases List.mem_append.mp hd with h | h
  · simp only [atLeastChains, List.mem_flatten, List.mem_ofFn] at h
    obtain ⟨_, ⟨v, rfl⟩, hdv⟩ := h
    have hv : v.val ≤ SourceGenericPairEnumeration.ordinalBound n a := by
      have := v.isLt
      unfold SourceGenericPairEnumeration.ordinalBound
      omega
    have hmul := Nat.mul_le_mul_right (width a q + 1) hv
    refine chain_valid _ _ _ ?_ ?_ d hdv
    · rw [atLeast_length]
      unfold base SourceGenericPairEnumeration.variableBound
      rw [Nat.add_mul]
      omega
    · intro l hl
      simp only [atLeastPayload, List.mem_ofFn] at hl
      obtain ⟨s, rfl⟩ := hl
      have hb := (bitIndex v s).isLt
      change (bitIndex v s).val < SourceGenericPairEnumeration.variableBound n a q
      unfold SourceGenericPairEnumeration.variableBound
      omega
  · simp only [pairChains, List.mem_flatten, List.mem_ofFn] at h
    obtain ⟨_, ⟨v, rfl⟩, h⟩ := h
    simp only [List.mem_flatten, List.mem_ofFn] at h
    obtain ⟨_, ⟨u, rfl⟩, hdv⟩ := h
    let s := (finProdFinEquiv.symm u).1
    let t := (finProdFinEquiv.symm u).2
    have ho := SourceGenericPairEnumeration.pairOrdinal_le v s t
    have hmul := Nat.mul_le_mul_right (width a q + 1) ho
    refine chain_valid _ _ _ ?_ ?_ d hdv
    · rw [pair_length]
      change n*a + pairOrdinal v s t * (width a q + 1) + 2 <
        SourceGenericPairEnumeration.variableBound n a q
      unfold SourceGenericPairEnumeration.variableBound
      rw [Nat.add_mul]
      omega
    · intro l hl
      change l ∈ pairPayload v s t at hl
      rw [pair_payload_signs] at hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · have hb := (bitIndex v s).isLt
        change (bitIndex v s).val < SourceGenericPairEnumeration.variableBound n a q
        unfold SourceGenericPairEnumeration.variableBound
        omega
      · have hb := (bitIndex v t).isLt
        change (bitIndex v t).val < SourceGenericPairEnumeration.variableBound n a q
        unfold SourceGenericPairEnumeration.variableBound
        omega

theorem savedWord_length_le (n a q : Nat) :
    (savedWord n a q).length ≤
      ((3*a+2+8*a*a)*n) *
        (6*SourceGenericPairEnumeration.variableBound n a q + 6) := by
  have h := clauseFields_length_upper _ _ (prefix_valid n a q)
  rw [prefix_length] at h
  simpa only [savedWord, PrefixCompositeEndpoint.sourceFields,
    List.length_reverse] using h

theorem countWord_length (n a : Nat) :
    (countWord n a).length = (3*a+2+8*(a*a))*n := by
  simp [countWord]

/-- Fixed-`(a,q)` coefficient of the closed ambient clock. -/
noncomputable def ambientCoefficient (a q : Nat) : Nat :=
  SourceGenericPrefixClock.compositeCoefficient a q +
    2*(3*a+2+8*a*a)*(6*SourceGenericPrefixClock.pairVariableCoefficient a q + 6) +
    2*(3*a+2+8*(a*a)) + 12

theorem cost_le_closed (n a q : Nat) :
    cost n a q ≤ ambientCoefficient a q * (n+1)^9 := by
  have hc := SourceGenericPrefixClock.prefix_composite_cost_le_closed
    n a q [] [] []
  simp only [List.length_nil, Nat.add_zero] at hc
  have hs := savedWord_length_le n a q
  have hv := SourceGenericPrefixClock.variableBound_le n a q (n+1) le_rfl
  have hcnt := countWord_length n a
  set X := n + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hnX : n ≤ X := by omega
  have hX2 : X ≤ X^9 := by
    calc X = X^1 := (pow_one X).symm
      _ ≤ X^9 := Nat.pow_le_pow_right hX1 (by norm_num)
  have hXX : X*X ≤ X^9 := by
    calc X*X = X^2 := (sq X).symm
      _ ≤ X^9 := Nat.pow_le_pow_right hX1 (by norm_num)
  have h6 : 6*SourceGenericPairEnumeration.variableBound n a q + 6 ≤
      (6*SourceGenericPrefixClock.pairVariableCoefficient a q + 6) * X := by
    nlinarith only [hv, hX1]
  have hsw : (savedWord n a q).length ≤
      (3*a+2+8*a*a)*(6*SourceGenericPrefixClock.pairVariableCoefficient a q + 6) *
        (X*X) := by
    have h1 : (3*a+2+8*a*a)*n ≤ (3*a+2+8*a*a)*X :=
      Nat.mul_le_mul_left _ hnX
    calc (savedWord n a q).length
        ≤ ((3*a+2+8*a*a)*n) *
            (6*SourceGenericPairEnumeration.variableBound n a q + 6) := hs
      _ ≤ ((3*a+2+8*a*a)*X) *
            ((6*SourceGenericPrefixClock.pairVariableCoefficient a q + 6) * X) :=
          Nat.mul_le_mul h1 h6
      _ = _ := by ring
  have hsw9 : (savedWord n a q).length ≤
      (3*a+2+8*a*a)*(6*SourceGenericPrefixClock.pairVariableCoefficient a q + 6) *
        X^9 :=
    hsw.trans (Nat.mul_le_mul_left _ hXX)
  have hcw9 : (countWord n a).length ≤ (3*a+2+8*(a*a)) * X^9 := by
    rw [hcnt]
    exact (Nat.mul_le_mul_left _ hnX).trans (Nat.mul_le_mul_left _ hX2)
  have hn9 : n ≤ X^9 := hnX.trans hX2
  have h19 : 1 ≤ X^9 := hX1.trans hX2
  have e : ambientCoefficient a q * X^9 =
      SourceGenericPrefixClock.compositeCoefficient a q * X^9 +
      2*((3*a+2+8*a*a)*(6*SourceGenericPrefixClock.pairVariableCoefficient a q + 6) *
        X^9) +
      2*((3*a+2+8*(a*a)) * X^9) + 12 * X^9 := by
    unfold ambientCoefficient
    ring
  unfold cost
  rw [e]
  omega

/-- The same run with the closed polynomial clock in the vertex count. -/
theorem run_polynomial {q : Nat} (a n : Nat)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (hvertex : U (.inr SourceClauseRowWriterOperands.vertex) =
      List.replicate n true)
    (hsaved : U (.inr SourceClauseRowWriterCleanup.savedCell) = [])
    (hcount : U (.inr SourceClauseRowWriterCleanup.countCell) = []) :
    ∃ T ≤ ambientCoefficient a q * (n+1)^9,
      ((advance (program a q))^[T])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          (none,
            (((((AtLeastLoopCallback.callback a q).initial, none),
                ((none, none), none)),
              ((PairVertexLoopCallback.routine a q).initial, none)),
              (none, none))),
          initial U⟩ :
          TM2.Cfg (fun _ : PrefixAmbientCopy.Stack q => Bool) _ _) =
        ⟨none,
          (none,
            (((((AtLeastLoopCallback.callback a q).initial, none),
                ((none, none), none)),
              ((PairVertexLoopCallback.routine a q).initial, none)),
              (none, none))),
          installed U n a⟩ := by
  obtain ⟨T, hT, hR⟩ := run a n U hvertex hsaved hcount
  exact ⟨T, hT.trans (cost_le_closed n a q), hR⟩

#print axioms run
#print axioms run_raw
#print axioms prefix_valid
#print axioms savedWord_length_le
#print axioms countWord_length
#print axioms cost_le_closed
#print axioms run_polynomial

end EthInapproximability.CurrentPaper.SourceGenericComposite.PrefixAmbientProgram
