import Paper2.SamplerAffineInit
import Paper2.AffineMultiplyAdd

set_option maxHeartbeats 5000000

namespace Paper2.SamplerDrawCount

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineRawSequence

abbrev Stack := SamplerAffineRound.Stack

def firstIndex (b : Bool) : Fin 6 ↪ Stack where
  toFun := ![SamplerAffineRound.col b, 8, 21, 17, 18, 22]
  inj' := by
    intro a c h
    cases b <;> fin_cases a <;> fin_cases c <;>
      simp [SamplerAffineRound.col] at h ⊢

def secondIndex (b : Bool) : Fin 6 ↪ Stack where
  toFun := ![SamplerAffineRound.row b, 7, 20, 17, 18, 22]
  inj' := by
    intro a c h
    cases b <;> fin_cases a <;> fin_cases c <;>
      simp [SamplerAffineRound.row] at h ⊢

def oneProgram := SourceClauseFixedUnary.program (21 : Stack) 1
def firstMul (b : Bool) :=
  MatrixStage4ScalarPreparationOps.multiplyProgram (firstIndex b)
def secondMul (b : Bool) :=
  MatrixStage4ScalarPreparationOps.multiplyProgram (secondIndex b)

abbrev FirstLabel := BitMachineRawSequence.Label
  (SourceClauseFixedUnary.Label 1) MatrixAddressMachine.Label
abbrev FirstControl := Unit × Bool
abbrev Label := BitMachineRawSequence.Label FirstLabel MatrixAddressMachine.Label
abbrev Control := FirstControl × Bool

def firstProgram (b : Bool) := BitMachineRawSequence.program
  oneProgram (firstMul b) .outer () false

def program (b : Bool) := BitMachineRawSequence.program
  (firstProgram b) (secondMul b) .outer ((),false) false

def finalBank (S : Stack → List Bool) (mY mX c r : Nat) :
    Stack → List Bool :=
  Function.update (Function.update S 21 [true]) 22
    (List.replicate (1 + mY*c + mX*r) true)

theorem run (b : Bool) (S : Stack → List Bool)
    (mY mX c r : Nat)
    (hcol : S (SamplerAffineRound.col b) = List.replicate c true)
    (hrow : S (SamplerAffineRound.row b) = List.replicate r true)
    (hmY : S 8 = List.replicate mY true)
    (hmX : S 7 = List.replicate mX true)
    (h17 : S 17 = []) (h18 : S 18 = [])
    (h20 : S 20 = []) (h21 : S 21 = []) (h22 : S 22 = []) :
    ∃ t ≤ 2 + MatrixAddressMachine.exactTime c mY 1 +
      MatrixAddressMachine.exactTime r mX 0 + 2,
      ((advance (program b))^[t])
        (⟨some (.inl (.inl (0 : SourceClauseFixedUnary.Label 1))),
          (((),false),false), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, (((),false),false), finalBank S mY mX c r⟩ := by
  let S₁ := Function.update S 21 [true]
  let S₂ := Function.update S₁ 22
    (List.replicate (c*mY+1) true)
  let S₃ := finalBank S mY mX c r
  have hS₁ (j : Stack) (hj : j ≠ 21) : S₁ j = S j := by
    simp only [S₁, Function.update_of_ne hj]
  have hS₂ (j : Stack) (hj22 : j ≠ 22) (hj21 : j ≠ 21) :
      S₂ j = S j := by
    change (Function.update S₁ 22 (List.replicate (c*mY+1) true)) j = _
    rw [Function.update_of_ne hj22]
    exact hS₁ j hj21
  have hOne := SourceClauseFixedUnary.run (21 : Stack) S 1 h21
  have hOne' : ((advance oneProgram)^[2])
      (⟨some (0 : SourceClauseFixedUnary.Label 1), (), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (), S₁⟩ := by
    simpa only [oneProgram, S₁] using hOne
  have hfirst := AffineMultiplyAdd.multiply_add_run (firstIndex b) S₁ c mY 1
    (by change S₁ (SamplerAffineRound.col b) = _
        rw [hS₁ _ (by cases b <;> decide)]
        exact hcol)
    (by change S₁ 8 = _
        rw [hS₁ _ (by decide)]
        exact hmY)
    (by change S₁ 21 = [true]
        exact Function.update_self ..)
    (by change S₁ 17 = _
        rw [hS₁ _ (by decide)]
        exact h17)
    (by change S₁ 18 = _
        rw [hS₁ _ (by decide)]
        exact h18)
  have hfirst' : ((advance (firstMul b))^[
      MatrixAddressMachine.exactTime c mY 1])
      (⟨some .outer, false, S₁⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, S₂⟩ := by
    have hS₁22 : S₁ 22 = [] := by
      rw [hS₁ _ (by decide)]
      exact h22
    have heq : Function.update S₁ (firstIndex b 5)
        (List.replicate (c*mY+1) true ++ S₁ (firstIndex b 5)) = S₂ := by
      change Function.update S₁ 22
        (List.replicate (c*mY+1) true ++ S₁ 22) = S₂
      rw [hS₁22, List.append_nil]
    rw [heq] at hfirst
    exact hfirst
  have hsecond := AffineMultiplyAdd.multiply_add_run (secondIndex b) S₂ r mX 0
    (by change S₂ (SamplerAffineRound.row b) = _
        rw [hS₂ _ (by cases b <;> decide) (by cases b <;> decide)]
        exact hrow)
    (by change S₂ 7 = _
        rw [hS₂ _ (by decide) (by decide)]
        exact hmX)
    (by change S₂ 20 = []
        rw [hS₂ _ (by decide) (by decide)]
        exact h20)
    (by change S₂ 17 = []
        rw [hS₂ _ (by decide) (by decide)]
        exact h17)
    (by change S₂ 18 = []
        rw [hS₂ _ (by decide) (by decide)]
        exact h18)
  have hsecond' : ((advance (secondMul b))^[
      MatrixAddressMachine.exactTime r mX 0])
      (⟨some .outer, false, S₂⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, S₃⟩ := by
    have hfinal : Function.update S₂ 22
        (List.replicate (r*mX+0) true ++ S₂ 22) = S₃ := by
      have hnum : r*mX+0 + (c*mY+1) = 1+mY*c+mX*r := by ring
      rw [show S₂ 22 = List.replicate (c*mY+1) true from Function.update_self ..,
        List.replicate_append_replicate, hnum]
      change Function.update S₂ 22 _ =
        Function.update S₁ 22 _
      exact Function.update_idem ..
    have hfinal' : Function.update S₂ (secondIndex b 5)
        (List.replicate (r*mX+0) true ++ S₂ (secondIndex b 5)) = S₃ := hfinal
    rw [hfinal'] at hsecond
    exact hsecond
  obtain ⟨ta, hta, ha⟩ := BitMachineRawSequence.runs
    oneProgram (firstMul b)
    (0 : SourceClauseFixedUnary.Label 1) .outer
    () () false false S S₁ S₂ 2
    (MatrixAddressMachine.exactTime c mY 1) hOne' hfirst'
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (firstProgram b) (secondMul b)
    (.inl (0 : SourceClauseFixedUnary.Label 1)) .outer
    ((),false) ((),false) false false S S₂ S₃ ta
    (MatrixAddressMachine.exactTime r mX 0) ha hsecond'
  exact ⟨t, by omega, by simpa only [program, firstProgram, S₃] using hr⟩

#print axioms run

end Paper2.SamplerDrawCount
