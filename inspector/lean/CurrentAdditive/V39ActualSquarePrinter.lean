import CurrentAdditive.V39ActualSquare
import CurrentAdditive.DeterministicETHPhysicalSquare

/-! One fixed physical rectangle-to-square postprocessor, applied to the
actual StoredMatrix. It first prints the square instance, then physically
removes its threshold header. The estimator receives exactly squareWord.
The complete clock is polynomial in the actual encoded rectangle length;
no Code D, source promise, completed printer or clock is a premise. -/

noncomputable section
set_option autoImplicit false
namespace CurrentAdditive.V39ActualSquarePrinter

open EthInapproximability.CurrentPaper
open CurrentAdditive.V39GeneratedConstruction
open CurrentAdditive.DeterministicETHPhysicalSquare

def machine : BitMachine.Machine := squareMatrixMachine

def clock (I : EncodedCommunication.Instance) : ℕ :=
  Paper2.ASquare.Post.fullBound I.rows I.cols I.threshold +
    2*(EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance I)).length+2+
    3*((EncodedCommunication.encodeInstance (Paper2.ASquare.squareInstance I)).length+1)

def coefficient : ℕ :=
  10^15+5*(1+10^15*Paper2.ASquare.Post.squareMachine.pushBound)

theorem clock_poly (I : EncodedCommunication.Instance) (hi : I.Valid) :
    clock I ≤ coefficient*((EncodedCommunication.encodeInstance I).length+1)^12 := by
  have hs := Paper2.ASquare.Post.full_outputs I hi
  have hb := Paper2.ASquare.Post.fullBound_le I hi
  have hl := BitMachine.output_length_bound Paper2.ASquare.Post.squareMachine hs
  have hpow : (EncodedCommunication.encodeInstance I).length+1 ≤
      ((EncodedCommunication.encodeInstance I).length+1)^12 := Nat.le_self_pow (by decide) _
  unfold coefficient
  generalize Paper2.ASquare.Post.squareMachine.pushBound = p at hl ⊢
  have hm := Nat.mul_le_mul_right p hb
  unfold clock
  nlinarith

theorem square_instance_identity (R : StoredMatrix) (b : ℕ) :
    Paper2.ASquare.squareInstance (R.numbered.rectangle b) =
      ⟨Paper2.SquarePadding.side R.rows R.cols,
        Paper2.SquarePadding.side R.rows R.cols,b,
        MatrixMaterialization.rowMajor R.square⟩ := by
  have hsq : Paper2.ASquare.squareFun R.rows R.cols
      (MatrixMaterialization.rowMajor R.entry) = R.square := by
    rw [Paper2.ASquare.squareFun_eq_matrix R.rows_pos R.cols_pos,
      rectangle_tableGame_rowMajor]
    rfl
  change (⟨_,_,_,MatrixMaterialization.rowMajor
    (Paper2.ASquare.squareFun R.rows R.cols (MatrixMaterialization.rowMajor R.entry))⟩ :
      EncodedCommunication.Instance) = _
  rw [hsq]
  rfl

theorem output_word_identity (R : StoredMatrix) (b : ℕ) :
    AFront.Projection.matrixWord
      (Paper2.ASquare.squareInstance (R.numbered.rectangle b)).rows
      (Paper2.ASquare.squareInstance (R.numbered.rectangle b)).cols
      (Paper2.ASquare.squareInstance (R.numbered.rectangle b)).table = R.squareWord := by
  rw [square_instance_identity]
  rfl

theorem outputs (R : StoredMatrix) (b : ℕ) :
    machine.OutputsWithin
      (EncodedCommunication.encodeInstance (R.numbered.rectangle b)) R.squareWord
      (clock (R.numbered.rectangle b)) := by
  let I := R.numbered.rectangle b
  have hs := Paper2.ASquare.Post.full_outputs I (R.numbered.rectangle_valid b)
  have hp := AFront.Projection.matrixMachine_encodeInstance (Paper2.ASquare.squareInstance I)
  have h := BitMachineComposition.composition_outputsWithin
    Paper2.ASquare.Post.squareMachine AFront.Projection.matrixMachine hs hp
  rw [output_word_identity] at h
  exact h

theorem outputs_polynomial (R : StoredMatrix) (b : ℕ) :
    machine.OutputsWithin
      (EncodedCommunication.encodeInstance (R.numbered.rectangle b)) R.squareWord
      (coefficient*((EncodedCommunication.encodeInstance (R.numbered.rectangle b)).length+1)^12) :=
  BitMachine.outputsWithin_mono _ (outputs R b)
    (clock_poly _ (R.numbered.rectangle_valid b))

#print axioms clock_poly
#print axioms square_instance_identity
#print axioms output_word_identity
#print axioms outputs
#print axioms outputs_polynomial
end CurrentAdditive.V39ActualSquarePrinter
