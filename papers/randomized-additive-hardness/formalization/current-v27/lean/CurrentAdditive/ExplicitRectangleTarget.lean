import CurrentAdditive.ExplicitStageNumbering
import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-! The exact encoded rectangle in a producer-chosen input order.  Its table
length is charged by the stage's bit budget, while all three numeric headers
remain visible in the complete encoded word. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open CurrentAdditive.IndexedStagePresentation
open EthInapproximability.CurrentPaper

universe u

def numberedRectangle {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) (b : ℕ) : EncodedCommunication.Instance :=
  ⟨rows R, cols R, b, MatrixMaterialization.rowMajor (numberedTable R e)⟩

theorem numberedRectangle_valid {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) (b : ℕ) :
    (numberedRectangle R e b).Valid := by
  exact ⟨rows_pos R, cols_pos R, MatrixMaterialization.rowMajor_length _⟩

theorem numberedRectangle_table_length {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) (b : ℕ) :
    (numberedRectangle R e b).table.length = rows R * cols R := by
  exact MatrixMaterialization.rowMajor_length _

theorem numberedRectangle_encoded_length {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) (b : ℕ) :
    (EncodedCommunication.encodeInstance (numberedRectangle R e b)).length =
      2 * ((rows R).bits.length + (cols R).bits.length + b.bits.length) +
        3 + rows R * cols R := by
  rw [EncodedCommunication.encodeInstance_length, numberedRectangle_table_length]
  rfl

theorem numberedRectangle_encoded_length_le {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) (b : ℕ) :
    (EncodedCommunication.encodeInstance (numberedRectangle R e b)).length ≤
      2 * ((rows R).bits.length + (cols R).bits.length + b.bits.length) +
        3 + R.encodingSize := by
  rw [numberedRectangle_encoded_length]
  exact Nat.add_le_add_left R.entries_le_encoding _

theorem numberedRectangle_decodes {N : ℕ} (R : Stage.{u} N)
    (e : ExplicitNumberings R) (b : ℕ) :
    EncodedCommunication.decodeInstance
      (EncodedCommunication.encodeInstance (numberedRectangle R e b)) =
      some (numberedRectangle R e b) :=
  EncodedCommunication.decode_encode _ (numberedRectangle_valid R e b)

#print axioms numberedRectangle_valid
#print axioms numberedRectangle_encoded_length_le
#print axioms numberedRectangle_decodes

end CurrentAdditive.IndexedExecutableStepRecovery
