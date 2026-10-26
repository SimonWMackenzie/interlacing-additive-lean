import CurrentAdditive.CanonicalAmbientWriterHeaderFull
import CurrentAdditive.V38AmbientHeaderFull

/-! The row-major table printer leaves the header inputs and copy scratch
intact while placing the exact table bits in its output cell. -/

noncomputable section

namespace CurrentAdditive.V38TablePrinter.Ambient

open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoLookup Paper2.YaoMachine Paper2.YaoFrame

def writerOutputBank {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v)
    (S : Cell t N → List Bool) : Cell t N → List Bool :=
  bank (writerEmbed t N) (CopyFill.fill (writerJobs t N) S)
    (MatrixTableWriter.ready
      (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
      (rowCount v (paddedEdgeBits e) t)
      (columnCount (paddedEdgeBits e) t d)
      0 0 0 0 []
      (table (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges).bits).contents

theorem writerOutputBank_foreign {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v)
    (S : Cell t N → List Bool) (j : Cell t N)
    (hwriter : ¬ ∃ k : MatrixTableWriter.Stack 60,
      writerEmbed t N k = j)
    (hjobs : ∀ job ∈ writerJobs t N, j ∉ job.2) :
    writerOutputBank t N d modulus edges S j = S j := by
  rw [writerOutputBank, bank_outside (writerEmbed t N) _ _ j hwriter]
  exact CopyFill.fill_off (writerJobs t N) S j hjobs

theorem writerOutputBank_header_inputs {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v)
    (S : Cell t N → List Bool) :
    (∀ k : Paper2.HeaderA.HB,
      writerOutputBank t N d modulus edges S (.header k) = S (.header k)) ∧
    writerOutputBank t N d modulus edges S (.copyScratch 0) =
      S (.copyScratch 0) ∧
    writerOutputBank t N d modulus edges S (.dimensions 5) =
      S (.dimensions 5) ∧
    writerOutputBank t N d modulus edges S (.dimensions 7) =
      S (.dimensions 7) ∧
    writerOutputBank t N d modulus edges S (.threshold 1) =
      S (.threshold 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    apply writerOutputBank_foreign
      <;> simp [writerJobs, writerEmbed]
  · apply writerOutputBank_foreign
      <;> simp [writerJobs, writerEmbed]
  · apply writerOutputBank_foreign
      <;> simp [writerJobs, writerEmbed]
  · apply writerOutputBank_foreign
      <;> simp [writerJobs, writerEmbed]
  · apply writerOutputBank_foreign
      <;> simp [writerJobs, writerEmbed]

theorem writerOutputBank_bits {v e : ℕ} (t N d modulus : ℕ)
    (edges : Fin e → Fin (2^t*2^t) ↪ Fin v)
    (S : Cell t N → List Bool) :
    writerOutputBank t N d modulus edges S (.writer (.inr .output)) =
      (table (paddedEdgeBits e) t d modulus
        (le_paddedEdgeCount e) edges).bits := by
  simpa [writerOutputBank, MatrixTableWriter.ready,
    MatrixTableWriter.Data.contents, MatrixTableWriter.Data.foreign] using
    (bank_at (writerEmbed t N) (CopyFill.fill (writerJobs t N) S)
      (MatrixTableWriter.ready
        (canonicalWriterBank (paddedEdgeBits e) t d modulus edges)
        (rowCount v (paddedEdgeBits e) t)
        (columnCount (paddedEdgeBits e) t d)
        0 0 0 0 []
        (table (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges).bits).contents
      (.inr .output))

#print axioms writerOutputBank_foreign
#print axioms writerOutputBank_header_inputs
#print axioms writerOutputBank_bits

end CurrentAdditive.V38TablePrinter.Ambient
