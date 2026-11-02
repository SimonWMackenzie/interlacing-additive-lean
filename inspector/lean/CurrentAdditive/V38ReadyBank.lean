import CurrentAdditive.V38ReadyField
import CurrentAdditive.V38TailAccounting

noncomputable section
namespace CurrentAdditive.V38ReadyField

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec
open CurrentAdditive.SmallBias
open CurrentAdditive.V38ReadyScalars (b d H)

theorem output_source {t : ℕ} (x : YaoSource t) (p modulus : ℕ) (k : WStack t 0) :
    outputBank x p modulus (.source k) = sourceReady x k := by
  rw [output_foreign x p modulus (.source k)
    (outside_producer t _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h))]
  rw [V38ReadyScalars.output_foreign x (.source k)
    (by intro i h; cases h) (by intro i h; cases h)
    (by intro i h; cases h) (by intro i h; cases h)]
  exact V38SourceFront.source_value x k

theorem output_scratch {t : ℕ} (x : YaoSource t) (p modulus : ℕ) :
    outputBank x p modulus (.copyScratch 0) = [] := by
  rw [output_foreign x p modulus (.copyScratch 0)
    (V38AmbientFieldInstall.producer_foreign_scratch t)]
  exact scratch_blank t x

theorem output_writer {t : ℕ} (x : YaoSource t) (p modulus : ℕ)
    (k : MatrixTableWriter.Stack 60) :
    outputBank x p modulus (.writer k) = [] := by
  rw [output_foreign x p modulus (.writer k)
    (outside_producer t _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h))]
  apply V38ReadyScalars.blank_value <;> intro i h <;> cases h

theorem output_header {t : ℕ} (x : YaoSource t) (p modulus : ℕ) (k : Paper2.HeaderA.HB) :
    outputBank x p modulus (.header k) = [] := by
  rw [output_foreign x p modulus (.header k)
    (outside_producer t _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h))]
  apply V38ReadyScalars.blank_value <;> intro i h <;> cases h

/-- Literal public-cell invariant. It asserts no completed table or output
runtime; the source and field programs prove it for their actual exit bank. -/
structure ReadyInput {t : ℕ} (x : YaoSource t) (modulus : ℕ)
    (S : Cell t 16 → List Bool) : Prop where
  scratch : S (.copyScratch 0) = []
  writer : ∀ k : MatrixTableWriter.Stack 60, S (.writer k) = []
  header : ∀ k : Paper2.HeaderA.HB, S (.header k) = []
  capacity : S (.selector 1) = List.replicate ((2^(b x))^(2^(t-1))) true
  labels : S (.square 3) = List.replicate ((2^(d x))^2) true
  addresses : S (.source (sN 6)) = List.replicate (2^(b x)) true
  body : S (.source (sN 1)) =
    Paper2.UnaryFieldListParserScratch.tokens (List.ofFn (flatten x.2.2))
  arity : S (.source (sN 9)) = List.replicate (2^t*2^t) true
  bits : S (.field (CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.printerSlots
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
    V38TablePrinter.bankBits (b x) t (d x) modulus
  width : S (.width 3) = List.replicate (2^(b x)*(2^t*2^t+1)) true
  rows : S (.dimensions 5) = List.replicate (rowCount x.1 (b x) t) true
  columns : S (.dimensions 7) = List.replicate (columnCount (b x) t (d x)) true
  threshold : S (.threshold 1) = List.replicate (2*b x+4*t+2) true

theorem output_ready {t : ℕ} (x : YaoSource t) (p modulus : ℕ) :
    ReadyInput x modulus (outputBank x p modulus) := by
  have hv := V39ScalarSetup.scalarOutput_values t x.1 (b x) (H x) (d x)
    (V38SourceFront.outputBank x)
  obtain ⟨hcap,hlabels,hrows,hcols,hthr⟩ := hv
  have hforeign (j : Cell t 16)
      (hF : ∀ k, j ≠ .field k) (hI : ∀ k, j ≠ .fieldInit k)
      (h1 : j ≠ .copyScratch 1) (h2 : j ≠ .copyScratch 2) :
      outputBank x p modulus j = V38ReadyScalars.outputBank x j :=
    output_foreign x p modulus j (outside_producer t j hF hI h1 h2)
  have hc : outputBank x p modulus (.selector 1) = _ :=
    hforeign _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  have hl : outputBank x p modulus (.square 3) = _ :=
    hforeign _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  have hr : outputBank x p modulus (.dimensions 5) = _ :=
    hforeign _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  have hcol : outputBank x p modulus (.dimensions 7) = _ :=
    hforeign _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  have hth : outputBank x p modulus (.threshold 1) = _ :=
    hforeign _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  obtain ⟨hbody,_,_,_,hH,hK⟩ := sourceReady_public_cells x
  refine ⟨output_scratch x p modulus, output_writer x p modulus,
    output_header x p modulus, hc.trans hcap, hl.trans hlabels, ?_, ?_, ?_, ?_, ?_,
    hr.trans hrows, hcol.trans hcols, hth.trans hthr⟩
  · rw [output_source]; exact hH
  · rw [output_source]; exact hbody
  · rw [output_source]; exact hK
  · exact V38AmbientFieldFull.finalBank_field (b x) t p modulus _
  · rw [hforeign _ (by intro i h; cases h) (by intro i h; cases h)
      (by intro h; cases h) (by intro h; cases h)]
    rw [V38ReadyScalars.output_foreign x (.width 3)
      (by intro i h; cases h) (by intro i h; cases h)
      (by intro i h; cases h) (by intro i h; cases h)]
    exact V38SourceFront.padded_width_value x

#print axioms output_ready
end CurrentAdditive.V38ReadyField
