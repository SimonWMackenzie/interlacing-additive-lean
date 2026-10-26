import CurrentAdditive.V38SourceDegree
import CurrentAdditive.CanonicalAmbientWidthFull

/-! Separate physical words for the genuine H*K field array and the internal
H*(K+1) lookup bank. These words must not be interchanged. -/

noncomputable section
namespace CurrentAdditive.V38SourceWidths

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding MatrixStage4ScalarPreparationOps
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

def place (t : ℕ) : Fin 6 ↪ Cell t 16 :=
  ⟨![.width 0, .width 1, .width 4, .width 6, .width 7, .width 5], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def paddedOutput {t : ℕ} (x : YaoSource t) : Cell t 16 → List Bool :=
  bank (widthEmbed t 16)
    (widthInputBank t 16 (paddedEdgeCount x.2.1) (arity t)
      (V38SourceDegree.outputBank x))
    (Function.update (Function.update
      (CurrentAdditive.FiniteFieldConstructor.CanonicalWidthMultiply.initial
        (paddedEdgeCount x.2.1) (arity t)) 2
      (List.replicate (arity t + 1) true)) 3
      (List.replicate (paddedEdgeCount x.2.1 * (arity t + 1)) true))

def outputBank {t : ℕ} (x : YaoSource t) : Cell t 16 → List Bool :=
  Function.update (paddedOutput x) (.width 5)
    (List.replicate (paddedEdgeCount x.2.1 * arity t) true)

def program (t : ℕ) := BitMachineRawSequence.program
  (widthFullProgram t 16) (multiplyProgram (place t))
  MatrixAddressMachine.Label.outer
  ((none, none), (none, ((), false))) false

theorem padded_words {t : ℕ} (x : YaoSource t) :
    paddedOutput x (.width 0) = List.replicate (paddedEdgeCount x.2.1) true ∧
    paddedOutput x (.width 1) = List.replicate (arity t) true ∧
    paddedOutput x (.width 3) =
      List.replicate (paddedEdgeCount x.2.1 * (arity t + 1)) true ∧
    paddedOutput x (.width 4) = [] ∧ paddedOutput x (.width 5) = [] ∧
    paddedOutput x (.width 6) = [] ∧ paddedOutput x (.width 7) = [] := by
  let W := Function.update (Function.update
    (CurrentAdditive.FiniteFieldConstructor.CanonicalWidthMultiply.initial
      (paddedEdgeCount x.2.1) (arity t)) 2
      (List.replicate (arity t + 1) true)) 3
      (List.replicate (paddedEdgeCount x.2.1 * (arity t + 1)) true)
  have he (i : Fin 8) : paddedOutput x (.width i) = W i :=
    bank_at (widthEmbed t 16) _ W i
  simp only [he]
  simp [W, CurrentAdditive.FiniteFieldConstructor.CanonicalWidthMultiply.initial]

theorem genuine_run (t : ℕ) (x : YaoSource t) :
    ((advance (multiplyProgram (place t)))^[
      MatrixAddressMachine.exactTime (paddedEdgeCount x.2.1) (arity t) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, paddedOutput x⟩ :
        TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      ⟨none, false, outputBank x⟩ := by
  obtain ⟨h0,h1,h3,h4,h5,h6,h7⟩ := padded_words x
  have hr := multiply_run (place t) (paddedOutput x)
    (paddedEdgeCount x.2.1) (arity t)
    (by simpa [place] using h0) (by simpa [place] using h1)
    (by simpa [place] using h4) (by simpa [place] using h6)
    (by simpa [place] using h7)
  simpa [place, h5, outputBank] using hr

theorem output_genuine {t : ℕ} (x : YaoSource t) :
    outputBank x (.width 5) =
      List.replicate (paddedEdgeCount x.2.1 * arity t) true := by
  simp [outputBank]

theorem output_padded {t : ℕ} (x : YaoSource t) :
    outputBank x (.width 3) =
      List.replicate (paddedEdgeCount x.2.1 * (arity t + 1)) true := by
  simpa [outputBank] using (padded_words x).2.2.1

def clock {t : ℕ} (x : YaoSource t) : ℕ :=
  ((2*paddedEdgeCount x.2.1+2) + (2*arity t+2) + 1) +
    ((2*arity t+2) + 2 + MatrixAddressMachine.exactTime
      (paddedEdgeCount x.2.1) (arity t+1) 0 + 2) + 1 +
    MatrixAddressMachine.exactTime (paddedEdgeCount x.2.1) (arity t) 0 + 1

theorem widths_run (t : ℕ) (x : YaoSource t) :
    ∃ steps ≤ clock x,
      ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none, none), (none, ((), false))), false),
          V38SourceDegree.outputBank x⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, (((none, none), (none, ((), false))), false), outputBank x⟩ := by
  obtain ⟨_,_,_,_,hH,hK⟩ :=
    CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.sourceReady_public_cells x
  have hh : V38SourceDegree.outputBank x (.source (sN 6)) =
      List.replicate (paddedEdgeCount x.2.1) true := by
    rw [V38SourceDegree.output_source]
    exact hH
  have hk : V38SourceDegree.outputBank x (.source (sN 9)) =
      List.replicate (arity t) true := by
    rw [V38SourceDegree.output_source]
    exact hK
  have hb : ∀ i : Fin 8, V38SourceDegree.outputBank x (.width i) = [] := by
    intro i
    exact V38SourceDegree.output_blank x (.width i)
      (by intro k h; cases h) (by intro k h; cases h)
  have hs : V38SourceDegree.outputBank x (.copyScratch 0) = [] :=
    V38SourceDegree.output_blank x (.copyScratch 0)
      (by intro k h; cases h) (by intro k h; cases h)
  obtain ⟨u,hu,hr⟩ := physical_width_full t 16
    (paddedEdgeCount x.2.1) (arity t) (V38SourceDegree.outputBank x) hh hk hb hs
  have hmul := genuine_run t x
  obtain ⟨v,hv,hc⟩ := BitMachineRawSequence.runs
    (widthFullProgram t 16) (multiplyProgram (place t))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    MatrixAddressMachine.Label.outer
    ((none, none), (none, ((), false)))
    ((none, none), (none, ((), false))) false false
    (V38SourceDegree.outputBank x) (paddedOutput x) (outputBank x) u
    (MatrixAddressMachine.exactTime (paddedEdgeCount x.2.1) (arity t) 0)
    (by simpa [paddedOutput] using hr) hmul
  exact ⟨v, by unfold clock; omega, by simpa [program] using hc⟩

theorem output_foreign {t : ℕ} (x : YaoSource t) (j : Cell t 16)
    (hj : ∀ k : Fin 8, Cell.width k ≠ j) :
    outputBank x j = V38SourceDegree.outputBank x j := by
  have h5 : j ≠ .width 5 := fun h => hj 5 h.symm
  have h0 : j ≠ .width 0 := fun h => hj 0 h.symm
  have h1 : j ≠ .width 1 := fun h => hj 1 h.symm
  have hp : ¬ ∃ k, widthEmbed t 16 k = j := by
    rintro ⟨k,hk⟩
    exact hj k hk
  simp only [outputBank, Function.update_of_ne h5]
  rw [paddedOutput, bank_outside (widthEmbed t 16) _ _ j hp]
  simp [widthInputBank, h0, h1]

#print axioms widths_run
#print axioms output_foreign

#print axioms genuine_run
#print axioms output_genuine
#print axioms output_padded
end CurrentAdditive.V38SourceWidths
