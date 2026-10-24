import CurrentAdditive.V38CloneMachine

/-!
The selected v39 `yao:source`/`yao:clones` source is the same as v38.
This file joins the actual strengthened clone compiler to its exact decoder
and supplies the finite sizes charged to downstream printers. The external
occurrence compiler `G : GLSourceInput t` remains uninstantiated.
-/

namespace CurrentAdditive.V39SourceCompiler

open CurrentAdditive.V38Source CurrentAdditive.V38Machine
open EthInapproximability.CurrentPaper
open Paper2.YaoCloneSource Paper2.YaoSourceCodec Paper2.YaoT26Size
open Paper2.YaoCloneMachine (labelsOf draftOccEncode_eq length_labelsOf)

set_option maxHeartbeats 1000000

/-- The actual Option-B word emitted by the strengthened source compiler. -/
def sourceCode {t : ℕ} (G : GLSourceInput t) (input : List Bool) : List Bool :=
  encode (selectedSource G input)

theorem sourceCode_outputs {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (sourceMachine G).OutputsWithin input (sourceCode G input)
      (CurrentAdditive.V38Machine.sourceTime G input) :=
  source_outputs G input

/-- The consumer decodes the exact same ordered, labelled source. -/
theorem sourceCode_decodes {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    decodeAll t (sourceCode G input) = some (selectedSource G input) :=
  decodeAll_encode _

/-- Every halting execution of that fixed compiler has this same output;
the decoder conclusion does not posit a source different from the emitted one. -/
theorem every_compiler_output_decodes {t : ℕ} (G : GLSourceInput t)
    (input bits : List Bool) (clock : ℕ)
    (hrun : (sourceMachine G).OutputsWithin input bits clock) :
    bits = sourceCode G input ∧
      decodeAll t bits = some (selectedSource G input) := by
  have hout : bits = sourceCode G input :=
    BitMachine.outputsWithin_unique (sourceMachine G) hrun (sourceCode_outputs G input)
  exact ⟨hout, hout ▸ sourceCode_decodes G input⟩

theorem occurrence_counts_le {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (G.output input).1 + (G.output input).2.1 + 2 ≤
      input.length + G.time input * G.machine.pushBound := by
  have h := occInput_length_ge (G.output input).1 (labelsOf (G.output input))
  rw [← draftOccEncode_eq, length_labelsOf] at h
  have hclock := h.trans (occurrence_length_le G input)
  omega

/-- Both headers are physically present in the emitted source word. -/
theorem cloned_counts_le_code {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (selectedSource G input).1 + (selectedSource G input).2.1 + 2 ≤
      (sourceCode G input).length := by
  rw [sourceCode, encode_length]
  omega

/-- Size bound in terms of the clock of this same fixed machine. -/
theorem cloned_counts_le_clock {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) :
    (selectedSource G input).1 + (selectedSource G input).2.1 + 2 ≤
      input.length + CurrentAdditive.V38Machine.sourceTime G input *
        (sourceMachine G).pushBound :=
  (cloned_counts_le_code G input).trans
    (BitMachine.output_length_bound _ (sourceCode_outputs G input))

/-- The source dimensions are polynomial in the actual encoded input length,
with constants permitted to depend on the fixed parameter and external compiler. -/
theorem cloned_counts_poly {t : ℕ} (G : GLSourceInput t) :
    ∃ c d : ℕ, ∀ input,
      (selectedSource G input).1 + (selectedSource G input).2.1 + 2 ≤
        c * (input.length + 1) ^ d := by
  obtain ⟨c, d, h⟩ := source_encoded_length_poly G
  exact ⟨c, d, fun input => (cloned_counts_le_code G input).trans (h input)⟩

theorem sourceCode_polytime {t : ℕ} (G : GLSourceInput t) :
    BitMachine.Polytime (sourceCode G) :=
  source_polytime G

#print axioms sourceCode_outputs
#print axioms sourceCode_decodes
#print axioms every_compiler_output_decodes
#print axioms occurrence_counts_le
#print axioms cloned_counts_le_code
#print axioms cloned_counts_le_clock
#print axioms cloned_counts_poly
#print axioms sourceCode_polytime

end CurrentAdditive.V39SourceCompiler
