import CurrentAdditive.V38ClockedRenderer
import CurrentAdditive.V39MinimalInstance

/-! The approved original source compiler, actual clone program and actual
source-to-table program are composed here. This uses the original strict
measure soundness at the same arity, without a stronger source record.
The physical clock includes both programs and the two-pass transfer. -/

noncomputable section
set_option autoImplicit false
namespace CurrentAdditive.V39ApprovedYaoCompiler

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic
open Paper2.YaoSourceCodec
open CurrentAdditive.YaoMinimalSource

def instanceWord {t : ℕ} (G : SourceInput t) (input : List Bool) : List Bool :=
  encodeInstance (V39SourceRenderer.sourceInstance (selectedSource G input))

def sourceTableMachine {t : ℕ} (G : SourceInput t) : BitMachine.Machine :=
  composition (sourceMachine G) (V38PhysicalRenderer.machine t)

def sourceTableTime {t : ℕ} (G : SourceInput t) (input : List Bool) : ℕ :=
  sourceTime G input + 2 * (sourceCode G input).length + 2 +
    V38PhysicalRenderer.clock (selectedSource G input)

theorem sourceTable_outputs {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t)
    (input : List Bool) :
    (sourceTableMachine G).OutputsWithin input (instanceWord G input)
      (sourceTableTime G input) := by
  have h := composition_outputsWithin (sourceMachine G) (V38PhysicalRenderer.machine t)
    (source_outputs G input) (V38PhysicalRenderer.outputs t ht (selectedSource G input))
  rw [V38PhysicalRenderer.word_eq_sourceInstance] at h
  exact h

theorem sourceTableTime_poly {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t) :
    ∃ c d : ℕ, ∀ input,
      sourceTableTime G input ≤ c * (input.length + 1) ^ d := by
  obtain ⟨a,p,ha⟩ := sourceTime_poly G
  obtain ⟨b,q,hb⟩ := V38PhysicalRenderer.clock_poly t ht
  refine ⟨a + 2 * (a * (sourceMachine G).pushBound + 1) +
      b * (a * (sourceMachine G).pushBound + 1)^q,
    (p+1)*(q+1),fun input => ?_⟩
  have hsource := ha input
  have hrenderer := hb (selectedSource G input)
  have hlen := BitMachine.output_length_bound (sourceMachine G) (source_outputs G input)
  have hmul := Nat.mul_le_mul_right (sourceMachine G).pushBound hsource
  have hcode : (sourceCode G input).length ≤ input.length +
      a * (input.length + 1)^p * (sourceMachine G).pushBound := by
    change (encode (selectedSource G input)).length ≤ _
    omega
  have hbound := composition_time_bound input.length a p b q
    (sourceMachine G).pushBound (sourceCode G input).length hcode
  change sourceTime G input + 2 * (sourceCode G input).length + 2 +
    V38PhysicalRenderer.clock (selectedSource G input) ≤ _
  change V38PhysicalRenderer.clock (selectedSource G input) ≤
    b * ((sourceCode G input).length + 1)^q at hrenderer
  omega

theorem instanceWord_polytime {t : ℕ} (G : SourceInput t) (ht : 4 ≤ t) :
    BitMachine.Polytime (instanceWord G) := by
  obtain ⟨c,d,hclock⟩ := sourceTableTime_poly G ht
  exact ⟨sourceTableMachine G,c,d,fun input =>
    BitMachine.outputsWithin_mono _ (sourceTable_outputs G ht input) (hclock input)⟩

theorem draft_instanceWord_polytime {t : ℕ}
    (G : Paper2.YaoX05Draft.GLSourceDraft t) (ht : 4 ≤ t) :
    BitMachine.Polytime (instanceWord (ofDraft G)) :=
  instanceWord_polytime (ofDraft G) ht

theorem draft_table_valid {t : ℕ} (G : Paper2.YaoX05Draft.GLSourceDraft t)
    (input : List Bool) :
    (V39SourceRenderer.sourceInstance (selectedSource (ofDraft G) input)).Valid :=
  selectedInstance_valid (ofDraft G) input

theorem draft_table_costs {t : ℕ} (G : Paper2.YaoX05Draft.GLSourceDraft t)
    (input : List Bool) (ht : 4 ≤ t) :
    let src := selectedSource (ofDraft G) input
    let b := V38Encoded.edgeBits src.2.1
    let inst := V39SourceRenderer.sourceInstance src
    (input ∈ G.L →
      Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table) ≤
        2*b+4*t+2) ∧
    (input ∉ G.L → (2*b+4*t+2)+2*t-8 ≤
      Paper2.Yao.Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table)) :=
  selectedInstance_costs (ofDraft G) input ht

#print axioms sourceTable_outputs
#print axioms sourceTableTime_poly
#print axioms instanceWord_polytime
#print axioms draft_instanceWord_polytime
#print axioms draft_table_costs
end CurrentAdditive.V39ApprovedYaoCompiler
