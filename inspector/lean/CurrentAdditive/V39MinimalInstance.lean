import CurrentAdditive.V39MinimalCompiler
import CurrentAdditive.V39SourceRenderer
import CurrentAdditive.V39SourceOutputSize

namespace CurrentAdditive.YaoMinimalSource

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.SmallBias CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.V38Encoded (edgeBits edgeCount_le_capacity)
open CurrentAdditive.V39SourceRenderer (sourceInstance selectedModulus sourceInstance_Dalt)
open CurrentAdditive.V38Source (colourCount)
open Paper2.YaoSourceCodec Paper2.YaoCloneSource
open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol

set_option maxHeartbeats 1000000

theorem selectedInstance_valid {t : ℕ} (G : SourceInput t) (input : List Bool) :
    (sourceInstance (selectedSource G input)).Valid :=
  CurrentAdditive.V38Executable.instanceOfTable_valid
    (selectedSource_nonempty G input) _ _ _ _ _ _

/-- The same canonical selected instance is used by the public source law,
the executable entry and both implications. No stronger epsilon is assumed. -/
theorem selectedInstance_costs {t : ℕ} (G : SourceInput t)
    (input : List Bool) (ht : 4 ≤ t) :
    let src := selectedSource G input
    let b := edgeBits src.2.1
    let inst := sourceInstance src
    (input ∈ G.L →
      Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table) ≤
        2 * b + 4 * t + 2) ∧
    (input ∉ G.L →
      (2 * b + 4 * t + 2) + 2 * t - 8 ≤
        Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table)) := by
  dsimp only
  let src := selectedSource G input
  let b := edgeBits src.2.1
  let index := Fin.castLEEmb (edgeCount_le_capacity src.2.1)
  obtain ⟨output, modulus, houtput, hmodulus, hout, hyes, hno⟩ :=
    v38_public_printed_matrix_yes_no b t ht src.2.2 index
  have hm : selectedModulus b t = modulus := by
    simp only [selectedModulus, hmodulus, Option.getD_some]
  constructor
  · intro hy
    rw [sourceInstance_Dalt, CurrentAdditive.V38Executable.table_Dalt]
    change Dalt .alice (matrixV38 (placeEdges src.2.2 index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (v38PrintedPairWord b t (v38FieldDegree b t) (selectedModulus b t))) ≤ _
    rw [hm]
    obtain ⟨colour, hbal⟩ := selectedSource_yes G input hy
    exact hyes colour hbal
  · intro hn
    rw [sourceInstance_Dalt, CurrentAdditive.V38Executable.table_Dalt]
    change _ ≤ Dalt .alice (matrixV38 (placeEdges src.2.2 index)
      (fullSelector (2 ^ (t - 1)) (2 ^ b))
      (v38PrintedPairWord b t (v38FieldDegree b t) (selectedModulus b t)))
    rw [hm]
    have hcol : ∀ colour : Fin src.1 → Fin (2 ^ (2 ^ t)),
        ∃ k c, ∀ j, colour (src.2.2 k j) = c :=
      selectedSource_no G input hn
    exact hno hcol

theorem render_sourceCode {t : ℕ} (G : SourceInput t) (input : List Bool) :
    CurrentAdditive.V39SourceRenderer.render t (sourceCode G input) =
      encodeInstance (sourceInstance (selectedSource G input)) :=
  CurrentAdditive.V39SourceRenderer.render_encode _

/-- Exact byte identity with the already reviewed stronger-input path. -/
theorem selectedInstance_ofStrong {t : ℕ}
    (G : CurrentAdditive.V38Source.GLSourceInput t) (input : List Bool) :
    sourceInstance (selectedSource (ofStrong G) input) =
      sourceInstance (CurrentAdditive.V38Source.selectedSource G input) := rfl

theorem selected_encoded_instance_length_poly {t : ℕ} (G : SourceInput t) :
    ∃ c d : ℕ, ∀ input,
      (encodeInstance (sourceInstance (selectedSource G input))).length ≤
        c * (input.length + 1) ^ d := by
  obtain ⟨c, d, hc⟩ := source_encoded_length_poly G
  refine ⟨CurrentAdditive.V39SourceOutputSize.outputCoefficient t *
      (c + 1) ^ CurrentAdditive.V39SourceOutputSize.outputDegree t,
    d * CurrentAdditive.V39SourceOutputSize.outputDegree t, fun input => ?_⟩
  have hp : 1 ≤ (input.length + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have hlen : (encode (selectedSource G input)).length + 1 ≤
      (c + 1) * (input.length + 1) ^ d := by
    have h := hc input
    nlinarith
  calc
    _ ≤ CurrentAdditive.V39SourceOutputSize.outputCoefficient t *
        ((encode (selectedSource G input)).length + 1) ^
          CurrentAdditive.V39SourceOutputSize.outputDegree t :=
      CurrentAdditive.V39SourceOutputSize.encoded_instance_length_bound _
    _ ≤ CurrentAdditive.V39SourceOutputSize.outputCoefficient t *
        ((c + 1) * (input.length + 1) ^ d) ^
          CurrentAdditive.V39SourceOutputSize.outputDegree t :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

#print axioms selectedInstance_valid
#print axioms selectedInstance_costs
#print axioms render_sourceCode
#print axioms selectedInstance_ofStrong
#print axioms selected_encoded_instance_length_poly

end CurrentAdditive.YaoMinimalSource
