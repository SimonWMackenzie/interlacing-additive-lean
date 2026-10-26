import CurrentAdditive.SmallBiasPhysicalDetEndpoint
import Paper2.HeaderWordPoly
import EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

/-!
# Physical midpoint-header composition

`Paper2.HeaderWordRun` already has one checked split/swap/map/concat bit
machine. It receives `encodeInstance i` and emits the exact header plus
matrix word. This file composes its clock with any encoded-instance printer
and specializes to the canonical source. Thus the only remaining physical
printer obligation is the encoded source instance itself.
-/

noncomputable section

namespace CurrentAdditive.SmallBias

set_option maxHeartbeats 2000000

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

def headerTransform (k : ℕ) (code : List Bool) : List Bool :=
  match decodeInstance code with
  | none => []
  | some i => Paper2.HeaderWordRun.headeredWord k i

theorem headerTransform_encode (k : ℕ) (i : Instance) (hi : i.Valid) :
    headerTransform k (encodeInstance i) =
      Paper2.HeaderWordRun.headeredWord k i := by
  simp [headerTransform, decode_encode i hi]

theorem header_from_encoded_polytime
    (f : List Bool → Instance) (hvalid : ∀ x, (f x).Valid)
    (hencoded : BitMachine.Polytime (fun x => encodeInstance (f x)))
    (k : ℕ) (hk : 0 < k) :
    BitMachine.Polytime (fun x => Paper2.HeaderWordRun.headeredWord k (f x)) := by
  let enc : List Bool → List Bool := fun x => encodeInstance (f x)
  obtain ⟨M, c, d, hM⟩ := hencoded
  obtain ⟨C, D, hHeader⟩ := Paper2.HeaderWordRun.machine_outputs_polynomial k
  let finalM := BitMachineComposition.composition M (Paper2.HeaderWordRun.machine k)
  have hcomp : ∀ x, finalM.OutputsWithin x (headerTransform k (enc x))
      (c * (x.length + 1) ^ d + 2 * (enc x).length + 2 +
        C * ((enc x).length + 1) ^ D) := by
    intro x
    rw [headerTransform_encode k (f x) (hvalid x)]
    exact BitMachineComposition.composition_outputsWithin M
      (Paper2.HeaderWordRun.machine k) (hM x) (hHeader (f x) hk)
  have hp : BitMachine.Polytime (headerTransform k ∘ enc) :=
    BitMachineCompositionArithmetic.polytime_of_composition_bound M finalM enc
      (headerTransform k) c d C D hM hcomp
  have heq : (headerTransform k ∘ enc) =
      (fun x => Paper2.HeaderWordRun.headeredWord k (f x)) := by
    funext x
    exact headerTransform_encode k (f x) (hvalid x)
  rw [heq] at hp
  exact hp

theorem canonicalClassifierWord_polytime_of_encoded (g : ℕ)
    (hg : 1 < g)
    (G : Paper2.YaoX05Draft.GLSourceDraft (v27GapParameter g))
    (hencoded : BitMachine.Polytime (fun input =>
      encodeInstance (sourceCanonicalInstance g G input))) :
    BitMachine.Polytime (canonicalClassifierWord g G) := by
  have hk : 0 < g - 1 := by omega
  have hp := header_from_encoded_polytime
    (sourceCanonicalInstance g G) (sourceCanonicalInstance_valid g G)
    hencoded (g - 1) hk
  simpa only [canonicalClassifierWord, canonicalEstimatorWord,
    Paper2.HeaderWordRun.headeredWord, Paper2.HeaderWordRun.matrix,
    AFront.Projection.matrixWord, Paper2.AModel.matrixWord] using hp

#print axioms CurrentAdditive.SmallBias.header_from_encoded_polytime
#print axioms CurrentAdditive.SmallBias.canonicalClassifierWord_polytime_of_encoded

end CurrentAdditive.SmallBias
