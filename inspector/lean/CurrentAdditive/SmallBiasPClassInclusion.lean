import CurrentAdditive.SmallBiasDeterministicClass
import Paper2.NPTruncRun
import EthInapproximability.CurrentPaper.BankFieldProjection

/-!
# The standard P subset NP inclusion in this exact encoded model

The verifier ignores its witness after the concrete truncating pair program
discards it. The physical one-field projection then recovers the input, so
an existing polynomial-time decider serves as the verifier. This closes the
routine class-inclusion side needed to spell the paper's `P=NP` conclusion.
-/

namespace CurrentAdditive.SmallBias

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open EthInapproximability.CurrentPaper.EncodedComplexity

def firstPairField (code : List Bool) : List Bool :=
  BankFieldProjection.result (0 : Fin 1)
    (NPOwner1.Trunc.result 0 0 id code)

theorem firstPairField_pair (input witness : List Bool) :
    firstPairField (pair input witness) = input := by
  have henc : BitMachineBankCodec.encode (fun _ : Fin 1 => input) = field input := by
    simp [BitMachineBankCodec.encode, BitMachineBankCodec.encodeFrom]
  change BankFieldProjection.result (0 : Fin 1)
    (NPOwner1.Trunc.result 0 0 id (pair input witness)) = input
  rw [NPOwner1.Trunc.result_pair]
  simp only [id_eq, Nat.zero_mul, List.take_zero, pair, List.append_nil]
  rw [← henc]
  exact BankFieldProjection.result_encode (0 : Fin 1) _

theorem firstPairField_polytime : BitMachine.Polytime firstPairField :=
  BitMachineComposition.polytime_comp
    (NPOwner1.Trunc.polytime_result
      ComplexityReductionClosure.polytime_id 0 0)
    (BankFieldProjection.polytime (0 : Fin 1))

theorem inP_subset_inNP (L : BinaryLanguage)
    (hP : ComplexityReductionClosure.InP L) : InNP L := by
  obtain ⟨dec, htime, hdec⟩ := hP
  refine ⟨fun code => dec (firstPairField code),
    BitMachineComposition.polytime_comp firstPairField_polytime htime,
    0, 0, ?_⟩
  intro input
  rw [hdec input]
  constructor
  · intro hd
    refine ⟨[], by simp, ?_⟩
    simpa only [firstPairField_pair] using hd
  · rintro ⟨witness, _, hw⟩
    simpa only [firstPairField_pair] using hw

def PEqualsNP : Prop :=
  ∀ L : BinaryLanguage, ComplexityReductionClosure.InP L ↔ InNP L

theorem p_equals_np_of_np_subset_p
    (h : ∀ L, InNP L → ComplexityReductionClosure.InP L) :
    PEqualsNP := by
  intro L
  exact ⟨inP_subset_inNP L, h L⟩

theorem canonical_p_equals_np_fixed_error
    (GF : (t : ℕ) → Paper2.YaoX05Draft.GLSourceDraft t)
    (L3 : BinaryLanguage) (hL : ∀ t, (GF t).L = L3)
    (hard : NPHard L3)
    (u : ℝ) (hu : 0 ≤ u)
    (est : List Bool → List Bool) (μ : Paper2.YaoBppDraft.YaoMeasure)
    (hest : DeterministicEstimatesYao est μ u)
    (hclock : BitMachine.Polytime (fun input =>
      [canonicalDetDecision (sourceEstimatorGap u)
        (GF (v27GapParameter (sourceEstimatorGap u))) est input])) :
    PEqualsNP :=
  p_equals_np_of_np_subset_p
    (canonical_np_subset_p_fixed_error GF L3 hL hard u hu est μ hest hclock)

#print axioms CurrentAdditive.SmallBias.firstPairField_pair
#print axioms CurrentAdditive.SmallBias.inP_subset_inNP
#print axioms CurrentAdditive.SmallBias.canonical_p_equals_np_fixed_error

end CurrentAdditive.SmallBias
