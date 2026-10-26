import CurrentAdditive.FeatureInnerAlphabetContract64
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! A fixed, disjoint 64-bank placement of the complete alphabet scan.
Banks 0--63 remain available for the outer old-feature scheduler. -/

noncomputable section

namespace CurrentAdditive.FeatureInnerLift128

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.FeatureInnerAlphabetContract64
open CurrentAdditive.FeatureInnerAlphabetRun64
open CurrentAdditive.Wide64ContextListScheduler
open CurrentAdditive.GaussListContext

abbrev OuterStack := Fin 128

def slot : Fin 64 ↪ OuterStack where
  toFun i := ⟨64 + i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp at hv
    omega

def innerProgram := Wide64ContextListScheduler.program
  FeatureExtensionCompose64.cleanedProgram
  (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel FeaturePairRaw64.start))
  ((FeaturePairRaw64.control,
    (((), none),
      (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
        ((), none)))), ((), none))

def liftedProgram (l) :=
  BitMachineStackEmbedding.stmt slot id id id none (innerProgram l)

def innerStart (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool) :=
  Wide64ContextListScheduler.run
    FeatureExtensionCompose64.cleanedProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel FeaturePairRaw64.start))
    ((FeaturePairRaw64.control,
      (((), none),
        (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
          ((), none)))), ((), none)) 0
    ⟨some (.inr (.inr .check)),
      Wide64ContextListScheduler.getterControl
        ((contract j c ys body).control [] [] [])
        (CylinderContextScanStep.copyControl ((), none)),
      (Wide64ContextPreservingScan.frame
        (foreignBank body j.bits (original ys).length (extra c))
        (CylinderContextScanStep.initial
          (SourceListEncoding.encode (original ys)) 0)).stk⟩

def liftedStart (foreign : OuterStack → List Bool)
    (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool) :=
  BitMachineStackEmbedding.cfg slot foreign id id none
    (innerStart j c ys body)

theorem lifted_alphabet_scan (foreign : OuterStack → List Bool)
    (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool) :
    ∃ t,
      let z := ((advance liftedProgram)^[t])
        (liftedStart foreign j c ys body)
      z.l = none ∧
      z.stk 73 = body ++
        SourceListEncoding.fields
          (ys.map (fun y =>
            CurrentAdditive.CylinderFeatureCodec.encodeFeature ((j,y)::c))) ∧
      (∀ k : OuterStack, k.val < 64 → z.stk k = foreign k) := by
  classical
  obtain ⟨t, _, vFinal, hrun⟩ :=
    physical_alphabet_scan j c ys body
  let I := innerStart j c ys body
  have hI : I =
      ⟨some (.inr (.inr .check)),
        Wide64ContextListScheduler.getterControl
          ((contract j c ys body).control [] [] [])
          (CylinderContextScanStep.copyControl ((), none)),
        (Wide64ContextPreservingScan.frame
          (foreignBank body j.bits (original ys).length (extra c))
          (CylinderContextScanStep.initial
            (SourceListEncoding.encode (original ys)) 0)).stk⟩ := by
    rfl
  have hhalt : (((advance innerProgram)^[t]) I).l = none := by
    simpa only [innerProgram, I, hI,
      Wide64ContextListScheduler.run] using congrArg TM2.Cfg.l hrun
  obtain ⟨u, _, hlift⟩ := BitMachineStackEmbedding.outputs
    slot foreign id id id (by intro; rfl) none
    innerProgram liftedProgram (by intro; rfl) I t hhalt
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [show liftedStart foreign j c ys body =
        BitMachineStackEmbedding.cfg slot foreign id id none I by rfl,
      hlift]
    simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hhalt]
  · rw [show liftedStart foreign j c ys body =
        BitMachineStackEmbedding.cfg slot foreign id id none I by rfl,
      hlift]
    have hbank := BitMachineStackEmbedding.bank_at slot foreign
      ((((advance innerProgram)^[t]) I).stk) (9 : Fin 64)
    have h9 : ((((advance innerProgram)^[t]) I).stk) 9 =
        body ++ joined (piece j c) (original ys) := by
      change (((advance innerProgram)^[t]) I) = _ at hrun
      have he := congrArg (fun z => z.stk (9 : Fin 64)) hrun
      have hp := Wide64ContextPreservingScan.output_preserved
        (foreignBank (body ++ joined (piece j c) (original ys))
          j.bits 0 (extra c))
        (CylinderContextScanStep.initial
          (SourceListEncoding.encode (original ys)) (original ys).length)
      simpa [foreignBank] using he.trans hp
    simpa only [slot, joined_exact] using hbank.trans h9
  · intro k hk
    rw [show liftedStart foreign j c ys body =
        BitMachineStackEmbedding.cfg slot foreign id id none I by rfl,
      hlift]
    apply BitMachineStackEmbedding.bank_outside
    rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    simp [slot] at hv
    omega

#print axioms lifted_alphabet_scan

end CurrentAdditive.FeatureInnerLift128
