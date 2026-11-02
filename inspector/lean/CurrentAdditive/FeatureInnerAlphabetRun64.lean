import CurrentAdditive.FeatureExtensionCompose64
import CurrentAdditive.CylinderSchedulerPost64
import CurrentAdditive.SourceContextScheduler64

/-! Fixed Fin64 scan of the actual alphabet label packet for one old
descriptor. -/

namespace CurrentAdditive.FeatureInnerAlphabetRun64

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.Wide64ContextListScheduler
open CurrentAdditive.GaussListContext

def labelWords (ys : List Nat) : List (List Bool) := ys.map Nat.bits

def piece (j : Nat) (c : List (Nat × Nat))
    (word : List Bool) : List Bool :=
  let r := encodeFeature ((j, bitsValue word)::c)
  natField r.length ++ r

def extra (c : List (Nat × Nat)) : Fin 64 → List Bool :=
  fun k => if k = 15 then encodeFeature c else []

noncomputable def selected (j : Nat) (c : List (Nat × Nat))
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (out : List Bool) :
    Fin 64 → List Bool :=
  (Wide64ContextPreservingScan.frame
    (foreignBank out j.bits suffix.length (extra c))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)).stk

theorem label_from_split (ys : List Nat)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hsplit : pre ++ word :: suffix = labelWords ys) :
    ∃ y ∈ ys, word = y.bits := by
  have hw : word ∈ labelWords ys := by
    rw [← hsplit]
    simp
  rcases List.mem_map.mp hw with ⟨y, hy, he⟩
  exact ⟨y, hy, he.symm⟩

theorem selected_high (j : Nat) (c : List (Nat × Nat))
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (out : List Bool)
    (k : Fin 64) (hk : 15 ≤ k.val) :
    selected j c pre word suffix out k = extra c k := by
  unfold selected
  rw [Wide64ContextPreservingScan.frame_foreign]
  · exact foreignBank_extra out j.bits suffix.length (extra c) k hk
  · rintro ⟨i, hi⟩
    have hsmall : (Wide64ContextPreservingScan.locate i).val < 15 := by
      fin_cases i <;> decide
    have hv := congrArg Fin.val hi
    omega

theorem selected_banks (j : Nat) (c : List (Nat × Nat))
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (out : List Bool) :
    let S := selected j c pre word suffix out
    S 6 = word ∧ S 9 = out ∧ S 12 = j.bits ∧
    S 15 = encodeFeature c ∧
    (∀ k : Fin 64, 16 ≤ k.val → S k = []) := by
  dsimp only
  have h6 := Wide64ContextPreservingScan.selected_word
    (SourceListEncoding.encode (pre ++ word :: suffix))
    (SourceListEncoding.fields suffix) word pre.length
    (foreignBank out j.bits suffix.length (extra c))
  have h9 := Wide64ContextPreservingScan.output_preserved
    (foreignBank out j.bits suffix.length (extra c))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
  have hcontext := Wide64ContextPreservingScan.context_preserved
    (foreignBank out j.bits suffix.length (extra c))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)
  refine ⟨h6, ?_, ?_, ?_, ?_⟩
  · simpa [foreignBank] using h9
  · simpa [foreignBank] using hcontext.1
  · rw [selected_high j c pre word suffix out 15 (by decide)]
    simp [extra]
  · intro k hk
    rw [selected_high j c pre word suffix out k (by omega)]
    simp [extra, show k ≠ 15 by omega]

theorem selected_scheduler_banks (j : Nat) (c : List (Nat × Nat))
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (out : List Bool) :
    let S := selected j c pre word suffix out
    S 8 = SourceListEncoding.encode (pre ++ word :: suffix) ∧
    S 10 = List.replicate pre.length true ∧
    S 13 = List.replicate suffix.length true := by
  dsimp only
  have h8 := Wide64ContextPreservingScan.selected_source
    (SourceListEncoding.encode (pre ++ word :: suffix))
    (SourceListEncoding.fields suffix) word pre.length
    (foreignBank out j.bits suffix.length (extra c))
  have h10 := Wide64ContextPreservingScan.frame_bank
    (foreignBank out j.bits suffix.length (extra c))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config) 10
  have h13 := (Wide64ContextPreservingScan.context_preserved
    (foreignBank out j.bits suffix.length (extra c))
    (⟨none,
      CylinderContextScanStep.getterControl
        (PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none))),
      CylinderContextScanStep.selectedBank
        (SourceListEncoding.encode (pre ++ word :: suffix))
        (SourceListEncoding.fields suffix) word pre.length⟩ :
          CylinderContextScanStep.Config)).2
  refine ⟨h8, ?_, ?_⟩
  · simpa [selected, CylinderContextScanStep.selectedBank,
      Wide64ContextPreservingScan.locate] using h10
  · simpa [foreignBank] using h13

theorem selected_raw_ready (j y : Nat) (c : List (Nat × Nat))
    (pre : List (List Bool)) (suffix : List (List Bool))
    (out : List Bool) :
    let S := selected j c pre y.bits suffix out
    (∀ k : FeaturePreparedCallback.Stack,
      S (FeatureContext64.locate k) = []) ∧ S 38 = [] := by
  have hhigh := (selected_banks j c pre y.bits suffix out).2.2.2.2
  constructor
  · intro k
    apply hhigh
    have hr := FeatureContext64.locate_range k
    omega
  · exact hhigh 38 (by decide)

theorem reachable_label_run (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hsplit : pre ++ word :: suffix = labelWords ys)
    (out : List Bool) :
    let S := selected j c pre word suffix out
    ∃ t,
      let z := ((advance FeatureExtensionCompose64.cleanedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
          ((FeaturePairRaw64.control,
            (((), none),
              (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                ((), none)))), ((), none)), S⟩ :
            TM2.Cfg (fun _ : Fin 64 => Bool) _ _)
      z.l = none ∧ z.stk 9 = out ++ piece j c word ∧
      z.stk 8 = S 8 ∧ z.stk 10 = S 10 ∧
      z.stk 12 = S 12 ∧ z.stk 13 = S 13 ∧
      z.stk 15 = S 15 ∧
      (∀ k : Fin 64, 16 ≤ k.val → z.stk k = []) := by
  dsimp only
  obtain ⟨y, _, hword⟩ := label_from_split ys pre word suffix hsplit
  subst word
  let S := selected j c pre y.bits suffix out
  obtain ⟨h6, h9, h12, h15, hhigh⟩ :=
    selected_banks j c pre y.bits suffix out
  obtain ⟨hblank, h38⟩ := selected_raw_ready j y c pre suffix out
  obtain ⟨t, hhalt, hout, hp12, hp15, hafterHigh, hlow⟩ :=
    FeatureExtensionCompose64.physical_cleaned_extension S j y c out
      h12 h6 h15 h9 hblank h38
  refine ⟨t, hhalt, ?_, ?_, ?_, hp12, ?_, hp15, hafterHigh⟩
  · simpa [piece, bitsValue_bits, FeatureExtensionCompose64.raw] using hout
  · exact hlow 8 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact hlow 10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
  · exact hlow 13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)

#print axioms selected_banks
#print axioms selected_scheduler_banks
#print axioms reachable_label_run

end CurrentAdditive.FeatureInnerAlphabetRun64
