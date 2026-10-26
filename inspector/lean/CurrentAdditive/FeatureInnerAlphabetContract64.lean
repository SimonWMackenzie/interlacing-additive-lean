import CurrentAdditive.FeatureInnerAlphabetRun64
import CurrentAdditive.SourceContextScheduler64
import CurrentAdditive.CylinderSchedulerPost64

/-! The physical extension callback for each occurrence in one encoded alphabet. -/

noncomputable section

namespace CurrentAdditive.FeatureInnerAlphabetContract64

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.Wide64ContextListScheduler
open CurrentAdditive.SourceContextScheduler64
open CurrentAdditive.GaussListContext
open CurrentAdditive.FeatureInnerAlphabetRun64

def original (ys : List Nat) : List (List Bool) := labelWords ys

private theorem packed_run (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hsplit : pre ++ word :: suffix = original ys) :
    ∃ z : Nat × (TM2.Cfg (fun _ : Fin 64 => Bool) _ _),
      z.2 = ((advance FeatureExtensionCompose64.cleanedProgram)^[z.1])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
          ((FeaturePairRaw64.control,
            (((), none),
              (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                ((), none)))), ((), none)),
          selected j c pre word suffix (body ++ joined (piece j c) pre)⟩ :
            TM2.Cfg (fun _ : Fin 64 => Bool) _ _) ∧
      z.2.l = none ∧
      z.2.stk 9 = body ++ joined (piece j c) pre ++ piece j c word ∧
      z.2.stk 8 = (selected j c pre word suffix
        (body ++ joined (piece j c) pre)) 8 ∧
      z.2.stk 10 = (selected j c pre word suffix
        (body ++ joined (piece j c) pre)) 10 ∧
      z.2.stk 12 = (selected j c pre word suffix
        (body ++ joined (piece j c) pre)) 12 ∧
      z.2.stk 13 = (selected j c pre word suffix
        (body ++ joined (piece j c) pre)) 13 ∧
      z.2.stk 15 = (selected j c pre word suffix
        (body ++ joined (piece j c) pre)) 15 ∧
      (∀ k : Fin 64, 16 ≤ k.val → z.2.stk k = []) := by
  obtain ⟨t, hhalt, h9, h8, h10, h12, h13, h15, hhigh⟩ :=
    reachable_label_run j c ys pre word suffix hsplit
      (body ++ joined (piece j c) pre)
  exact ⟨(t, _), rfl, hhalt, by simpa [List.append_assoc] using h9,
    h8, h10, h12, h13, h15, hhigh⟩

private noncomputable def runData (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :=
  if h : pre ++ word :: suffix = original ys then
    Classical.choose (packed_run j c ys body pre word suffix h)
  else (0, (⟨none, ((FeaturePairRaw64.control,
    (((), none), (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
      ((), none)))), ((), none)), fun _ => []⟩ :
      TM2.Cfg (fun _ : Fin 64 => Bool) _ _))

private theorem runData_spec (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool))
    (hsplit : pre ++ word :: suffix = original ys) :
    let z := runData j c ys body pre word suffix
    z.2 = ((advance FeatureExtensionCompose64.cleanedProgram)^[z.1])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
          ((FeaturePairRaw64.control,
            (((), none),
              (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                ((), none)))), ((), none)),
          selected j c pre word suffix (body ++ joined (piece j c) pre)⟩ :
            TM2.Cfg (fun _ : Fin 64 => Bool) _ _) ∧
    z.2.l = none ∧
    z.2.stk 9 = body ++ joined (piece j c) pre ++ piece j c word ∧
    z.2.stk 8 = (selected j c pre word suffix
      (body ++ joined (piece j c) pre)) 8 ∧
    z.2.stk 10 = (selected j c pre word suffix
      (body ++ joined (piece j c) pre)) 10 ∧
    z.2.stk 12 = (selected j c pre word suffix
      (body ++ joined (piece j c) pre)) 12 ∧
    z.2.stk 13 = (selected j c pre word suffix
      (body ++ joined (piece j c) pre)) 13 ∧
    z.2.stk 15 = (selected j c pre word suffix
      (body ++ joined (piece j c) pre)) 15 ∧
    (∀ k : Fin 64, 16 ≤ k.val → z.2.stk k = []) := by
  dsimp only [runData]
  rw [dif_pos hsplit]
  exact Classical.choose_spec (packed_run j c ys body pre word suffix hsplit)

def contract (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool) :
    SourceCallbackContract
      FeatureExtensionCompose64.cleanedProgram
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel FeaturePairRaw64.start))
      ((FeaturePairRaw64.control,
        (((), none),
          (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
            ((), none)))), ((), none))
      (piece j c) body j.bits (original ys) where
  extra := extra c
  time := fun pre word suffix =>
    (runData j c ys body pre word suffix).1
  control := fun pre word suffix =>
    (runData j c ys body pre word suffix).2.var
  state := fun pre word suffix =>
    (runData j c ys body pre word suffix).2.stk
  callback_run := by
    intro pre word suffix hsplit
    have hr := (runData_spec j c ys body pre word suffix hsplit).1
    have hhalt := (runData_spec j c ys body pre word suffix hsplit).2.1
    have hselected :
        selected j c pre word suffix (body ++ joined (piece j c) pre) =
        (Wide64ContextPreservingScan.frame
          (foreignBank (body ++ joined (piece j c) pre)
            j.bits suffix.length (extra c))
          (⟨none,
            CylinderContextScanStep.getterControl
              (PreservingV2Program.v2Control
                (IndexedV2Program.indexControl
                  (SourceListMachineFields.coreControl
                    (some true, false), none))),
            CylinderContextScanStep.selectedBank
              (SourceListEncoding.encode (original ys))
              (SourceListEncoding.fields suffix) word pre.length⟩ :
              CylinderContextScanStep.Config)).stk := by
      simp only [selected, hsplit, original]
    have hz : (runData j c ys body pre word suffix).2 =
        ⟨none, (runData j c ys body pre word suffix).2.var,
          (runData j c ys body pre word suffix).2.stk⟩ := by
      cases h : (runData j c ys body pre word suffix).2 with
      | mk l v T =>
        cases l with
        | none => simp
        | some l => simp [h] at hhalt
    dsimp only
    rw [← hselected, ← hr]
    exact hz
  post := by
    intro pre word suffix hsplit
    obtain ⟨_, _, h9, h8, h10, h12, h13, h15, hhigh⟩ :=
      runData_spec j c ys body pre word suffix hsplit
    let T := (runData j c ys body pre word suffix).2.stk
    have hsource : T 8 =
        SourceListEncoding.encode (pre ++ word :: suffix) := by
      exact h8.trans (selected_scheduler_banks j c pre word suffix
        (body ++ joined (piece j c) pre)).1
    have hindex : T 10 = List.replicate pre.length true := by
      exact h10.trans (selected_scheduler_banks j c pre word suffix
        (body ++ joined (piece j c) pre)).2.1
    have hcontext : T 12 = j.bits := by
      exact h12.trans (selected_banks j c pre word suffix
        (body ++ joined (piece j c) pre)).2.2.1
    have hfuel : T 13 = List.replicate suffix.length true := by
      exact h13.trans (selected_scheduler_banks j c pre word suffix
        (body ++ joined (piece j c) pre)).2.2
    have hextra : ∀ k : Fin 64, 15 ≤ k.val → T k = extra c k := by
      intro k hk
      by_cases hkey : k = 15
      · subst k
        exact h15.trans (selected_high j c pre word suffix
          (body ++ joined (piece j c) pre) 15 (by decide))
      · exact (hhigh k (by omega)).trans (by simp [extra, hkey])
    have hpost := CylinderSchedulerPost64.callback_post pre word suffix
      (body ++ joined (piece j c) pre) j.bits (extra c) T
      (piece j c word) hsource (by simpa [List.append_assoc] using h9)
      hindex hcontext hfuel hextra
    simpa only [List.append_assoc, joined_append_one, hsplit] using hpost

#print axioms contract

/-- One fixed physical Fin64 program traverses the entire encoded alphabet,
including repeated labels, and appends each resulting descriptor in order. -/
theorem physical_alphabet_scan (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) (body : List Bool) :
    let C := contract j c ys body
    let original := original ys
    let source := SourceListEncoding.encode original
    ∃ t ≤ SourceContextScheduler64.remainingBudget
        FeatureExtensionCompose64.cleanedProgram
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel FeaturePairRaw64.start))
        ((FeaturePairRaw64.control,
          (((), none),
            (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
              ((), none)))), ((), none))
        (piece j c) body j.bits original C [] original,
      ∃ vFinal,
      Wide64ContextListScheduler.run
        FeatureExtensionCompose64.cleanedProgram
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel FeaturePairRaw64.start))
        ((FeaturePairRaw64.control,
          (((), none),
            (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
              ((), none)))), ((), none)) t
        ⟨some (.inr (.inr .check)),
          Wide64ContextListScheduler.getterControl
            ((contract j c ys body).control [] [] [])
            (CylinderContextScanStep.copyControl ((), none)),
          (Wide64ContextPreservingScan.frame
            (foreignBank body j.bits original.length (extra c))
            (CylinderContextScanStep.initial source 0)).stk⟩ =
        ⟨none, vFinal,
          (Wide64ContextPreservingScan.frame
            (foreignBank (body ++ joined (piece j c) original)
              j.bits 0 (extra c))
            (CylinderContextScanStep.initial source
              original.length)).stk⟩ := by
  classical
  have hr := SourceContextScheduler64.run_remaining
    FeatureExtensionCompose64.cleanedProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel FeaturePairRaw64.start))
    ((FeaturePairRaw64.control,
      (((), none),
        (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
          ((), none)))), ((), none))
    (piece j c) body j.bits (original ys)
    (contract j c ys body) [] (original ys) (by simp)
    (Wide64ContextListScheduler.getterControl
      ((contract j c ys body).control [] [] [])
      (CylinderContextScanStep.copyControl ((), none)))
  simpa only [List.nil_append, List.append_nil, List.length_nil, joined,
    List.flatMap_nil, contract] using hr

#print axioms physical_alphabet_scan

theorem joined_exact (j : Nat) (c : List (Nat × Nat))
    (ys : List Nat) :
    joined (piece j c) (original ys) =
      SourceListEncoding.fields
        (ys.map (fun y =>
          CurrentAdditive.CylinderFeatureCodec.encodeFeature ((j,y)::c))) := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
      simp only [original, labelWords, List.map_cons,
        joined, List.flatMap_cons, SourceListEncoding.fields,
        List.map_cons]
      rw [show piece j c y.bits =
          EthInapproximability.CurrentPaper.EncodedCommunication.natField
            (CurrentAdditive.CylinderFeatureCodec.encodeFeature ((j,y)::c)).length ++
          CurrentAdditive.CylinderFeatureCodec.encodeFeature ((j,y)::c) by
          simp [piece, bitsValue_bits]]
      rw [← ih]
      rfl

#print axioms joined_exact

end CurrentAdditive.FeatureInnerAlphabetContract64
