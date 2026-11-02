import CurrentAdditive.RatioCoefficientLookup
import CurrentAdditive.RatioRequestSerializer

set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 4096

/-! A concrete update-request producer for the currently selected source entry:
read its indexed Gauss coefficient, copy the fixed selected scalar, then
serialize all three fields. Every read, copy, clearing and field write is
executed by a fixed finite-control program. -/

namespace CurrentAdditive.RatioUpdateItem

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MinimumRatioCallbackLayout

noncomputable def scalarSlots : Fin 3 ↪ Stack where
  toFun i := low (![25,29,30] i)
  inj' := by
    intro a b h
    have hh := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;> simp_all [low]

noncomputable def scalarProgram := ExactParameterBranchInstall.copyProgram scalarSlots

noncomputable def prepProgram := BitMachineRawSequence.program
  RatioCoefficientLookup.fullProgram scalarProgram .scan
  RatioCoefficientLookup.fullControl none

abbrev PrepLabel := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label RatioCoefficientLookup.Label RatioCoefficientLookup.ClearLabel)
  BitMachineCopy.Label
abbrev PrepControl := (RatioCoefficientLookup.Control × RatioCoefficientLookup.ClearControl) ×
  Option Bool

noncomputable def prepStart : PrepLabel :=
  BitMachineRawSequence.leftLabel RatioCoefficientLookup.fullStart
noncomputable def prepControl : PrepControl := (RatioCoefficientLookup.fullControl,none)

noncomputable def program := BitMachineRawSequence.program prepProgram
  RatioRequestSerializer.program (.inl (.emit 0)) prepControl none

abbrev Label := BitMachineRawSequence.Label PrepLabel RatioRequestSerializer.Label
abbrev Control := PrepControl × Option Bool

noncomputable def start : Label := BitMachineRawSequence.leftLabel prepStart
noncomputable def control : Control := (prepControl,none)

noncomputable def clock (pre : List (List Bool)) (c : List Bool)
    (tail : List (List Bool)) (old lambda : List Bool) : Nat :=
  RatioCoefficientLookup.clock pre c tail + (2*lambda.length+2) + 1 +
    (old.length+1+(lambda.length+1)+(c.length+1)+
      (RatioRequestSerializer.bytes old lambda c).length+3) + 1

theorem item_run (S : Bank) (pre : List (List Bool)) (c : List Bool)
    (tail : List (List Bool)) (old lambda : List Bool)
    (hsource : S (RatioCoefficientLookup.locate 8) =
      SourceListEncoding.encode (pre ++ c :: tail))
    (hindex : S (RatioCoefficientLookup.locate 10) =
      List.replicate pre.length true)
    (hlookup : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      S (RatioCoefficientLookup.locate j) = [])
    (hold : S (low 6) = old) (hlambda : S (low 25) = lambda)
    (h26 : S (low 26) = []) (h27 : S (low 27) = [])
    (h28 : S (low 28) = []) (h29 : S (low 29) = [])
    (h30 : S (low 30) = []) :
    ∃ t ≤ clock pre c tail old lambda,
      ((advance program)^[t])
        (⟨some start, control, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control,
          Function.update (Function.update S (low 6) []) (low 28)
            (RatioRequestSerializer.bytes old lambda c)⟩ := by
  have hne (a b : Fin 32) (h : a ≠ b) : low a ≠ low b := by
    intro he
    apply h
    apply Fin.ext
    exact congrArg (fun j : Stack => j.val) he
  have hget6 : RatioCoefficientLookup.locate 6 = low 21 := rfl
  have h21 : S (low 21) = [] := by
    simpa only [hget6] using hlookup 6 (by decide) (by decide)
  let S1 := Function.update S (low 21) c
  let S2 := Function.update S1 (low 29) lambda
  obtain ⟨a,ha,hrA⟩ := RatioCoefficientLookup.full_run S pre c tail
    hsource hindex hlookup
  have hscalar : S1 (scalarSlots 0) = lambda := by
    simp [S1,scalarSlots,Function.update_of_ne,hne 25 21 (by decide),hlambda]
  have htarget : S1 (scalarSlots 1) = [] := by
    simp [S1,scalarSlots,Function.update_of_ne,hne 29 21 (by decide),h29]
  have hwork : S1 (scalarSlots 2) = [] := by
    simp [S1,scalarSlots,Function.update_of_ne,hne 30 21 (by decide),h30]
  obtain ⟨b,hb,hrB⟩ := ExactParameterBranchInstall.copy_run scalarSlots
    S1 lambda hscalar htarget hwork
  obtain ⟨ab,hab,hrAB⟩ := BitMachineRawSequence.runs
    RatioCoefficientLookup.fullProgram scalarProgram
    RatioCoefficientLookup.fullStart .scan
    RatioCoefficientLookup.fullControl RatioCoefficientLookup.fullControl
    none none S S1 S2 a b
    (by simpa only [S1,hget6] using hrA)
    (by simpa only [scalarProgram,scalarSlots,S2] using hrB)
  have hser0 : S2 (RatioRequestSerializer.locate (.inl 0)) = old := by
    simp [S2,S1,RatioRequestSerializer.locate,RatioRequestSerializer.localSlot,
      Function.update_of_ne,hne 6 29 (by decide),hne 6 21 (by decide),hold]
  have hser1 : S2 (RatioRequestSerializer.locate (.inl 1)) = lambda := by
    simp [S2,RatioRequestSerializer.locate,RatioRequestSerializer.localSlot]
  have hser2 : S2 (RatioRequestSerializer.locate (.inl 2)) = c := by
    simp [S2,S1,RatioRequestSerializer.locate,RatioRequestSerializer.localSlot,
      Function.update_of_ne,hne 21 29 (by decide)]
  have hserblank : ∀ i : Fin 3, S2 (RatioRequestSerializer.locate (.inr i)) = [] := by
    intro i
    fin_cases i
    · change S2 (low 26) = []
      simp only [S2,S1,Function.update_of_ne (hne 26 29 (by decide)),
        Function.update_of_ne (hne 26 21 (by decide)),h26]
    · change S2 (low 27) = []
      simp only [S2,S1,Function.update_of_ne (hne 27 29 (by decide)),
        Function.update_of_ne (hne 27 21 (by decide)),h27]
    · change S2 (low 28) = []
      simp only [S2,S1,Function.update_of_ne (hne 28 29 (by decide)),
        Function.update_of_ne (hne 28 21 (by decide)),h28]
  obtain ⟨d,hd,hrD⟩ := RatioRequestSerializer.serialize_request S2 old lambda c
    hser0 hser1 hser2 hserblank
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs prepProgram
    RatioRequestSerializer.program prepStart (.inl (.emit 0))
    prepControl prepControl none none S S2
    (RatioRequestSerializer.result S2 old lambda c) ab d
    (by simpa only [prepProgram,prepStart,prepControl] using hrAB) hrD
  have hout : RatioRequestSerializer.result S2 old lambda c =
      Function.update (Function.update S (low 6) []) (low 28)
        (RatioRequestSerializer.bytes old lambda c) := by
    funext j
    by_cases h6 : j = low 6
    · subst j
      simp [RatioRequestSerializer.result,RatioRequestSerializer.locate,
        RatioRequestSerializer.localSlot,Function.update_of_ne,
        hne 6 28 (by decide),hne 6 21 (by decide),hne 6 29 (by decide)]
    · by_cases h28j : j = low 28
      · subst j
        simp [RatioRequestSerializer.result,RatioRequestSerializer.locate,
          RatioRequestSerializer.localSlot]
      · by_cases h21j : j = low 21
        · subst j
          simp [RatioRequestSerializer.result,RatioRequestSerializer.locate,
            RatioRequestSerializer.localSlot,Function.update_of_ne,
            hne 21 28 (by decide),hne 21 6 (by decide),h21]
        · by_cases h29j : j = low 29
          · subst j
            simp [RatioRequestSerializer.result,RatioRequestSerializer.locate,
              RatioRequestSerializer.localSlot,Function.update_of_ne,
              hne 29 28 (by decide),hne 29 6 (by decide),hne 29 21 (by decide),h29]
          · simp [RatioRequestSerializer.result,RatioRequestSerializer.locate,
              RatioRequestSerializer.localSlot,S2,S1,Function.update_of_ne,
              h6,h28j,h21j,h29j]
  rw [hout] at hr
  refine ⟨t,?_,?_⟩
  · unfold clock
    omega
  · simpa only [program,start,control] using hr

theorem actual_request_run (S : Bank) (pre tail : List (List Bool))
    (old : CodeDSourceCodecV2.Entry) (lambda coeff : ℚ)
    (hsource : S (RatioCoefficientLookup.locate 8) =
      SourceListEncoding.encode (pre ++
        CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat coeff) :: tail))
    (hindex : S (RatioCoefficientLookup.locate 10) =
      List.replicate pre.length true)
    (hlookup : ∀ j : CylinderContextScanStep.Stack, j ≠ 8 → j ≠ 10 →
      S (RatioCoefficientLookup.locate j) = [])
    (hold : S (low 6) = CodeDSourceCodecV2.encodeEntry old)
    (hlambda : S (low 25) =
      CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat lambda))
    (h26 : S (low 26) = []) (h27 : S (low 27) = [])
    (h28 : S (low 28) = []) (h29 : S (low 29) = [])
    (h30 : S (low 30) = []) :
    ∃ t ≤ clock pre (CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat coeff))
        tail (CodeDSourceCodecV2.encodeEntry old)
        (CodeDCodec.encodeRawRat (CodeDCanonicalSourceV2.rawOfRat lambda)),
      ((advance program)^[t])
        (⟨some start, control, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, control,
          Function.update (Function.update S (low 6) []) (low 28)
            (CodeDUpdateProductPairFields.requestPacket old lambda coeff)⟩ := by
  simpa only [RatioRequestSerializer.bytes_request] using
    item_run S pre _ tail _ _ hsource hindex hlookup hold hlambda
      h26 h27 h28 h29 h30

#print axioms actual_request_run

end CurrentAdditive.RatioUpdateItem
