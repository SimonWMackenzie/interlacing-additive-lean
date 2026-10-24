import CurrentAdditive.FeaturePairRaw64
import CurrentAdditive.V2FeatureFrameAppend64Total
import CurrentAdditive.FeatureClearHigh64

/-! A fixed Fin64 callback body for one alphabet occurrence. -/

namespace CurrentAdditive.FeatureExtensionCompose64

open Turing Turing.TM2
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CylinderFeatureCodec
open CurrentAdditive.MinimumRatioContext

abbrev Bank := Fin 64

def raw (j y : Nat) (c : List (Nat × Nat)) : List Bool :=
  encodeFeature ((j,y)::c)

theorem staged_extension (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat)) (body : List Bool)
    (hj : S 12 = j.bits) (hy : S 6 = y.bits)
    (hc : S 15 = encodeFeature c) (hbody : S 9 = body)
    (hblank : ∀ k : FeaturePreparedCallback.Stack,
      S (FeatureContext64.locate k) = [])
    (h38 : S 38 = []) :
    ∃ a ≤ FeaturePairRaw64.clock j y c,
      ∃ b ≤ V2FeatureFrameAppend64Total.bound
          (((advance FeaturePairRaw64.program)^[a])
            (⟨some FeaturePairRaw64.start, FeaturePairRaw64.control, S⟩ :
              TM2.Cfg (fun _ : Bank => Bool) _ _)).stk
          (raw j y c) body,
      ∃ (U : Bank → List Bool),
        let R := (((advance FeaturePairRaw64.program)^[a])
          (⟨some FeaturePairRaw64.start, FeaturePairRaw64.control, S⟩ :
            TM2.Cfg (fun _ : Bank => Bool) _ _)).stk
        (((advance V2FeatureFrameAppend64Total.program)^[b])
          (⟨some (BitMachineRawSequence.leftLabel
            (MachineInvokeClear.clearLabel 2 0)),
            (((), none),
              (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                ((), none))), R⟩ :
            TM2.Cfg (fun _ : Bank => Bool) _ _)).stk = U ∧
        U 9 = body ++ EncodedCommunication.natField (raw j y c).length ++ raw j y c ∧
        U 12 = S 12 ∧ U 15 = S 15 := by
  obtain ⟨a, ha, hhalt, hraw, hforeign⟩ :=
    FeaturePairRaw64.physical_raw S j y c hj hy hc hblank h38
  let R := (((advance FeaturePairRaw64.program)^[a])
    (⟨some FeaturePairRaw64.start, FeaturePairRaw64.control, S⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _)).stk
  have h9 : R 9 = body := (hforeign 9 (by decide)).trans hbody
  obtain ⟨b, hb, v, U, hrest⟩ :=
    V2FeatureFrameAppend64Total.run R (raw j y c) body hraw h9
  have hrun := hrest.1
  have hout := hrest.2.1
  have h5 := hrest.2.2.1
  have hpres := hrest.2.2.2.2
  refine ⟨a, ha, b, hb, U, ?_, ?_, ?_, ?_⟩
  · exact congrArg TM2.Cfg.stk hrun
  · simpa only [List.append_assoc] using hout
  · exact (hpres 12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by intro i; fin_cases i <;> decide)).trans
        (hforeign 12 (by decide))
  · exact (hpres 15 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by intro i; fin_cases i <;> decide)).trans
        (hforeign 15 (by decide))

noncomputable def program := BitMachineRawSequence.program
  FeaturePairRaw64.program V2FeatureFrameAppend64Total.program
  (BitMachineRawSequence.leftLabel (MachineInvokeClear.clearLabel 2 0))
  FeaturePairRaw64.control
  (((), none),
    (V2ItemFrameCore.control V2FeatureFrameLayout64.slots, ((), none)))

theorem physical_extension (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat)) (body : List Bool)
    (hj : S 12 = j.bits) (hy : S 6 = y.bits)
    (hc : S 15 = encodeFeature c) (hbody : S 9 = body)
    (hblank : ∀ k : FeaturePreparedCallback.Stack,
      S (FeatureContext64.locate k) = [])
    (h38 : S 38 = []) :
    ∃ a ≤ FeaturePairRaw64.clock j y c,
      ∃ t ≤ a +
          V2FeatureFrameAppend64Total.bound
            (((advance FeaturePairRaw64.program)^[a])
              (⟨some FeaturePairRaw64.start, FeaturePairRaw64.control, S⟩ :
                TM2.Cfg (fun _ : Bank => Bool) _ _)).stk
            (raw j y c) body + 1,
      ∃ (v : GaussV2BodyAppend64.Control) (U : Bank → List Bool),
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel FeaturePairRaw64.start),
            (FeaturePairRaw64.control,
              (((), none),
                (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                  ((), none)))), S⟩ :
            TM2.Cfg (fun _ : Bank => Bool) _ _) =
          ⟨none,
            (FeaturePairRaw64.control,
              (((), none),
                (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,v))),
            U⟩ ∧
        U 9 = body ++ (EncodedCommunication.natField (raw j y c).length ++
          raw j y c) ∧ U 12 = S 12 ∧ U 15 = S 15 ∧
        (∀ k : Bank, k.val < 16 → k ≠ 5 → k ≠ 7 → k ≠ 9 →
          k ≠ 11 → k ≠ 14 → U k = S k) := by
  obtain ⟨a, ha, hhalt, hraw, hforeign⟩ :=
    FeaturePairRaw64.physical_raw S j y c hj hy hc hblank h38
  let z := ((advance FeaturePairRaw64.program)^[a])
    (⟨some FeaturePairRaw64.start, FeaturePairRaw64.control, S⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _)
  change z.l = none at hhalt
  have hz : z = ⟨none, z.var, z.stk⟩ := by
    cases h : z with
    | mk l v T =>
        cases l with
        | none => simp [h]
        | some l => simp [h] at hhalt
  have h9 : z.stk 9 = body := (hforeign 9 (by decide)).trans hbody
  obtain ⟨b, hb, v, U, hrest⟩ :=
    V2FeatureFrameAppend64Total.run z.stk (raw j y c) body hraw h9
  have hrun := hrest.1
  have hout := hrest.2.1
  have hpres := hrest.2.2.2.2
  obtain ⟨t, ht, hseq⟩ := BitMachineRawSequence.runs
    FeaturePairRaw64.program V2FeatureFrameAppend64Total.program
    FeaturePairRaw64.start
    (BitMachineRawSequence.leftLabel (MachineInvokeClear.clearLabel 2 0))
    FeaturePairRaw64.control z.var
    (((), none),
      (V2ItemFrameCore.control V2FeatureFrameLayout64.slots, ((), none)))
    (((), none),
      (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,v))
    S z.stk U a b hz (by simpa only using hrun)
  refine ⟨a, ha, t, ?_, v, U, ?_, hout, ?_, ?_, ?_⟩
  · change t ≤ a + V2FeatureFrameAppend64Total.bound z.stk
        (raw j y c) body + 1
    omega
  · simpa only [program] using hseq
  · exact (hpres 12 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by intro i; fin_cases i <;> decide)).trans
        (hforeign 12 (by decide))
  · exact (hpres 15 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by intro i; fin_cases i <;> decide)).trans
        (hforeign 15 (by decide))
  · intro k hk hk5 hk7 hk9 hk11 hk14
    have hm : ∀ i, k ≠ V2FeatureFrameLayout64.slots.machine i := by
      intro i h
      have hv := congrArg Fin.val h
      simp [V2FeatureFrameLayout64.slots,
        V2FeatureFrameLayout64.embedded] at hv
      omega
    exact (hpres k hk5 hk9 hk11 hk14 hk7 hm).trans
      (hforeign k (Or.inl hk))

noncomputable def cleanedProgram := BitMachineRawSequence.program
  program FeatureClearHigh64.program
  (MachineInvokeClear.clearLabel 48 0)
  (FeaturePairRaw64.control,
    (((), none),
      (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
        ((), none))))
  ((), none)

theorem physical_cleaned_extension (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat)) (body : List Bool)
    (hj : S 12 = j.bits) (hy : S 6 = y.bits)
    (hc : S 15 = encodeFeature c) (hbody : S 9 = body)
    (hblank : ∀ k : FeaturePreparedCallback.Stack,
      S (FeatureContext64.locate k) = [])
    (h38 : S 38 = []) :
    ∃ t,
      let z := ((advance cleanedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
          ((FeaturePairRaw64.control,
            (((), none),
              (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                ((), none)))), ((), none)), S⟩ :
            TM2.Cfg (fun _ : Bank => Bool) _ _)
      z.l = none ∧
      z.stk 9 = body ++
        (EncodedCommunication.natField (raw j y c).length ++ raw j y c) ∧
      z.stk 12 = S 12 ∧ z.stk 15 = S 15 ∧
      (∀ k : Bank, 16 ≤ k.val → z.stk k = []) ∧
      (∀ k : Bank, k.val < 16 → k ≠ 5 → k ≠ 7 → k ≠ 9 →
        k ≠ 11 → k ≠ 14 → z.stk k = S k) := by
  obtain ⟨a, ha, t1, ht1, v, U, hfirst, hout, h12, h15, hlow⟩ :=
    physical_extension S j y c body hj hy hc hbody hblank h38
  have hsecond := FeatureClearHigh64.run U
  obtain ⟨t, ht, hseq⟩ := BitMachineRawSequence.runs
    program FeatureClearHigh64.program
    (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)
    (MachineInvokeClear.clearLabel 48 0)
    (FeaturePairRaw64.control,
      (((), none),
        (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
          ((), none))))
    (FeaturePairRaw64.control,
      (((), none),
        (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,v)))
    ((), none) ((), none) S U (FeatureClearHigh64.cleaned U)
    t1 (FeatureClearHigh64.time U) hfirst hsecond
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg TM2.Cfg.l hseq
  · have hh := congrArg (fun z => z.stk (9 : Bank)) hseq
    simpa only [cleanedProgram, FeatureClearHigh64.cleaned_low U 9 (by decide)]
      using hh.trans hout
  · have hh := congrArg (fun z => z.stk (12 : Bank)) hseq
    simpa only [cleanedProgram, FeatureClearHigh64.cleaned_low U 12 (by decide)]
      using hh.trans h12
  · have hh := congrArg (fun z => z.stk (15 : Bank)) hseq
    simpa only [cleanedProgram, FeatureClearHigh64.cleaned_low U 15 (by decide)]
      using hh.trans h15
  · intro k hk
    have hh := congrArg (fun z => z.stk k) hseq
    simpa only [cleanedProgram, FeatureClearHigh64.cleaned_high U k hk] using hh
  · intro k hk hk5 hk7 hk9 hk11 hk14
    have hh := congrArg (fun z => z.stk k) hseq
    have hh' :
        (((advance cleanedProgram)^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
            ((FeaturePairRaw64.control,
              (((), none),
                (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                  ((), none)))), ((), none)), S⟩ :
              TM2.Cfg (fun _ : Bank => Bool) _ _)).stk k =
            FeatureClearHigh64.cleaned U k := by
      simpa only [cleanedProgram] using hh
    rw [FeatureClearHigh64.cleaned_low U k hk] at hh'
    exact hh'.trans (hlow k hk hk5 hk7 hk9 hk11 hk14)

#print axioms staged_extension
#print axioms physical_extension
#print axioms physical_cleaned_extension

end CurrentAdditive.FeatureExtensionCompose64
