import CurrentAdditive.FeatureExtensionCompose64

/-! The actual cleaned feature-extension program, now with its complete
clock retained. Every temporary-cell cleanup is charged by the physical
program's stack-growth theorem. This is the one-extension stage used by
the forthcoming complete ordered traversal, not a feature producer alone. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace CurrentAdditive.FeatureBoundedExtension64

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.FeatureExtensionCompose64
open CurrentAdditive.CylinderFeatureCodec

def bankSize (S : Fin 64 → List Bool) : ℕ := ∑ k : Fin 64, (S k).length

theorem bank_length_le (S : Fin 64 → List Bool) (k : Fin 64) :
    (S k).length ≤ bankSize S :=
  by
    unfold bankSize
    exact Finset.single_le_sum
      (f := fun i : Fin 64 => (S i).length)
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin 64))) => Nat.zero_le (S i).length)
      (Finset.mem_univ k)

def rawCap (S : Fin 64 → List Bool) (j y : ℕ) (c : List (ℕ × ℕ)) : ℕ :=
  bankSize S + BitMachineStackGrowth.perStep FeaturePairRaw64.program *
    FeaturePairRaw64.clock j y c

def appendClock (S : Fin 64 → List Bool) (j y : ℕ)
    (c : List (ℕ × ℕ)) (body : List Bool) : ℕ :=
  2*rawCap S j y c+4 + V2ItemFrameClock.coefficient*
    ((raw j y c).length+10*rawCap S j y c+1)^2 +
    4*body.length+2*(EncodedCommunication.natField (raw j y c).length ++ raw j y c).length+9

def firstClock (S : Fin 64 → List Bool) (j y : ℕ)
    (c : List (ℕ × ℕ)) (body : List Bool) : ℕ :=
  FeaturePairRaw64.clock j y c+appendClock S j y c body+1

def clock (S : Fin 64 → List Bool) (j y : ℕ)
    (c : List (ℕ × ℕ)) (body : List Bool) : ℕ :=
  firstClock S j y c body +
    48*BitMachineStackGrowth.perStep FeatureExtensionCompose64.program *
      firstClock S j y c body+51

theorem raw_bank_bound (S : Fin 64 → List Bool) (j y : ℕ)
    (c : List (ℕ × ℕ)) (a : ℕ) (ha : a ≤ FeaturePairRaw64.clock j y c)
    (k : Fin 64) :
    ((((advance FeaturePairRaw64.program)^[a])
      (⟨some FeaturePairRaw64.start,FeaturePairRaw64.control,S⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) _ _)).stk k).length ≤ rawCap S j y c := by
  exact (BitMachineStackGrowth.run_growth FeaturePairRaw64.program _ a k).trans
    (Nat.add_le_add (bank_length_le S k) (Nat.mul_le_mul_left _ ha))

theorem append_clock_bound (S : Fin 64 → List Bool) (j y : ℕ)
    (c : List (ℕ × ℕ)) (body : List Bool)
    (a : ℕ) (ha : a ≤ FeaturePairRaw64.clock j y c) :
    V2FeatureFrameAppend64Total.bound
      (((advance FeaturePairRaw64.program)^[a])
        (⟨some FeaturePairRaw64.start,FeaturePairRaw64.control,S⟩ :
          TM2.Cfg (fun _ : Fin 64 => Bool) _ _)).stk
      (raw j y c) body ≤ appendClock S j y c body := by
  let R := (((advance FeaturePairRaw64.program)^[a])
    (⟨some FeaturePairRaw64.start,FeaturePairRaw64.control,S⟩ :
      TM2.Cfg (fun _ : Fin 64 => Bool) _ _)).stk
  have hr (k : Fin 64) : (R k).length ≤ rawCap S j y c :=
    raw_bank_bound S j y c a ha k
  have hclear : V2FeatureFrameAppend64Total.clearTime R ≤ 2*rawCap S j y c+4 := by
    unfold V2FeatureFrameAppend64Total.clearTime
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => hr (V2FeatureFrameAppend64Total.clearSlot i))
    simpa using Nat.add_le_add_right hsum 4
  have hsize : V2ItemFrameClock.inputSize V2FeatureFrameLayout64.slots R (raw j y c) ≤
      (raw j y c).length+10*rawCap S j y c := by
    unfold V2ItemFrameClock.inputSize
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun i (_ : i ∈ Finset.univ) => hr (V2ItemFrameCore.clearBank V2FeatureFrameLayout64.slots i))
    simpa using Nat.add_le_add_left hsum (raw j y c).length
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 2
  have hmul := Nat.mul_le_mul_left V2ItemFrameClock.coefficient hpow
  change V2FeatureFrameAppend64Total.bound R (raw j y c) body ≤ _
  unfold V2FeatureFrameAppend64Total.bound appendClock
  omega

theorem run (S : Fin 64 → List Bool) (j y : ℕ)
    (c : List (ℕ × ℕ)) (body : List Bool)
    (hj : S 12 = j.bits) (hy : S 6 = y.bits)
    (hc : S 15 = encodeFeature c) (hbody : S 9 = body)
    (hblank : ∀ k : FeaturePreparedCallback.Stack, S (FeatureContext64.locate k) = [])
    (h38 : S 38 = [])
    (hhigh : ∀ k : Fin 64, 16 ≤ k.val → S k = []) :
    ∃ t ≤ clock S j y c body,
      let z := ((advance cleanedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
          ((FeaturePairRaw64.control,
            (((),none),(V2ItemFrameCore.control V2FeatureFrameLayout64.slots,((),none)))),
            ((),none)),S⟩ : TM2.Cfg (fun _ : Fin 64 => Bool) _ _)
      z.l = none ∧ z.stk 9 = body ++
        (EncodedCommunication.natField (raw j y c).length ++ raw j y c) ∧
      z.stk 12 = S 12 ∧ z.stk 15 = S 15 ∧
      (∀ k : Fin 64, 16 ≤ k.val → z.stk k = []) ∧
      (∀ k : Fin 64, k.val < 16 → k ≠ 5 → k ≠ 7 → k ≠ 9 →
        k ≠ 11 → k ≠ 14 → z.stk k = S k) := by
  classical
  obtain ⟨a,ha,t1,ht1,v,U,hfirst,hout,h12,h15,hlow⟩ :=
    physical_extension S j y c body hj hy hc hbody hblank h38
  have happend := append_clock_bound S j y c body a ha
  have hfirstBound : t1 ≤ firstClock S j y c body := by
    unfold firstClock
    omega
  let I := ((advance FeatureExtensionCompose64.program)^[0]) (⟨some (BitMachineRawSequence.leftLabel FeaturePairRaw64.start),
    (FeaturePairRaw64.control,
      (((),none),(V2ItemFrameCore.control V2FeatureFrameLayout64.slots,((),none)))),S⟩ :
      TM2.Cfg (fun _ : Fin 64 => Bool) _ _)
  have hcleanup := FeatureClearHigh64.time_after_run_le
    FeatureExtensionCompose64.program I (firstClock S j y c body) t1 hfirstBound
    (fun i => hhigh _ (by simp [I,FeatureClearHigh64.high]))
  change FeatureClearHigh64.time (((advance FeatureExtensionCompose64.program)^[t1]) I).stk ≤ _ at hcleanup
  rw [show ((advance FeatureExtensionCompose64.program)^[t1]) I = _ from hfirst] at hcleanup
  change FeatureClearHigh64.time U ≤ _ at hcleanup
  obtain ⟨t,ht,hseq⟩ := BitMachineRawSequence.runs
    FeatureExtensionCompose64.program FeatureClearHigh64.program
    (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)
    (MinimumRatioContext.MachineInvokeClear.clearLabel 48 0)
    (FeaturePairRaw64.control,
      (((),none),(V2ItemFrameCore.control V2FeatureFrameLayout64.slots,((),none))))
    (FeaturePairRaw64.control,
      (((),none),(V2ItemFrameCore.control V2FeatureFrameLayout64.slots,v)))
    ((),none) ((),none) S U (FeatureClearHigh64.cleaned U)
    t1 (FeatureClearHigh64.time U) hfirst (FeatureClearHigh64.run U)
  refine ⟨t,by unfold clock; omega,?_,?_,?_,?_,?_,?_⟩
  · exact congrArg TM2.Cfg.l hseq
  · have hh := congrArg (fun z => z.stk (9 : Fin 64)) hseq
    simpa only [cleanedProgram,FeatureClearHigh64.cleaned_low U 9 (by decide)] using hh.trans hout
  · have hh := congrArg (fun z => z.stk (12 : Fin 64)) hseq
    simpa only [cleanedProgram,FeatureClearHigh64.cleaned_low U 12 (by decide)] using hh.trans h12
  · have hh := congrArg (fun z => z.stk (15 : Fin 64)) hseq
    simpa only [cleanedProgram,FeatureClearHigh64.cleaned_low U 15 (by decide)] using hh.trans h15
  · intro k hk
    have hh := congrArg (fun z => z.stk k) hseq
    simpa only [cleanedProgram,FeatureClearHigh64.cleaned_high U k hk] using hh
  · intro k hk hk5 hk7 hk9 hk11 hk14
    have hh := congrArg (fun z => z.stk k) hseq
    have hh' :
        (((advance cleanedProgram)^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel FeaturePairRaw64.start)),
            ((FeaturePairRaw64.control,
              (((),none),
                (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,
                  ((),none)))),((),none)),S⟩ :
              TM2.Cfg (fun _ : Fin 64 => Bool) _ _)).stk k =
          FeatureClearHigh64.cleaned U k := by
      simpa only [cleanedProgram] using hh
    rw [FeatureClearHigh64.cleaned_low U k hk] at hh'
    exact hh'.trans (hlow k hk hk5 hk7 hk9 hk11 hk14)

#print axioms run
end CurrentAdditive.FeatureBoundedExtension64
