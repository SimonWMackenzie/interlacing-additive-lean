import CurrentAdditive.FeaturePreparedReady64

/-! One fixed Fin64 program prepares and computes the raw V2 feature
descriptor from the enumerator's retained context. -/

namespace CurrentAdditive.FeaturePairRaw64

open EthInapproximability.CurrentPaper
open CurrentAdditive.FeaturePreparedCallback
open CurrentAdditive.FeatureContext64
open Turing BitMachineEncoding

noncomputable section

abbrev Bank := FeatureContext64.Bank

def callbackControl : FeaturePreparedCallback.Control := (.inl none, none)

def program := BitMachineRawSequence.program
  FeatureInputPrep64.program FeatureContext64.program
  (.pair (.emit 0)) FeatureInputPrep64.control callbackControl

def start : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
      BitMachineCopy.Label)
    FeaturePreparedCallback.Label :=
  BitMachineRawSequence.leftLabel FeatureInputPrep64.start
def control := (FeatureInputPrep64.control, callbackControl)

def copyClock (j y : Nat) (c : List (Nat × Nat)) : Nat :=
  (2*j.bits.length+2) + (2*y.bits.length+2) +
    (2*(CylinderFeatureCodec.encodeFeature c).length+2) + 2

def clock (j y : Nat) (c : List (Nat × Nat)) : Nat :=
  copyClock j y c + FeaturePreparedCallback.preparedClock j y c + 1

theorem clock_poly (j y : Nat) (c : List (Nat × Nat)) :
    clock j y c ≤
      (10*(UnaryBinaryEncoding.coefficient+100)+9)*
        (FeaturePreparedCallback.preparedSize j y c)^2 := by
  let N := FeaturePreparedCallback.preparedSize j y c
  have hN : 1 ≤ N := by dsimp [N, FeaturePreparedCallback.preparedSize]; omega
  have hsq : N ≤ N^2 := by nlinarith
  have hcopy : copyClock j y c ≤ 2*N+6 := by
    dsimp [copyClock,N,FeaturePreparedCallback.preparedSize]
    omega
  have hp := FeaturePreparedCallback.prepared_clock_poly j y c
  change FeaturePreparedCallback.preparedClock j y c ≤
    10*(UnaryBinaryEncoding.coefficient+100)*N^2 at hp
  unfold clock
  nlinarith

theorem physical_raw (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat))
    (hj : S ⟨12,by omega⟩ = j.bits)
    (hy : S ⟨6,by omega⟩ = y.bits)
    (hc : S ⟨15,by omega⟩ = CylinderFeatureCodec.encodeFeature c)
    (hblank : ∀ k : FeaturePreparedCallback.Stack, S (locate k) = [])
    (h38 : S ⟨38,by omega⟩ = []) :
    ∃ t ≤ clock j y c,
      let z := ((advance program)^[t])
        (⟨some start, control, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _)
      z.l = none ∧
      z.stk ⟨36,by omega⟩ =
        CylinderFeatureCodec.encodeFeature ((j,y)::c) ∧
      ∀ k : Bank, (k.val < 16 ∨ 38 ≤ k.val) → z.stk k = S k := by
  have h16 : S ⟨16,by omega⟩ = [] := by
    simpa [FeatureContext64.locate, FeatureContext64.locateMap,
      FeaturePreparedCallback.pairSlots] using
      hblank (FeaturePreparedCallback.pairSlots (.inl 0))
  have h17 : S ⟨17,by omega⟩ = [] := by
    simpa [FeatureContext64.locate, FeatureContext64.locateMap,
      FeaturePreparedCallback.pairSlots] using
      hblank (FeaturePreparedCallback.pairSlots (.inl 1))
  have h21 : S ⟨21,by omega⟩ = [] := by
    simpa [FeatureContext64.locate, FeatureContext64.locateMap,
      FeaturePreparedCallback.countSource,
      FeaturePreparedCallback.countSlots] using
      hblank FeaturePreparedCallback.countSource
  obtain ⟨a, ha, hprep⟩ :=
    FeatureInputPrep64.physical_inputs S j y c
      hj hy hc h16 h17 h21 h38
  let S1 := FeatureInputPrep64.after S j y c
  have hready : FeatureContext64.Ready S1 j y c :=
    FeaturePreparedReady64.copied_ready S j y c hblank
  obtain ⟨b, hb, hhalt, hout⟩ :=
    FeatureContext64.prepared_run S1 j y c hready
  let z2 := FeatureContext64.run b
    (⟨some (.pair (.emit 0)), callbackControl, S1⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _)
  have hr2 : FeatureContext64.run b
      (⟨some (.pair (.emit 0)), callbackControl, S1⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, z2.var, z2.stk⟩ := by
    have hz : z2.l = none := by
      simpa only [z2, callbackControl] using hhalt
    change z2 = ⟨none, z2.var, z2.stk⟩
    cases h : z2 with
    | mk l v T =>
        cases l with
        | none => simp
        | some l => simp [h] at hz
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    FeatureInputPrep64.program FeatureContext64.program
    FeatureInputPrep64.start (.pair (.emit 0))
    FeatureInputPrep64.control FeatureInputPrep64.control
    callbackControl z2.var S S1 z2.stk a b
    (by simpa only [S1, FeatureInputPrep64.control,
      FeatureInputPrep64.start] using hprep)
    hr2
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · unfold clock copyClock
    omega
  · simpa only [program,start,control] using congrArg
      TM2.Cfg.l hrun
  · have he := congrArg (fun w => w.stk (⟨36,by omega⟩ : Bank)) hrun
    have h36 : locate FeaturePreparedCallback.joinOutput =
        (⟨36,by omega⟩ : Bank) := rfl
    simpa only [h36] using he.trans hout
  · intro k hk
    have hknot : ¬ ∃ x : FeaturePreparedCallback.Stack, locate x = k := by
      rintro ⟨x,hx⟩
      have hrange := FeatureContext64.locate_range x
      have hval := congrArg Fin.val hx
      omega
    have hforeign : z2.stk k = S1 k := by
      rw [show z2 = FeatureContext64.frame S1
        (FeaturePreparedCallback.run b
          (FeaturePreparedCallback.initialCfg j y c)) from by
            rw [← FeatureContext64.run_frame]
            exact congrArg
              (FeatureContext64.run b)
              (by
                have hbank := BitMachineStackEmbedding.bank_eq_self
                  FeatureContext64.locate S1
                  (FeaturePreparedCallback.initialBank j y c)
                  (fun x => (hready x).symm)
                simp [FeatureContext64.frame,
                  BitMachineStackEmbedding.stackCfg,
                  FeaturePreparedCallback.initialCfg,
                  callbackControl, hbank])]
      exact BitMachineStackEmbedding.bank_outside
        FeatureContext64.locate S1 _ k hknot
    have hS1 : S1 k = S k := by
      unfold S1 FeatureInputPrep64.after
      have hn16 : k ≠ (⟨16,by omega⟩ : Bank) := by
        intro h
        have hv : k.val = 16 := by simpa using congrArg Fin.val h
        omega
      have hn17 : k ≠ (⟨17,by omega⟩ : Bank) := by
        intro h
        have hv : k.val = 17 := by simpa using congrArg Fin.val h
        omega
      have hn21 : k ≠ (⟨21,by omega⟩ : Bank) := by
        intro h
        have hv : k.val = 21 := by simpa using congrArg Fin.val h
        omega
      simp only [Function.update_of_ne hn21,
        Function.update_of_ne hn17, Function.update_of_ne hn16]
    have he := congrArg (fun w => w.stk k) hrun
    simpa only [program,start,control] using he.trans (hforeign.trans hS1)

#print axioms physical_raw
#print axioms clock_poly

end
end CurrentAdditive.FeaturePairRaw64
