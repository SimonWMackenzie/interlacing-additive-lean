import CurrentAdditive.FeatureContext64
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Three charged source-preserving copies prepare the feature callback's
private inputs from the enumerator's live context. -/

namespace CurrentAdditive.FeatureInputPrep64

open EthInapproximability.CurrentPaper
open CurrentAdditive.FeaturePreparedCallback
open CurrentAdditive.FeatureContext64
open Turing BitMachineEncoding

noncomputable section

def jSlots : Fin 3 ↪ Bank :=
  ⟨![⟨12,by omega⟩,⟨16,by omega⟩,⟨38,by omega⟩], by decide⟩
def ySlots : Fin 3 ↪ Bank :=
  ⟨![⟨6,by omega⟩,⟨17,by omega⟩,⟨38,by omega⟩], by decide⟩
def cSlots : Fin 3 ↪ Bank :=
  ⟨![⟨15,by omega⟩,⟨21,by omega⟩,⟨38,by omega⟩], by decide⟩

def p01 := BitMachineRawSequence.program
  (ExactParameterBranchInstall.copyProgram jSlots)
  (ExactParameterBranchInstall.copyProgram ySlots)
  BitMachineCopy.Label.scan none none

def program := BitMachineRawSequence.program p01
  (ExactParameterBranchInstall.copyProgram cSlots)
  BitMachineCopy.Label.scan (none,none) none

def start : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label)
    BitMachineCopy.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)

def control : ((Option Bool × Option Bool) × Option Bool) :=
  ((none,none),none)

def after (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat)) : Bank → List Bool :=
  Function.update
    (Function.update (Function.update S ⟨16,by omega⟩ j.bits)
      ⟨17,by omega⟩ y.bits)
    ⟨21,by omega⟩ (CylinderFeatureCodec.encodeFeature c)

theorem physical_inputs (S : Bank → List Bool) (j y : Nat)
    (c : List (Nat × Nat))
    (hj : S ⟨12,by omega⟩ = j.bits)
    (hy : S ⟨6,by omega⟩ = y.bits)
    (hc : S ⟨15,by omega⟩ = CylinderFeatureCodec.encodeFeature c)
    (h16 : S ⟨16,by omega⟩ = [])
    (h17 : S ⟨17,by omega⟩ = [])
    (h21 : S ⟨21,by omega⟩ = [])
    (h38 : S ⟨38,by omega⟩ = []) :
    ∃ t ≤ (2*j.bits.length+2) + (2*y.bits.length+2) +
        (2*(CylinderFeatureCodec.encodeFeature c).length+2) + 2,
      ((advance program)^[t])
        (⟨some start, control, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, control, after S j y c⟩ := by
  obtain ⟨a, ha, hrj⟩ :=
    ExactParameterBranchInstall.copy_run jSlots S j.bits hj h16 h38
  let S1 := Function.update S ⟨16,by omega⟩ j.bits
  have hy1 : S1 ⟨6,by omega⟩ = y.bits := by simpa [S1] using hy
  have h171 : S1 ⟨17,by omega⟩ = [] := by simpa [S1] using h17
  have h381 : S1 ⟨38,by omega⟩ = [] := by simpa [S1] using h38
  obtain ⟨b, hb, hry⟩ :=
    ExactParameterBranchInstall.copy_run ySlots S1 y.bits hy1 h171 h381
  let S2 := Function.update S1 ⟨17,by omega⟩ y.bits
  have hc2 : S2 ⟨15,by omega⟩ = CylinderFeatureCodec.encodeFeature c := by
    simpa [S2,S1] using hc
  have h212 : S2 ⟨21,by omega⟩ = [] := by simpa [S2,S1] using h21
  have h382 : S2 ⟨38,by omega⟩ = [] := by simpa [S2,S1] using h38
  obtain ⟨d, hd, hrc⟩ :=
    ExactParameterBranchInstall.copy_run cSlots S2
      (CylinderFeatureCodec.encodeFeature c) hc2 h212 h382
  obtain ⟨ab, hab, hrab⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram jSlots)
    (ExactParameterBranchInstall.copyProgram ySlots)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none S S1 S2 a b
    (by simpa only [S1] using hrj)
    (by simpa only [S1,S2] using hry)
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    p01 (ExactParameterBranchInstall.copyProgram cSlots)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    BitMachineCopy.Label.scan
    (none,none) (none,none) none none S S2
    (after S j y c) ab d
    (by simpa only [p01] using hrab)
    (by simpa only [S2,S1,after] using hrc)
  refine ⟨t, by omega, ?_⟩
  simpa only [program,start,control] using hrun

end
end CurrentAdditive.FeatureInputPrep64
