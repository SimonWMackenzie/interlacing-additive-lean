import CurrentAdditive.FeatureBoundedLift96
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Five literal source-preserving copies install the alphabet scan from
the outer caller bank. No semantic packet is installed without a physical copy. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace CurrentAdditive.FeatureInnerPrep96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
abbrev Bank := Fin 96

def slots0 : Fin 3 ↪ Bank := ⟨![30,40,16],by decide⟩
def slots1 : Fin 3 ↪ Bank := ⟨![9,41,16],by decide⟩
def slots2 : Fin 3 ↪ Bank := ⟨![15,44,16],by decide⟩
def slots3 : Fin 3 ↪ Bank := ⟨![31,45,16],by decide⟩
def slots4 : Fin 3 ↪ Bank := ⟨![6,47,16],by decide⟩

def p0 := ExactParameterBranchInstall.copyProgram slots0
def p1 := BitMachineRawSequence.program p0
  (ExactParameterBranchInstall.copyProgram slots1)
  BitMachineCopy.Label.scan (none : Option Bool) (none : Option Bool)
def p2 := BitMachineRawSequence.program p1
  (ExactParameterBranchInstall.copyProgram slots2)
  BitMachineCopy.Label.scan ((none : Option Bool),(none : Option Bool)) (none : Option Bool)
def p3 := BitMachineRawSequence.program p2
  (ExactParameterBranchInstall.copyProgram slots3)
  BitMachineCopy.Label.scan (((none : Option Bool),(none : Option Bool)),(none : Option Bool)) (none : Option Bool)
def p4 := BitMachineRawSequence.program p3
  (ExactParameterBranchInstall.copyProgram slots4)
  BitMachineCopy.Label.scan ((((none : Option Bool),(none : Option Bool)),(none : Option Bool)),(none : Option Bool)) (none : Option Bool)
def program := p4
def start : BitMachineRawSequence.Label (BitMachineRawSequence.Label (BitMachineRawSequence.Label (BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label) BitMachineCopy.Label) BitMachineCopy.Label) BitMachineCopy.Label := (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))
def control := (((((none : Option Bool),(none : Option Bool)),(none : Option Bool)),(none : Option Bool)),(none : Option Bool))

def after (S : Bank → List Bool) (w : Fin 5 → List Bool) : Bank → List Bool :=
  (Function.update (Function.update (Function.update (Function.update (Function.update S 40 (w 0)) 41 (w 1)) 44 (w 2)) 45 (w 3)) 47 (w 4))

theorem run (S : Bank → List Bool) (w : Fin 5 → List Bool)
    (hs : ∀ i : Fin 5, S (![30,9,15,31,6] i) = w i)
    (ht : ∀ i : Fin 5, S (![40,41,44,45,47] i) = [])
    (h16 : S 16 = []) :
    ∃ t ≤ 2*((w 0).length+(w 1).length+(w 2).length+(w 3).length+(w 4).length)+14,
      ((advance program)^[t])
        (⟨some start,control,S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none,control,after S w⟩ := by
  let S1 := Function.update S 40 (w 0)
  obtain ⟨t0,h0,r0⟩ := ExactParameterBranchInstall.copy_run slots0 S (w 0)
    (by simpa [slots0] using hs 0)
    (by simpa [slots0] using ht 0)
    (by simpa [slots0] using h16)
  let S2 := Function.update S1 41 (w 1)
  obtain ⟨t1,h1,r1⟩ := ExactParameterBranchInstall.copy_run slots1 S1 (w 1)
    (by simpa [S1,slots1] using hs 1)
    (by simpa [S1,slots1] using ht 1)
    (by simpa [S1,slots1] using h16)
  let S3 := Function.update S2 44 (w 2)
  obtain ⟨t2,h2,r2⟩ := ExactParameterBranchInstall.copy_run slots2 S2 (w 2)
    (by simpa [S2,S1,slots2] using hs 2)
    (by simpa [S2,S1,slots2] using ht 2)
    (by simpa [S2,S1,slots2] using h16)
  let S4 := Function.update S3 45 (w 3)
  obtain ⟨t3,h3,r3⟩ := ExactParameterBranchInstall.copy_run slots3 S3 (w 3)
    (by simpa [S3,S2,S1,slots3] using hs 3)
    (by simpa [S3,S2,S1,slots3] using ht 3)
    (by simpa [S3,S2,S1,slots3] using h16)
  let S5 := Function.update S4 47 (w 4)
  obtain ⟨t4,h4,r4⟩ := ExactParameterBranchInstall.copy_run slots4 S4 (w 4)
    (by simpa [S4,S3,S2,S1,slots4] using hs 4)
    (by simpa [S4,S3,S2,S1,slots4] using ht 4)
    (by simpa [S4,S3,S2,S1,slots4] using h16)
  obtain ⟨u1,hu1,ru1⟩ := BitMachineRawSequence.runs
    p0 (ExactParameterBranchInstall.copyProgram slots1)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    (none : Option Bool) (none : Option Bool) none none
    S S1 S2 t0 t1
    (by simpa only [p0,S1] using r0)
    (by simpa only [S2] using r1)
  obtain ⟨u2,hu2,ru2⟩ := BitMachineRawSequence.runs
    p1 (ExactParameterBranchInstall.copyProgram slots2)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) BitMachineCopy.Label.scan
    ((none : Option Bool),(none : Option Bool)) ((none : Option Bool),(none : Option Bool)) none none
    S S2 S3 u1 t2
    (by simpa only [p1,S2] using ru1)
    (by simpa only [S3] using r2)
  obtain ⟨u3,hu3,ru3⟩ := BitMachineRawSequence.runs
    p2 (ExactParameterBranchInstall.copyProgram slots3)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)) BitMachineCopy.Label.scan
    (((none : Option Bool),(none : Option Bool)),(none : Option Bool)) (((none : Option Bool),(none : Option Bool)),(none : Option Bool)) none none
    S S3 S4 u2 t3
    (by simpa only [p2,S3] using ru2)
    (by simpa only [S4] using r3)
  obtain ⟨u4,hu4,ru4⟩ := BitMachineRawSequence.runs
    p3 (ExactParameterBranchInstall.copyProgram slots4)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))) BitMachineCopy.Label.scan
    ((((none : Option Bool),(none : Option Bool)),(none : Option Bool)),(none : Option Bool)) ((((none : Option Bool),(none : Option Bool)),(none : Option Bool)),(none : Option Bool)) none none
    S S4 S5 u3 t4
    (by simpa only [p3,S4] using ru3)
    (by simpa only [S5] using r4)
  refine ⟨u4,by omega,?_⟩
  simpa only [program,p4,start,control,after,S5,S4,S3,S2,S1] using ru4

#print axioms run
end CurrentAdditive.FeatureInnerPrep96
