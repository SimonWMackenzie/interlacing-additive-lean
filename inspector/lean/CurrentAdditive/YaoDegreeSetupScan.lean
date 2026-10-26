import CurrentAdditive.YaoDegreePrinter

/-! One physical setup-and-scan machine from the renderer's degree inputs. -/

namespace CurrentAdditive.SmallBias.YaoDegreeSetupScan

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding
open YaoCutScanBody

def preBlank (S : Fin 16 → List Bool) : Prop :=
  ∀ z : Fin 16, 3 ≤ z.val → S z = []

def setup (t : ℕ) :=
  BitMachineRawSequence.program (YaoThreshold.program t)
    (YaoDepthFuel.program t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none, none) (none, ())

def setupCtrl : (Option Bool × Option Bool) × (Option Bool × Unit) :=
  ((none, none), (none, ()))

def scanCtrl := ((none : Option Bool), bodyControl YaoCutTester.v1)

def program (t : ℕ) :=
  BitMachineRawSequence.program (setup t) (YaoCutPhysical.program t)
    (Sum.inl () : FuelLoop.Label _) setupCtrl scanCtrl

def setupBound (b t : ℕ) :=
  ((2 * 2 ^ b + 2) + YaoThreshold.affineTime t (2 ^ b) + 1) +
  ((2 * b + 2) + (YaoDepthFuel.fixedExtra t + 1) + 1) + 1

def totalBound (b t : ℕ) := setupBound b t + YaoCutPhysical.bound b t + 1

theorem run (S : Fin 16 → List Bool) (b t : ℕ) (ht : 4 ≤ t)
    (hb : S 0 = List.replicate b true)
    (hH : S 1 = List.replicate (2 ^ b) true)
    (hblank : preBlank S) :
    ∃ u ≤ totalBound b t,
      ((advance (program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (setupCtrl, scanCtrl), S⟩ :
          TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, (setupCtrl, scanCtrl),
        YaoCutScanLoop.scanState
          (Function.update
            (Function.update S 6
              (List.replicate (2 ^ (t + b - 3)) true))
            5 (List.replicate (sourcePairDepth b t) true))
          (sourcePairDepth b t)
          (fun j => decide (sourceCutFeasible b t j))
          (sourcePairDepth b t)⟩ := by
  let R := 2 ^ (t + b - 3)
  let a := sourcePairDepth b t
  let S1 := Function.update S (6 : Fin 16) (List.replicate R true)
  let S2 := Function.update S1 (5 : Fin 16) (List.replicate a true)
  have hinit (z : Fin 16) (hz : 3 ≤ z.val) : S z = [] := hblank z hz
  obtain ⟨u1, hu1, hr1⟩ := YaoThreshold.run S b t (by omega) hH
    (hinit 6 (by decide)) (hinit 7 (by decide))
    (hinit 8 (by decide)) (hinit 9 (by decide))
  have hb1 : S1 0 = List.replicate b true := by simp [S1, hb]
  have h51 : S1 5 = [] := by simp [S1, hinit 5 (by decide)]
  have h71 : S1 7 = [] := by simp [S1, hinit 7 (by decide)]
  obtain ⟨u2, hu2, hr2⟩ := YaoDepthFuel.run S1 b t hb1 h51 h71
  have ha : b + YaoDepthFuel.fixedExtra t = a :=
    YaoDepthFuel.fuel_value b t (by omega)
  rw [ha] at hr2
  obtain ⟨u12, hu12, hr12⟩ := BitMachineRawSequence.runs
    (YaoThreshold.program t) (YaoDepthFuel.program t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none, none) (none, none) (none, ()) (none, ())
    S S1 S2 u1 u2 hr1 hr2
  have h5S2 : S2 5 = List.replicate a true := by simp [S2]
  have h4S2 : S2 4 = [] := by simp [S2, S1, hinit 4 (by decide)]
  have h3S2 : S2 3 = [] := by simp [S2, S1, hinit 3 (by decide)]
  have h6S2 : S2 6 = List.replicate R true := by simp [S2, S1]
  have h12S2 : S2 12 = [] := by simp [S2, S1, hinit 12 (by decide)]
  have hsS2 : scratchEmpty S2 := by
    intro z hz hz12
    have hz5 : z ≠ 5 := by intro he; subst z; norm_num at hz
    have hz6 : z ≠ 6 := by intro he; subst z; norm_num at hz
    simpa [S2, S1, Function.update_apply,
      hz5, hz6, hz5.symm, hz6.symm] using hinit z (by omega)
  obtain ⟨u3, hu3, hr3⟩ := YaoCutPhysical.run S2 b t ht
    h5S2 h4S2 h3S2 h6S2 h12S2 hsS2
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (setup t) (YaoCutPhysical.program t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))
    (Sum.inl () : FuelLoop.Label _)
    setupCtrl setupCtrl scanCtrl scanCtrl S S2 _ u12 u3 hr12 hr3
  exact ⟨u, by dsimp [totalBound, setupBound]; omega,
    by simpa [program, setup, S1, S2, R, a, setupCtrl, scanCtrl]
      using hr⟩

#print axioms run

end CurrentAdditive.SmallBias.YaoDegreeSetupScan
