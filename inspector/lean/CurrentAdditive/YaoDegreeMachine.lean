import CurrentAdditive.YaoDegreeSetupScan
import CurrentAdditive.YaoDegreeArithmetic

/-! One fixed Fin16 TM2 program for each fixed t≥4. From unary b,H=2^b
and a retained K, with all work cells blank, it physically searches the cut,
subtracts the suffix, constructs its power of two, and writes the exact
locked `publicFieldDegree b t` on bank 3. -/

namespace CurrentAdditive.SmallBias.YaoDegreeMachine

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding

def powerCtrl : MatrixUnaryCut.Control × MatrixUnaryPower.Control :=
  ((false, true), ((false, false), none))

def printCtrl : Option Bool × (Option Bool × Unit) :=
  (none, (none, ()))

def afterCtrl := (powerCtrl, printCtrl)

def afterProgram (t : ℕ) :=
  BitMachineRawSequence.program YaoSuffixPower.program
    (YaoDegreePrinter.program t)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    powerCtrl printCtrl

def program (t : ℕ) :=
  BitMachineRawSequence.program (YaoDegreeSetupScan.program t)
    (afterProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixUnaryCut.Label.scan))
    (YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl)
    afterCtrl

def baseBank (S : Fin 16 → List Bool) (b t : ℕ) :=
  Function.update
    (Function.update S 6 (List.replicate (2 ^ (t + b - 3)) true))
    5 (List.replicate (sourcePairDepth b t) true)

def scanBank (S : Fin 16 → List Bool) (b t : ℕ) :=
  YaoCutScanLoop.scanState (baseBank S b t) (sourcePairDepth b t)
    (fun j => decide (sourceCutFeasible b t j)) (sourcePairDepth b t)

def powerBank (S : Fin 16 → List Bool) (b t : ℕ) :=
  Function.update
    (Function.update (scanBank S b t) 4
      (List.replicate (sourceSuffixDepth b t) true))
    5 (List.replicate (2 ^ sourceSuffixDepth b t) true)

def finalBank (S : Fin 16 → List Bool) (b t : ℕ) :=
  Function.update (powerBank S b t) 3
    (List.replicate (publicFieldDegree b t) true)

def timeBound (b t : ℕ) : ℕ :=
  let i := sourceCutIndex b t
  let h := sourceSuffixDepth b t
  let Q := 2 ^ h
  YaoDegreeSetupScan.totalBound b t +
    ((3 * i + 4) + (4 * Q + 5 * h + 7) + 1) +
    ((2 * Q + 2) + (2 * b + 2) + (YaoDegreePrinter.fixedPart t + 1) + 2) + 2

theorem degree_value (b t : ℕ) :
    2 ^ sourceSuffixDepth b t + b + sourceCutIndex b t +
      YaoDegreePrinter.fixedPart t = publicFieldDegree b t := by
  rw [YaoDegreeArithmetic.public_degree_closed]
  unfold publicBiasExponent YaoDegreePrinter.fixedPart
  omega

theorem run (S : Fin 16 → List Bool) (b t : ℕ) (ht : 4 ≤ t)
    (hb : S 0 = List.replicate b true)
    (hH : S 1 = List.replicate (2 ^ b) true)
    (hblank : YaoDegreeSetupScan.preBlank S) :
    ∃ u ≤ timeBound b t,
      ((advance (program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))),
          ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
            afterCtrl), S⟩ : TM2.Cfg (fun _ : Fin 16 => Bool) _ _) =
      ⟨none, ((YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl),
        afterCtrl), finalBank S b t⟩ := by
  let a := sourcePairDepth b t
  let i := sourceCutIndex b t
  let h := sourceSuffixDepth b t
  let Q := 2 ^ h
  let S3 := scanBank S b t
  let S4 := powerBank S b t
  obtain ⟨u1, hu1, hr1⟩ := YaoDegreeSetupScan.run S b t ht hb hH hblank
  have h4S3 : S3 4 = List.replicate a true := by
    simp [S3, scanBank, YaoCutScanLoop.scanState_4, a]
  have h3S3 : S3 3 = List.replicate i true := by
    simpa [S3, scanBank, i] using
      YaoCutPhysical.output_cut (baseBank S b t) b t ht
  have h5S3 : S3 5 = [] := by
    simp [S3, scanBank, YaoCutScanLoop.scanState_5]
  have h7S3 : S3 7 = [] := by
    rw [show S3 7 = baseBank S b t 7 from
      YaoCutScanLoop.scanState_other _ _ _ _ 7 (by decide)
        (by decide) (by decide)]
    simpa [baseBank] using hblank 7 (by decide)
  have h8S3 : S3 8 = [] := by
    rw [show S3 8 = baseBank S b t 8 from
      YaoCutScanLoop.scanState_other _ _ _ _ 8 (by decide)
        (by decide) (by decide)]
    simpa [baseBank] using hblank 8 (by decide)
  have hi : i ≤ a := Nat.le_of_lt (sourceCutIndex_spec b t ht).2.1
  have hh : a - i = h := rfl
  obtain ⟨u2, hu2, hr2⟩ := YaoSuffixPower.run S3 a i hi
    h4S3 h3S3 h5S3 h7S3 h8S3
  rw [hh] at hr2
  rw [hh] at hu2
  have h0S4 : S4 0 = List.replicate b true := by
    have hbase : baseBank S b t 0 = S 0 := by simp [baseBank]
    rw [show S4 0 = baseBank S b t 0 by
      simp [S4, powerBank, scanBank,
        YaoCutScanLoop.scanState_other _ _ _ _ 0 (by decide)
          (by decide) (by decide)]]
    exact hbase.trans hb
  have h3S4 : S4 3 = List.replicate i true := by
    calc
      S4 3 = S3 3 := by simp [S4, powerBank, S3]
      _ = List.replicate i true := h3S3
  have h5S4 : S4 5 = List.replicate Q true := by
    simp [S4, powerBank, Q, h]
  have h7S4 : S4 7 = [] := by
    calc
      S4 7 = S3 7 := by simp [S4, powerBank, S3]
      _ = [] := h7S3
  obtain ⟨u3, hu3, hr3⟩ := YaoDegreePrinter.run S4 b i Q t
    h0S4 h3S4 h5S4 h7S4
  have hfinal : Function.update S4 3
      (List.replicate (Q + b + i + YaoDegreePrinter.fixedPart t) true) =
      finalBank S b t := by
    rw [show Q + b + i + YaoDegreePrinter.fixedPart t =
      publicFieldDegree b t from degree_value b t]
    rfl
  rw [hfinal] at hr3
  obtain ⟨u23, hu23, hr23⟩ := BitMachineRawSequence.runs
    YaoSuffixPower.program (YaoDegreePrinter.program t)
    (BitMachineRawSequence.leftLabel MatrixUnaryCut.Label.scan)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    powerCtrl powerCtrl printCtrl printCtrl S3 S4 _ u2 u3 hr2 hr3
  obtain ⟨u, hu, hr⟩ := BitMachineRawSequence.runs
    (YaoDegreeSetupScan.program t) (afterProgram t)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel MatrixUnaryCut.Label.scan))
    (YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl)
    (YaoDegreeSetupScan.setupCtrl, YaoDegreeSetupScan.scanCtrl)
    afterCtrl afterCtrl S S3 _ u1 u23 hr1 hr23
  have htime : u ≤ timeBound b t := by
    change u ≤ YaoDegreeSetupScan.totalBound b t +
      ((3 * i + 4) + (4 * Q + 5 * h + 7) + 1) +
      ((2 * Q + 2) + (2 * b + 2) + (YaoDegreePrinter.fixedPart t + 1) + 2) + 2
    omega
  exact ⟨u, htime,
    by simpa [program, afterProgram, S3, S4, powerBank, h, Q,
      sourceSuffixDepth] using hr⟩

#print axioms run

end CurrentAdditive.SmallBias.YaoDegreeMachine
