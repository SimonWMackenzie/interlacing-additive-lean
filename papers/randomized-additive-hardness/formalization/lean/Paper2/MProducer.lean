import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Unit 3, segment (2), second part: a physical producer of the sample dimensions
`mY = sourceCols L r q k = 2 (Z + 12)` and `mX = sourceRows L r q k = (Z + 12) ⌈/⌉ L`,
`Z = compressionEntropy (sourceRank …) (sourceCost …) = (R (R+1) + 2) 2^(H-1)`, `R = 2^(b-1)`, `H = b + k`,
from unary `b = sourceBudget L r q k` (the threshold already produced by owner-9's `ThrProducer`), unary `k`
and unary `L`.

Bank `MK = Fin 18`. ONE fixed program `mProg` (nineteen parts, production `BitMachineRawSequence` handoffs):
admitted copies, single-step pushes/pops, admitted `multiplyProgram` (twice), admitted `unaryPowerProgram`
(twice), the admitted `MatrixUnaryDivision.program` (total form, divisor kept). Every cell stated at the exit. -/

set_option maxHeartbeats 32000000
set_option maxRecDepth 16384
set_option linter.unusedSimpArgs false

namespace Paper2.MProducer

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev MK := Fin 18

def u (n : ℕ) : List Bool := List.replicate n true

-- cells: 0 b, 1 k, 2 L, 3 x = b-1, 4 R, 5 H, 6 2^(H-1), 7 R+1, 8 A, 9 Z(+12), 10 mY, 11 dividend,
-- 12 remainder, 13 mX, 14 copy scratch, 15-17 arithmetic scratch

def cpE (a b : MK) (hab : a ≠ b) (ha : a ≠ 14) (hb : b ≠ 14) : Fin 3 ↪ MK :=
  ⟨![a, b, 14], by intro x y h; fin_cases x <;> fin_cases y <;> simp_all [eq_comm]⟩

def powF (o e : MK) : MatrixUnaryPower.Stack → MK
  | .inl 0 => o
  | .inl 1 => 15
  | .inl _ => 16
  | .inr () => e

def powE (o e : MK) (h1 : o ≠ 15) (h2 : o ≠ 16) (h3 : o ≠ e) (h4 : e ≠ 15) (h5 : e ≠ 16) :
    MatrixUnaryPower.Stack ↪ MK := ⟨powF o e, by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · fin_cases a <;> fin_cases b <;> simp_all [powF]
  · cases b; fin_cases a <;> simp_all [powF, eq_comm]
  · cases a; fin_cases b <;> simp_all [powF, eq_comm]
  · cases a; cases b; rfl⟩

def ιM1 : Fin 6 ↪ MK := ⟨![4, 7, 15, 16, 17, 8], by decide⟩
def ιM2 : Fin 6 ↪ MK := ⟨![8, 6, 15, 16, 17, 9], by decide⟩
def ιD : Fin 6 ↪ MK := ⟨![11, 2, 15, 12, 13, 16], by decide⟩

def divProgram (ι : Fin 6 ↪ MK) :
    MatrixUnaryDivision.Label → TM2.Stmt (fun _ : MK => Bool) MatrixUnaryDivision.Label Bool :=
  fun l => stackStmt ι (MatrixUnaryDivision.program l)

theorem div_run (ι : Fin 6 ↪ MK) (S : MK → List Bool) (n m : ℕ)
    (h0 : S (ι 0) = u n) (h1 : S (ι 1) = u m) (h2 : S (ι 2) = []) (h3 : S (ι 3) = [])
    (h4 : S (ι 4) = []) (h5 : S (ι 5) = []) :
    ((advance (divProgram ι))^[MatrixUnaryDivision.totalTime n m])
        (⟨some .start, false, S⟩ : TM2.Cfg (fun _ : MK => Bool) MatrixUnaryDivision.Label Bool) =
      ⟨none, false, Function.update (Function.update (Function.update S (ι 0) []) (ι 3)
        (u (n % m))) (ι 4) (u (n / m))⟩ := by
  let c := MatrixUnaryDivision.cfg (some .start) false (u n) (u m) [] [] [] []
  have hstart : stackCfg ι S c =
      (⟨some .start, false, S⟩ : TM2.Cfg (fun _ : MK => Bool) MatrixUnaryDivision.Label Bool) := by
    dsimp [stackCfg, c, MatrixUnaryDivision.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [h0, h1, h2, h3, h4, h5]
  have hrun := BitMachineStackRun.run ι S MatrixUnaryDivision.program c
    (MatrixUnaryDivision.totalTime n m)
  rw [hstart] at hrun
  change _ = stackCfg ι S (MatrixUnaryDivision.run (MatrixUnaryDivision.totalTime n m) c) at hrun
  rw [show c = MatrixUnaryDivision.cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] [] from rfl, MatrixUnaryDivision.division_total_run n m] at hrun
  refine hrun.trans ?_
  dsimp [stackCfg, MatrixUnaryDivision.cfg]
  congr 1
  have hloc : (![[], List.replicate m true, [], List.replicate (n % m) true,
      List.replicate (n / m) true, []] : Fin 6 → List Bool) =
      Function.update (Function.update (Function.update (fun k : Fin 6 => S (ι k)) 0 []) 3
        (u (n % m))) 4 (u (n / m)) := by
    funext k
    fin_cases k <;> simp [h1, h2, h5, u]
  rw [hloc, bank_update, bank_update, bank_update, bank_restrict]

def cp (a b : MK) (hab : a ≠ b) (ha : a ≠ 14) (hb : b ≠ 14) :=
  MatrixStage4ScalarPreparationOps.copyProgram (cpE a b hab ha hb)
def pw (o e : MK) (h1 : o ≠ 15) (h2 : o ≠ 16) (h3 : o ≠ e) (h4 : e ≠ 15) (h5 : e ≠ 16) :=
  MatrixStage4ScalarPreparationOps.unaryPowerProgram (powE o e h1 h2 h3 h4 h5)

def pushN (a : MK) (k : ℕ) (q : TM2.Stmt (fun _ : MK => Bool) Unit Bool) :
    TM2.Stmt (fun _ : MK => Bool) Unit Bool :=
  match k with
  | 0 => q
  | k + 1 => TM2.Stmt.push a (fun _ => true) (pushN a k q)

def pushP (a : MK) (k : ℕ) : Unit → TM2.Stmt (fun _ : MK => Bool) Unit Bool := fun _ =>
  pushN a k TM2.Stmt.halt

def pop1 (a : MK) : Unit → TM2.Stmt (fun _ : MK => Bool) Unit Bool := fun _ =>
  TM2.Stmt.pop a (fun v _ => v) TM2.Stmt.halt

abbrev powCtl : MatrixUnaryPower.Control := ((false, false), none)
abbrev oc := (none : Option Bool)

def P1 := cp 0 3 (by decide) (by decide) (by decide)
def P2 := pop1 3
def P3 := pw 4 3 (by decide) (by decide) (by decide) (by decide) (by decide)
def P4 := cp 0 5 (by decide) (by decide) (by decide)
def P5 := cp 1 5 (by decide) (by decide) (by decide)
def P6 := pop1 5
def P7 := pw 6 5 (by decide) (by decide) (by decide) (by decide) (by decide)
def P8 := cp 4 7 (by decide) (by decide) (by decide)
def P9 := pushP 7 1
def P10 := MatrixStage4ScalarPreparationOps.multiplyProgram ιM1
def P11 := pushP 8 2
def P12 := MatrixStage4ScalarPreparationOps.multiplyProgram ιM2
def P13 := pushP 9 12
def P14 := cp 9 10 (by decide) (by decide) (by decide)
def P15 := cp 9 10 (by decide) (by decide) (by decide)
def P16 := cp 9 11 (by decide) (by decide) (by decide)
def P17 := cp 2 11 (by decide) (by decide) (by decide)
def P18 := pop1 11
def P19 := divProgram ιD

def s1 := BitMachineRawSequence.program P1 P2 () oc false
def s2 := BitMachineRawSequence.program s1 P3 (.inr false) (oc, false) powCtl
def k2 := ((oc, false), powCtl)
def s3 := BitMachineRawSequence.program s2 P4 BitMachineCopy.Label.scan k2 oc
def k3 := (k2, oc)
def s4 := BitMachineRawSequence.program s3 P5 BitMachineCopy.Label.scan k3 oc
def k4 := (k3, oc)
def s5 := BitMachineRawSequence.program s4 P6 () k4 false
def k5 := (k4, false)
def s6 := BitMachineRawSequence.program s5 P7 (.inr false) k5 powCtl
def k6 := (k5, powCtl)
def s7 := BitMachineRawSequence.program s6 P8 BitMachineCopy.Label.scan k6 oc
def k7 := (k6, oc)
def s8 := BitMachineRawSequence.program s7 P9 () k7 false
def k8 := (k7, false)
def s9 := BitMachineRawSequence.program s8 P10 MatrixAddressMachine.Label.outer k8 false
def k9 := (k8, false)
def s10 := BitMachineRawSequence.program s9 P11 () k9 false
def k10 := (k9, false)
def s11 := BitMachineRawSequence.program s10 P12 MatrixAddressMachine.Label.outer k10 false
def k11 := (k10, false)
def s12 := BitMachineRawSequence.program s11 P13 () k11 false
def k12 := (k11, false)
def s13 := BitMachineRawSequence.program s12 P14 BitMachineCopy.Label.scan k12 oc
def k13 := (k12, oc)
def s14 := BitMachineRawSequence.program s13 P15 BitMachineCopy.Label.scan k13 oc
def k14 := (k13, oc)
def s15 := BitMachineRawSequence.program s14 P16 BitMachineCopy.Label.scan k14 oc
def k15 := (k14, oc)
def s16 := BitMachineRawSequence.program s15 P17 BitMachineCopy.Label.scan k15 oc
def k16 := (k15, oc)
def s17 := BitMachineRawSequence.program s16 P18 () k16 false
def k17 := (k16, false)
/-- The sample-dimension producer: ONE fixed program. -/
def mProg := BitMachineRawSequence.program s17 P19 MatrixUnaryDivision.Label.start k17 false
def mCtl := (k17, false)
def labelOfP {L σ : Type*} {K : Type*} (_P : L → TM2.Stmt (fun _ : K => Bool) L σ)
    (l : L) : L := l
def mStart := labelOfP mProg (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel (leftLabel (leftLabel (leftLabel BitMachineCopy.Label.scan))))))))))))))))))

/-- Start bank: unary `b`, `k`, `L` in cells 0, 1, 2; everything else blank. -/
def M0 (b k L : ℕ) : MK → List Bool :=
  Function.update (Function.update (Function.update (fun _ => []) 0 (u b)) 1 (u k)) 2 (u L)

end

end Paper2.MProducer
