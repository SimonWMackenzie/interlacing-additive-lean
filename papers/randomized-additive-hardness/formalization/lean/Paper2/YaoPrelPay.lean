import Paper2.YaoPrelArith
import Paper2.YaoIdxDecode
import Paper2.YaoPosFull
import Paper2.ClearAll
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Unit 5 segment Y6, part 3 (lane a-yao-owner-2): the payload-count stage
of the Yao prelude.

Consumer: the prelude (Y6); the output `pay = payloadCount t b lambda` is the
divisor of the index decoder Y4.  One fixed program per `t` (and `lambda`),
placed by `ι : Fin 17 ↪ J`.  Cells: 0 unary `b` (preserved), 1 unary
`pow = 2^b` (preserved), 2 output `pay`; 3..16 scratch (all empty at entry and
exit).  Arithmetic, all by admitted unary programs with charged handoffs:

* part A: `A+1 = (2 + 2^(2b+6t-4)) / 3` (copy, copy-append, fixed push,
  admitted power, fixed push, fixed write, admitted division, `ClearAll`);
  `A = aliceNodes (b+3t-3)` by the admitted `aliceNodes_closed`;
* part B: `x = pow*(K+1)*(A+1) + lambda` (fixed write, copy, two admitted
  multiplications, fixed push);
* part C: `pay = (2^(b+(t-4)) + x - 1) / 2^(b+(t-4))` (copy, fixed push,
  admitted power, copy-append, one-mark drop, admitted division, `ClearAll`),
  which is the admitted `payloadCount` (`payloadCount_eq`). -/

noncomputable section

namespace Paper2.YaoPrelude

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoLowerBound

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem clearFrom_zero {K : Type*} [DecidableEq K] {N : ℕ} (cs : Fin N → K)
    (T : K → List Bool) (k : K) :
    Paper2.ClearAll.clearFrom cs 0 T k = if ∃ j, cs j = k then [] else T k := by
  classical
  simp only [Paper2.ClearAll.clearFrom, Nat.zero_le, true_and]

def p3 (p q r : Fin 17) (h : Function.Injective ![p, q, r]) : Fin 3 ↪ Fin 17 := ⟨![p, q, r], h⟩

/-! ## Part A: `A + 1` -/

def cpB3 : Fin 3 ↪ Fin 17 := p3 0 3 14 (by decide)
def powA : MatrixUnaryPower.Stack ↪ Fin 17 := ⟨Sum.elim ![4, 15, 16] (fun _ => 3), by decide⟩
def divA : Fin 6 ↪ Fin 17 := ⟨![4, 5, 14, 7, 6, 15], by decide⟩

variable {J : Type*} [DecidableEq J]

def clrA (ι : Fin 17 ↪ J) : Fin 2 → J := ![ι 3, ι 5]

omit [DecidableEq J] in
theorem clrA_injective (ι : Fin 17 ↪ J) : Function.Injective (clrA ι) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [clrA, ι.injective.eq_iff]

def aA8 (ι : Fin 17 ↪ J) := Paper2.ClearAll.prog (clrA ι)
def aA78 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoIndexDecoder.divProgram (divA.trans ι)) (aA8 ι)
    (⟨0, by omega⟩ : Fin 3) false none
def aA678 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (SourceClauseFixedUnary.program (ι 5) 3) (aA78 ι)
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) () (false, none)
def aA5678 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (SourceClauseFixedUnary.program (ι 4) 2) (aA678 ι)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 3)) () ((), (false, none))
def aA45678 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (powProgram (powA.trans ι)) (aA5678 ι)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 2))
    ((false, false), none) ((), ((), (false, none)))
def aA345678 (t : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (SourceClauseFixedUnary.program (ι 3) (6 * t - 4)) (aA45678 ι)
    (BitMachineRawSequence.leftLabel (.inr false : MatrixUnaryPower.Label)) ()
    (((false, false), none), ((), ((), (false, none))))
def aA2345678 (t : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpB3.trans ι))
    (aA345678 t ι) (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (6 * t - 4)))
    none ((), (((false, false), none), ((), ((), (false, none)))))
/-- Part A program. -/
def partA (t : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpB3.trans ι))
    (aA2345678 t ι) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none (none, ((), (((false, false), none), ((), ((), (false, none))))))

def partAControl : Option Bool × (Option Bool × (Unit × (MatrixUnaryPower.Control × (Unit ×
    (Unit × (Bool × Option Bool)))))) :=
  (none, (none, ((), (((false, false), none), ((), ((), (false, none)))))))

def partAClock (t b : ℕ) : ℕ :=
  (2 * b + 2) + (2 * b + 2) + (6 * t - 4 + 1) +
    (4 * 2 ^ (6 * t - 4 + (b + b)) + 5 * (6 * t - 4 + (b + b)) + 7) + 3 + 4 +
    (8 * (2 + 2 ^ (6 * t - 4 + (b + b))) + 3 * 3 + 4) + (2 * (6 * t + 2 * b + 3 + 1) + 1) + 7

theorem part_A (t : ℕ) (ht : 1 ≤ t) (ι : Fin 17 ↪ J) (S : J → List Bool) (b : ℕ)
    (h0 : S (ι 0) = List.replicate b true)
    (h3 : S (ι 3) = []) (h4 : S (ι 4) = []) (h5 : S (ι 5) = []) (h6 : S (ι 6) = [])
    (h7 : S (ι 7) = []) (h14 : S (ι 14) = []) (h15 : S (ι 15) = []) (h16 : S (ι 16) = []) :
    ∃ total ≤ partAClock t b, ∃ c',
      ((advance (partA t ι))^[total])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), partAControl, S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update S (ι 6)
          (List.replicate (Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1) true)⟩ := by
  classical
  have hinj := ι.injective
  -- A1: copy b into cell 3
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run (cpB3.trans ι) S
    (List.replicate b true) (by simp [cpB3, p3, h0]) (by simp [cpB3, p3, h3])
    (by simp [cpB3, p3, h14])
  set S1 := Function.update S (ι 3) (List.replicate b true) with hS1
  -- A2: copy-append b into cell 3
  obtain ⟨t2, ht2, hr2⟩ := copy_append_run (cpB3.trans ι) S1
    (List.replicate b true) (List.replicate b true)
    (by simp [hS1, cpB3, p3, hinj.eq_iff, h0]) (by simp [hS1, cpB3, p3])
    (by simp [hS1, cpB3, p3, hinj.eq_iff, h14])
  set S2 := Function.update S (ι 3) (List.replicate (b + b) true) with hS2
  have hr2' : ((advance (ExactParameterBranchInstall.copyProgram (cpB3.trans ι)))^[t2])
      (⟨some .scan, none, S1⟩ : TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, S2⟩ := by
    rw [hr2, hS2, hS1]
    simp [cpB3, p3, List.replicate_append_replicate]
  -- A3: push 6t-4 onto cell 3
  set a := 6 * t - 4 + (b + b) with ha
  have hr3 := push_const_run (ι 3) S2 (6 * t - 4) (List.replicate (b + b) true)
    (by simp [hS2])
  set S3 := Function.update S (ι 3) (List.replicate a true) with hS3
  have hr3' : ((advance (SourceClauseFixedUnary.program (ι 3) (6 * t - 4)))^[6 * t - 4 + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label (6 * t - 4)), (), S2⟩ :
        TM2.Cfg (fun _ : J => Bool) (SourceClauseFixedUnary.Label (6 * t - 4)) Unit) =
      ⟨none, (), S3⟩ := by
    rw [hr3, hS3, hS2, ha]
    simp [List.replicate_append_replicate]
  -- A4: power 2^a into cell 4
  obtain ⟨t4, ht4, hr4⟩ := pow_run (powA.trans ι) S3 a
    (by simp [hS3, powA]) (by simp [hS3, powA, hinj.eq_iff, h4])
    (by simp [hS3, powA, hinj.eq_iff, h15]) (by simp [hS3, powA, hinj.eq_iff, h16])
  set S4 := Function.update S3 (ι 4) (List.replicate (2 ^ a) true) with hS4
  have hr4' := hr4
  -- A5: push 2 onto cell 4
  have hr5 := push_const_run (ι 4) S4 2 (List.replicate (2 ^ a) true) (by simp [hS4])
  set S5 := Function.update S3 (ι 4) (List.replicate (2 + 2 ^ a) true) with hS5
  have hr5' : ((advance (SourceClauseFixedUnary.program (ι 4) 2))^[2 + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label 2), (), S4⟩ :
        TM2.Cfg (fun _ : J => Bool) (SourceClauseFixedUnary.Label 2) Unit) =
      ⟨none, (), S5⟩ := by
    rw [hr5, hS5, hS4, Function.update_idem, List.replicate_append_replicate]
  -- A6: write 3 into cell 5
  have hr6 := push_const_run (ι 5) S5 3 [] (by simp [hS5, hS3, hinj.eq_iff, h5])
  set S6 := Function.update S5 (ι 5) (List.replicate 3 true) with hS6
  have hr6' : ((advance (SourceClauseFixedUnary.program (ι 5) 3))^[3 + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label 3), (), S5⟩ :
        TM2.Cfg (fun _ : J => Bool) (SourceClauseFixedUnary.Label 3) Unit) =
      ⟨none, (), S6⟩ := by
    rw [hr6, hS6, List.append_nil]
  -- A7: divide cell 4 by cell 5
  obtain ⟨t7, ht7, hr7⟩ := Paper2.YaoIndexDecoder.div_run (divA.trans ι) S6 (2 + 2 ^ a) 3
    (by simp [hS6, hS5, divA, hinj.eq_iff]) (by simp [hS6, divA])
    (by simp [hS6, hS5, hS3, divA, hinj.eq_iff, h14])
    (by simp [hS6, hS5, hS3, divA, hinj.eq_iff, h7])
    (by simp [hS6, hS5, hS3, divA, hinj.eq_iff, h6])
    (by simp [hS6, hS5, hS3, divA, hinj.eq_iff, h15])
  have hq : (2 + 2 ^ a) / 3 = Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1 := by
    rw [ha, exponent_eq t b ht, alice_div_three]
  have hm : (2 + 2 ^ a) % 3 = 0 := by
    rw [ha, exponent_eq t b ht, alice_mod_three]
  set S7 := Function.update (Function.update S6 (ι 4) []) (ι 6)
    (List.replicate (Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1) true) with hS7
  change _ = (⟨none, false, Function.update (Function.update (Function.update S6 (ι 4) [])
      (ι 7) (List.replicate ((2 + 2 ^ a) % 3) true)) (ι 6)
      (List.replicate ((2 + 2 ^ a) / 3) true)⟩ :
      TM2.Cfg (fun _ : J => Bool) MatrixUnaryDivision.Label Bool) at hr7
  have e7 : Function.update (Function.update S6 (ι 4) []) (ι 7) [] =
      Function.update S6 (ι 4) [] := by
    apply Function.update_eq_self_iff.mpr
    simp [hS6, hS5, hS3, hinj.eq_iff, h7]
  rw [hm, hq, List.replicate_zero, e7, ← hS7] at hr7
  have hr7' := hr7
  -- A8: clear cells 3 and 5
  have hL : ∀ j, (S7 (clrA ι j)).length ≤ 6 * t + 2 * b + 3 := by
    intro j
    fin_cases j
    · simp [clrA, hS7, hS6, hS5, hS3, hinj.eq_iff, ha]; omega
    · simp [clrA, hS7, hS6, hS5, hS3, hinj.eq_iff, ha]
  obtain ⟨t8, ht8, v8, hr8⟩ := Paper2.ClearAll.all_run (clrA ι) (clrA_injective ι)
    (6 * t + 2 * b + 3) S7 hL none
  have hfin : Paper2.ClearAll.clearFrom (clrA ι) 0 S7 = Function.update S (ι 6)
      (List.replicate (Paper2.Yao.aliceNodes (b + 3 * t - 3) + 1) true) := by
    funext j
    rw [clearFrom_zero]
    by_cases hj3 : j = ι 3
    · subst hj3
      rw [if_pos ⟨0, rfl⟩]
      simp [hinj.eq_iff, h3]
    · by_cases hj5 : j = ι 5
      · subst hj5
        rw [if_pos ⟨1, rfl⟩]
        simp [hinj.eq_iff, h5]
      · rw [if_neg (by
          rintro ⟨i, hi⟩
          fin_cases i
          · exact hj3 hi.symm
          · exact hj5 hi.symm)]
        simp only [hS7, hS6, hS5, hS3, Function.update_apply]
        split_ifs <;> simp_all
  rw [hfin] at hr8
  -- sequencing
  obtain ⟨u7, hu7, hrun7⟩ := BitMachineRawSequence.runs
    (Paper2.YaoIndexDecoder.divProgram (divA.trans ι)) (aA8 ι)
    MatrixUnaryDivision.Label.start (⟨0, by omega⟩ : Fin 3)
    false false none v8 S6 S7 _ t7 t8 hr7' hr8
  obtain ⟨u6, hu6, hrun6⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (ι 5) 3) (aA78 ι)
    (0 : SourceClauseFixedUnary.Label 3)
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start)
    () () (false, none) (false, v8) S5 S6 _ (3 + 1) u7 hr6' hrun7
  obtain ⟨u5, hu5, hrun5⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (ι 4) 2) (aA678 ι)
    (0 : SourceClauseFixedUnary.Label 2)
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 3))
    () () ((), (false, none)) ((), (false, v8)) S4 S5 _ (2 + 1) u6 hr5' hrun6
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs
    (powProgram (powA.trans ι)) (aA5678 ι)
    (.inr false) (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label 2))
    ((false, false), none) ((false, false), none) ((), ((), (false, none)))
    ((), ((), (false, v8))) S3 S4 _ t4 u5 hr4' hrun5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (ι 3) (6 * t - 4)) (aA45678 ι)
    (0 : SourceClauseFixedUnary.Label (6 * t - 4))
    (BitMachineRawSequence.leftLabel (.inr false : MatrixUnaryPower.Label))
    () () (((false, false), none), ((), ((), (false, none))))
    (((false, false), none), ((), ((), (false, v8)))) S2 S3 _ (6 * t - 4 + 1) u4 hr3' hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpB3.trans ι)) (aA345678 t ι)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (6 * t - 4)))
    none none ((), (((false, false), none), ((), ((), (false, none)))))
    ((), (((false, false), none), ((), ((), (false, v8))))) S1 S2 _ t2 u3 hr2' hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpB3.trans ι)) (aA2345678 t ι)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    none none (none, ((), (((false, false), none), ((), ((), (false, none))))))
    (none, ((), (((false, false), none), ((), ((), (false, v8)))))) S S1 _ t1 u2
    (by simpa [hS1, cpB3, p3] using hr1) hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_replicate] at ht1 ht2
  rw [ha] at ht4 ht7
  unfold partAClock
  omega

#print axioms part_A

/-! ## Part B: `x = pow*(K+1)*(A+1) + lambda` -/

def cpPow : Fin 3 ↪ Fin 17 := p3 1 10 14 (by decide)
def mulB1 : Fin 4 ↪ Fin 17 := ⟨![8, 10, 9, 14], by decide⟩
def mulB2 : Fin 4 ↪ Fin 17 := ⟨![6, 9, 10, 14], by decide⟩

def bB45 (lambda : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoPositionFull.mulProgram (mulB2.trans ι))
    (SourceClauseFixedUnary.program (ι 10) lambda) (0 : SourceClauseFixedUnary.Label lambda)
    false ()
def bB345 (lambda : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoPositionFull.mulProgram (mulB1.trans ι))
    (bB45 lambda ι) (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)
    false (false, ())
def bB2345 (lambda : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpPow.trans ι))
    (bB345 lambda ι) (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)
    none (false, (false, ()))
/-- Part B program. -/
def partB (t lambda : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (SourceClauseFixedUnary.program (ι 8) (2 ^ t * 2 ^ t + 1))
    (bB2345 lambda ι) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    () (none, (false, (false, ())))

def partBControl : Unit × (Option Bool × (Bool × (Bool × Unit))) :=
  ((), (none, (false, (false, ()))))

def partBClock (t lambda pow A : ℕ) : ℕ :=
  (2 ^ t * 2 ^ t + 1 + 1) + (2 * pow + 2) +
    (pow * (2 * (2 ^ t * 2 ^ t + 1) + 3) + 1 + (2 ^ t * 2 ^ t + 1 + 1)) +
    (pow * (2 ^ t * 2 ^ t + 1) * (2 * A + 3) + 1 + (A + 1)) + (lambda + 1) + 4

theorem part_B (t lambda : ℕ) (ι : Fin 17 ↪ J) (S : J → List Bool) (pow A : ℕ)
    (h1 : S (ι 1) = List.replicate pow true) (h6 : S (ι 6) = List.replicate A true)
    (h8 : S (ι 8) = []) (h9 : S (ι 9) = []) (h10 : S (ι 10) = []) (h14 : S (ι 14) = []) :
    ∃ total ≤ partBClock t lambda pow A, ∃ c',
      ((advance (partB t lambda ι))^[total])
        (⟨some (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label
            (2 ^ t * 2 ^ t + 1))), partBControl, S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update (Function.update S (ι 6) []) (ι 10)
          (List.replicate (lambda + pow * (2 ^ t * 2 ^ t + 1) * A) true)⟩ := by
  classical
  have hinj := ι.injective
  -- B1: write K+1 into cell 8
  have hr1 := push_const_run (ι 8) S (2 ^ t * 2 ^ t + 1) [] h8
  rw [List.append_nil] at hr1
  set S1 := Function.update S (ι 8) (List.replicate (2 ^ t * 2 ^ t + 1) true) with hS1
  -- B2: copy pow into cell 10
  obtain ⟨t2, ht2, hr2⟩ := ExactParameterBranchInstall.copy_run (cpPow.trans ι) S1
    (List.replicate pow true) (by simp [hS1, cpPow, p3, hinj.eq_iff, h1])
    (by simp [hS1, cpPow, p3, hinj.eq_iff, h10]) (by simp [hS1, cpPow, p3, hinj.eq_iff, h14])
  change _ = (⟨none, none, Function.update S1 (ι 10) (List.replicate pow true)⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr2
  set S2 := Function.update S1 (ι 10) (List.replicate pow true) with hS2
  -- B3: multiply
  obtain ⟨t3, ht3, hr3⟩ := Paper2.YaoPositionFull.mul_run (mulB1.trans ι) S2 pow
    (2 ^ t * 2 ^ t + 1) (by simp [hS2, hS1, mulB1, hinj.eq_iff])
    (by simp [hS2, mulB1]) (by simp [hS2, hS1, mulB1, hinj.eq_iff, h9])
    (by simp [hS2, hS1, mulB1, hinj.eq_iff, h14])
  change _ = (⟨none, false, Function.update (Function.update (Function.update S2 (ι 8) [])
      (ι 10) []) (ι 9) (List.replicate (pow * (2 ^ t * 2 ^ t + 1)) true)⟩ :
    TM2.Cfg (fun _ : J => Bool) MatrixUnaryArithmetic.Label Bool) at hr3
  set S3 := Function.update (Function.update (Function.update S2 (ι 8) [])
      (ι 10) []) (ι 9) (List.replicate (pow * (2 ^ t * 2 ^ t + 1)) true) with hS3
  -- B4: multiply by A
  obtain ⟨t4, ht4, hr4⟩ := Paper2.YaoPositionFull.mul_run (mulB2.trans ι) S3
    (pow * (2 ^ t * 2 ^ t + 1)) A (by simp [hS3, hS2, hS1, mulB2, hinj.eq_iff, h6])
    (by simp [hS3, mulB2]) (by simp [hS3, mulB2, hinj.eq_iff])
    (by simp [hS3, hS2, hS1, mulB2, hinj.eq_iff, h14])
  change _ = (⟨none, false, Function.update (Function.update (Function.update S3 (ι 6) [])
      (ι 9) []) (ι 10) (List.replicate (pow * (2 ^ t * 2 ^ t + 1) * A) true)⟩ :
    TM2.Cfg (fun _ : J => Bool) MatrixUnaryArithmetic.Label Bool) at hr4
  set S4 := Function.update (Function.update (Function.update S3 (ι 6) [])
      (ι 9) []) (ι 10) (List.replicate (pow * (2 ^ t * 2 ^ t + 1) * A) true) with hS4
  -- B5: push lambda
  have hr5 := push_const_run (ι 10) S4 lambda
    (List.replicate (pow * (2 ^ t * 2 ^ t + 1) * A) true) (by simp [hS4])
  have hfin : Function.update S4 (ι 10) (List.replicate lambda true ++
      List.replicate (pow * (2 ^ t * 2 ^ t + 1) * A) true) =
      Function.update (Function.update S (ι 6) []) (ι 10)
        (List.replicate (lambda + pow * (2 ^ t * 2 ^ t + 1) * A) true) := by
    rw [List.replicate_append_replicate]
    funext j
    simp only [hS4, hS3, hS2, hS1, Function.update_apply]
    split_ifs <;> simp_all [hinj.eq_iff]
  rw [hfin] at hr5
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs
    (Paper2.YaoPositionFull.mulProgram (mulB2.trans ι))
    (SourceClauseFixedUnary.program (ι 10) lambda)
    MatrixUnaryArithmetic.Label.outer (0 : SourceClauseFixedUnary.Label lambda)
    false false () () S3 S4 _ t4 (lambda + 1) hr4 hr5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs
    (Paper2.YaoPositionFull.mulProgram (mulB1.trans ι)) (bB45 lambda ι)
    MatrixUnaryArithmetic.Label.outer
    (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)
    false false (false, ()) (false, ()) S2 S3 _ t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpPow.trans ι)) (bB345 lambda ι)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel MatrixUnaryArithmetic.Label.outer)
    none none (false, (false, ())) (false, (false, ())) S1 S2 _ t2 u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (ι 8) (2 ^ t * 2 ^ t + 1)) (bB2345 lambda ι)
    (0 : SourceClauseFixedUnary.Label (2 ^ t * 2 ^ t + 1))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    () () (none, (false, (false, ()))) (none, (false, (false, ()))) S S1 _
    (2 ^ t * 2 ^ t + 1 + 1) u2 hr1 hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_replicate] at ht2
  unfold partBClock
  omega

#print axioms part_B

/-! ## Part C: `pay = (δ + x - 1) / δ`, `δ = 2^(t-4+b)` -/

def cpB11 : Fin 3 ↪ Fin 17 := p3 0 11 14 (by decide)
def powC : MatrixUnaryPower.Stack ↪ Fin 17 := ⟨Sum.elim ![12, 15, 16] (fun _ => 11), by decide⟩
def cpD : Fin 3 ↪ Fin 17 := p3 12 10 14 (by decide)
def divC : Fin 6 ↪ Fin 17 := ⟨![10, 12, 14, 13, 2, 15], by decide⟩

def clrC (ι : Fin 17 ↪ J) : Fin 3 → J := ![ι 11, ι 12, ι 13]

omit [DecidableEq J] in
theorem clrC_injective (ι : Fin 17 ↪ J) : Function.Injective (clrC ι) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [clrC, ι.injective.eq_iff]

def cC67 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (Paper2.YaoIndexDecoder.divProgram (divC.trans ι))
    (Paper2.ClearAll.prog (clrC ι)) (⟨0, by omega⟩ : Fin 4) false none
def cC567 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (dropProgram (ι 10)) (cC67 ι)
    (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start) () (false, none)
def cC4567 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpD.trans ι))
    (cC567 ι) (BitMachineRawSequence.leftLabel ()) none ((), (false, none))
def cC34567 (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (powProgram (powC.trans ι)) (cC4567 ι)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ((false, false), none)
    (none, ((), (false, none)))
def cC234567 (t : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (SourceClauseFixedUnary.program (ι 11) (t - 4)) (cC34567 ι)
    (BitMachineRawSequence.leftLabel (.inr false : MatrixUnaryPower.Label)) ()
    (((false, false), none), (none, ((), (false, none))))
/-- Part C program. -/
def partC (t : ℕ) (ι : Fin 17 ↪ J) :=
  BitMachineRawSequence.program (ExactParameterBranchInstall.copyProgram (cpB11.trans ι))
    (cC234567 t ι) (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (t - 4)))
    none ((), (((false, false), none), (none, ((), (false, none)))))

def partCControl : Option Bool × (Unit × (MatrixUnaryPower.Control × (Option Bool ×
    (Unit × (Bool × Option Bool))))) :=
  (none, ((), (((false, false), none), (none, ((), (false, none))))))

def partCClock (t b x : ℕ) : ℕ :=
  (2 * b + 2) + (t - 4 + 1) + (4 * 2 ^ (t - 4 + b) + 5 * (t - 4 + b) + 7) +
    (2 * 2 ^ (t - 4 + b) + 2) + 1 +
    (8 * (2 ^ (t - 4 + b) + x - 1) + 3 * 2 ^ (t - 4 + b) + 4) +
    (3 * (t + b + 2 ^ (t - 4 + b) + 1) + 1) + 6

theorem part_C (t : ℕ) (ι : Fin 17 ↪ J) (S : J → List Bool) (b x : ℕ)
    (h0 : S (ι 0) = List.replicate b true) (h10 : S (ι 10) = List.replicate x true)
    (h2 : S (ι 2) = []) (h11 : S (ι 11) = []) (h12 : S (ι 12) = []) (h13 : S (ι 13) = [])
    (h14 : S (ι 14) = []) (h15 : S (ι 15) = []) (h16 : S (ι 16) = []) :
    ∃ total ≤ partCClock t b x, ∃ c',
      ((advance (partC t ι))^[total])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), partCControl, S⟩ :
          TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update (Function.update S (ι 10) []) (ι 2)
          (List.replicate ((2 ^ (t - 4 + b) + x - 1) / 2 ^ (t - 4 + b)) true)⟩ := by
  classical
  have hinj := ι.injective
  set d := 2 ^ (t - 4 + b) with hd
  have hdpos : 0 < d := by rw [hd]; positivity
  -- C1: copy b into cell 11
  obtain ⟨t1, ht1, hr1⟩ := ExactParameterBranchInstall.copy_run (cpB11.trans ι) S
    (List.replicate b true) (by simp [cpB11, p3, h0]) (by simp [cpB11, p3, h11])
    (by simp [cpB11, p3, h14])
  change _ = (⟨none, none, Function.update S (ι 11) (List.replicate b true)⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr1
  set S1 := Function.update S (ι 11) (List.replicate b true) with hS1
  -- C2: push t-4
  have hr2 := push_const_run (ι 11) S1 (t - 4) (List.replicate b true) (by simp [hS1])
  rw [List.replicate_append_replicate, hS1, Function.update_idem] at hr2
  set S2 := Function.update S (ι 11) (List.replicate (t - 4 + b) true) with hS2
  -- C3: power
  obtain ⟨t3, ht3, hr3⟩ := pow_run (powC.trans ι) S2 (t - 4 + b)
    (by simp [hS2, powC]) (by simp [hS2, powC, hinj.eq_iff, h12])
    (by simp [hS2, powC, hinj.eq_iff, h15]) (by simp [hS2, powC, hinj.eq_iff, h16])
  change _ = (⟨none, ((false, false), none), Function.update S2 (ι 12) (List.replicate d true)⟩ :
    TM2.Cfg (fun _ : J => Bool) MatrixUnaryPower.Label MatrixUnaryPower.Control) at hr3
  set S3 := Function.update S2 (ι 12) (List.replicate d true) with hS3
  -- C4: append δ to cell 10
  obtain ⟨t4, ht4, hr4⟩ := copy_append_run (cpD.trans ι) S3 (List.replicate d true)
    (List.replicate x true) (by simp [hS3, cpD, p3])
    (by simp [hS3, hS2, cpD, p3, hinj.eq_iff, h10])
    (by simp [hS3, hS2, cpD, p3, hinj.eq_iff, h14])
  change _ = (⟨none, none, Function.update S3 (ι 10)
      (List.replicate d true ++ List.replicate x true)⟩ :
    TM2.Cfg (fun _ : J => Bool) BitMachineCopy.Label (Option Bool)) at hr4
  rw [List.replicate_append_replicate] at hr4
  set S4 := Function.update S3 (ι 10) (List.replicate (d + x) true) with hS4
  -- C5: drop one mark
  have hr5 := drop_run (ι 10) S4 (List.replicate (d + x) true) (by simp [hS4])
  rw [List.tail_replicate, hS4, Function.update_idem] at hr5
  set S5 := Function.update S3 (ι 10) (List.replicate (d + x - 1) true) with hS5
  -- C6: divide by δ
  obtain ⟨t6, ht6, hr6⟩ := Paper2.YaoIndexDecoder.div_run (divC.trans ι) S5 (d + x - 1) d
    (by simp [hS5, divC]) (by simp [hS5, hS3, divC, hinj.eq_iff])
    (by simp [hS5, hS3, hS2, divC, hinj.eq_iff, h14])
    (by simp [hS5, hS3, hS2, divC, hinj.eq_iff, h13])
    (by simp [hS5, hS3, hS2, divC, hinj.eq_iff, h2])
    (by simp [hS5, hS3, hS2, divC, hinj.eq_iff, h15])
  change _ = (⟨none, false, Function.update (Function.update (Function.update S5 (ι 10) [])
      (ι 13) (List.replicate ((d + x - 1) % d) true)) (ι 2)
      (List.replicate ((d + x - 1) / d) true)⟩ :
      TM2.Cfg (fun _ : J => Bool) MatrixUnaryDivision.Label Bool) at hr6
  set S6 := Function.update (Function.update (Function.update S5 (ι 10) [])
      (ι 13) (List.replicate ((d + x - 1) % d) true)) (ι 2)
      (List.replicate ((d + x - 1) / d) true) with hS6
  -- C7: clear cells 11, 12, 13
  have hL : ∀ j, (S6 (clrC ι j)).length ≤ t + b + d := by
    intro j
    have hmod := Nat.mod_lt (d + x - 1) hdpos
    fin_cases j
    · simp [clrC, hS6, hS5, hS3, hS2, hinj.eq_iff]; omega
    · simp [clrC, hS6, hS5, hS3, hinj.eq_iff]
    · simp [clrC, hS6, hinj.eq_iff]; omega
  obtain ⟨t7, ht7, v7, hr7⟩ := Paper2.ClearAll.all_run (clrC ι) (clrC_injective ι)
    (t + b + d) S6 hL none
  have hfin : Paper2.ClearAll.clearFrom (clrC ι) 0 S6 = Function.update
      (Function.update S (ι 10) []) (ι 2) (List.replicate ((d + x - 1) / d) true) := by
    funext j
    rw [clearFrom_zero]
    by_cases hj : ∃ i, clrC ι i = j
    · rw [if_pos hj]
      obtain ⟨i, rfl⟩ := hj
      fin_cases i <;> simp [clrC, hinj.eq_iff, h11, h12, h13]
    · rw [if_neg hj]
      have h11' : j ≠ ι 11 := fun h => hj ⟨0, h.symm⟩
      have h12' : j ≠ ι 12 := fun h => hj ⟨1, h.symm⟩
      have h13' : j ≠ ι 13 := fun h => hj ⟨2, h.symm⟩
      simp only [hS6, hS5, hS3, hS2, Function.update_apply, h11', h12', h13', if_false]
      split_ifs <;> rfl
  rw [hfin] at hr7
  -- sequencing
  obtain ⟨u6, hu6, hrun6⟩ := BitMachineRawSequence.runs
    (Paper2.YaoIndexDecoder.divProgram (divC.trans ι)) (Paper2.ClearAll.prog (clrC ι))
    MatrixUnaryDivision.Label.start (⟨0, by omega⟩ : Fin 4)
    false false none v7 S5 S6 _ t6 t7 hr6 hr7
  obtain ⟨u5, hu5, hrun5⟩ := BitMachineRawSequence.runs (dropProgram (ι 10)) (cC67 ι)
    () (BitMachineRawSequence.leftLabel MatrixUnaryDivision.Label.start)
    () () (false, none) (false, v7) S4 S5 _ 1 u6 hr5 hrun6
  obtain ⟨u4, hu4, hrun4⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpD.trans ι)) (cC567 ι)
    BitMachineCopy.Label.scan (BitMachineRawSequence.leftLabel ())
    none none ((), (false, none)) ((), (false, v7)) S3 S4 _ t4 u5 hr4 hrun5
  obtain ⟨u3, hu3, hrun3⟩ := BitMachineRawSequence.runs (powProgram (powC.trans ι)) (cC4567 ι)
    (.inr false) (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((false, false), none) ((false, false), none) (none, ((), (false, none)))
    (none, ((), (false, v7))) S2 S3 _ t3 u4 hr3 hrun4
  obtain ⟨u2, hu2, hrun2⟩ := BitMachineRawSequence.runs
    (SourceClauseFixedUnary.program (ι 11) (t - 4)) (cC34567 ι)
    (0 : SourceClauseFixedUnary.Label (t - 4))
    (BitMachineRawSequence.leftLabel (.inr false : MatrixUnaryPower.Label))
    () () (((false, false), none), (none, ((), (false, none))))
    (((false, false), none), (none, ((), (false, v7)))) S1 S2 _ (t - 4 + 1) u3 hr2 hrun3
  obtain ⟨u1, hu1, hrun1⟩ := BitMachineRawSequence.runs
    (ExactParameterBranchInstall.copyProgram (cpB11.trans ι)) (cC234567 t ι)
    BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (t - 4)))
    none none ((), (((false, false), none), (none, ((), (false, none)))))
    ((), (((false, false), none), (none, ((), (false, v7))))) S S1 _ t1 u2 hr1 hrun2
  refine ⟨u1, ?_, _, hrun1⟩
  simp only [List.length_replicate] at ht1 ht4
  unfold partCClock
  rw [← hd]
  omega

#print axioms part_C

end Paper2.YaoPrelude

end
