import Paper2.DefaultWordLoop

/-! Runs of the default-word level body and of the full level loop. -/

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.DefaultWordLoop

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)
open Paper2.CanonicalDefaultWordScratch (repeatWord words successor_words)

abbrev innerW (q₁ s : ℕ) (C : List Bool) := CanonicalDefaultWordScratch.RowMachine.innerWord q₁ s C

def bodyBound (q₁ s Q w : ℕ) (R C : List Bool) : ℕ :=
  CanonicalDefaultWordScratch.RowMachine.rowBound q₁ s Q C.length +
  ((2 * R.length + 2) + 4 + (2 * w + 2) +
    (w * (2 * ([true, false, false, false] ++ R).length + 3) + 1) + 1 + 7) +
  (C.length + 1) + ((innerW q₁ s C).length + 1) +
  (R.length + 1) + (([true, false, false, false] ++ R).length + 1) +
  (2 * (repeatWord Q (innerW q₁ s C)).length + 2) + ((repeatWord Q (innerW q₁ s C)).length + 1) +
  (2 * ([false] ++ repeatWord w ([true, false, false, false] ++ R)).length + 2) +
  (([false] ++ repeatWord w ([true, false, false, false] ++ R)).length + 1) + 9

def bodyStart := labelOf body
  (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel (leftLabel
    (leftLabel (CanonicalDefaultWordScratch.RowMachine.Label.copyQ1 BitMachineCopy.Label.scan))))))))))

theorem body_run (q₁ s Q w : ℕ) (R C ctr : List Bool) :
    ∃ t ≤ bodyBound q₁ s Q w R C, ∃ v,
      ((advance body)^[t])
        (⟨some bodyStart, bodyCtl, S q₁ s Q w R C ctr⟩ : TM2.Cfg (fun _ : LB => Bool) _ _) =
        ⟨none, v, S q₁ s Q w (repeatWord Q (innerW q₁ s C))
          ([false] ++ repeatWord w ([true, false, false, false] ++ R)) ctr⟩ := by
  let hw := [true, false, false, false] ++ R
  let nR := repeatWord Q (innerW q₁ s C)
  let nC := [false] ++ repeatWord w hw
  let A0 := CanonicalDefaultWordScratch.RowMachine.B (List.replicate q₁ true)
    (List.replicate s true) (List.replicate Q true) C [] [] [] [] [] []
  let B0 := DefaultColumnRound.B [] [] [] [] [] R (List.replicate w true) []
  let D0 : Fin 2 → List Bool := ![ctr, []]
  let F1 := CanonicalDefaultWordScratch.RowMachine.finalBank q₁ s Q C []
  let B1 := DefaultColumnRound.B hw [] [] nC [] R (List.replicate w true) []
  -- row round
  obtain ⟨t1, ht1, h1⟩ := CanonicalDefaultWordScratch.RowMachine.row_run q₁ s Q C []
  simp only [CanonicalDefaultWordScratch.RowMachine.run,
    CanonicalDefaultWordScratch.RowMachine.initial] at h1
  have l1 := lift iRM CanonicalDefaultWordScratch.RowMachine.program (bk A0 B0 D0) _ _
    (fun _ => rfl) _ _ _ _ h1
  rw [bank_RM] at l1
  -- column round
  obtain ⟨t2, ht2, h2⟩ := DefaultColumnRound.column_round_run R w
  have l2 := lift iCR DefaultColumnRound.program (bk F1 B0 D0) _ _ (fun _ => rfl) _ _ _ _ h2
  rw [bank_CR] at l2
  -- clears and moves
  have p3 := clr_run (.inl 3) C (bk F1 B1 D0) oc rfl
  rw [upd_RM] at p3
  have p4 := clr_run (.inl 6) (innerW q₁ s C) (bk (Function.update F1 3 []) B1 D0) oc rfl
  rw [upd_RM] at p4
  let F2 := Function.update (Function.update F1 3 []) 6 []
  have p5 := clr_run crR R (bk F2 B1 D0) oc rfl
  rw [show crR = .inr (.inl (.inr 0)) from rfl, upd_CR] at p5
  let B2 := Function.update B1 (.inr 0) []
  have p6 := clr_run crJ hw (bk F2 B2 D0) oc rfl
  rw [show crJ = .inr (.inl (.inl 0)) from rfl, upd_CR] at p6
  let B3 := Function.update B2 (.inl 0) []
  have p7 := MatrixStage4ScalarPreparationOps.copy_run rowSlots (bk F2 B3 D0) rfl
  rw [show (bk F2 B3 D0) (rowSlots 0) = nR from rfl,
    show (bk F2 B3 D0) (rowSlots 1) = [] from rfl, List.append_nil,
    show rowSlots 1 = .inr (.inl (.inr 0)) from rfl, upd_CR] at p7
  let B4 := Function.update B3 (.inr 0) nR
  have p8 := clr_run (.inl 7) nR (bk F2 B4 D0) oc rfl
  rw [upd_RM] at p8
  let F3 := Function.update F2 7 []
  have p9 := MatrixStage4ScalarPreparationOps.copy_run colSlots (bk F3 B4 D0) rfl
  rw [show (bk F3 B4 D0) (colSlots 0) = nC from rfl,
    show (bk F3 B4 D0) (colSlots 1) = [] from rfl, List.append_nil,
    show colSlots 1 = .inl 3 from rfl, upd_RM] at p9
  let F4 := Function.update F3 3 nC
  have p10 := clr_run crOut nC (bk F4 B4 D0) oc rfl
  rw [show crOut = .inr (.inl (.inl 3)) from rfl, upd_CR] at p10
  -- sequencing
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs rmP crP _ crStart oc _
    DefaultColumnRound.startCtl _ _ _ _ _ _ l1 l2
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs b1 (clr (.inl 3)) _ () k1 _ oc _
    _ _ _ _ _ q1 p3
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs b2 (clr (.inl 6)) _ () k2 _ oc _
    _ _ _ _ _ q2 p4
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs b3 (clr crR) _ () k3 _ oc _
    _ _ _ _ _ q3 p5
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs b4 (clr crJ) _ () k4 _ oc _
    _ _ _ _ _ q4 p6
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs b5 cpRow _ .scan k5 _ oc _
    _ _ _ _ _ q5 p7
  obtain ⟨u7, hu7, q7⟩ := BitMachineRawSequence.runs b6 (clr (.inl 7)) _ () k6 _ oc _
    _ _ _ _ _ q6 p8
  obtain ⟨u8, hu8, q8⟩ := BitMachineRawSequence.runs b7 cpCol _ .scan k7 _ oc _
    _ _ _ _ _ q7 p9
  obtain ⟨u9, hu9, q9⟩ := BitMachineRawSequence.runs b8 (clr crOut) _ () k8 _ oc _
    _ _ _ _ _ q8 p10
  have hfinal : bk F4 (Function.update B4 (.inl 3) []) D0 =
      S q₁ s Q w nR nC ctr := by
    unfold S bk
    congr 1
    · funext i; fin_cases i <;> rfl
    · congr 1
      funext i
      rcases i with i | i <;> fin_cases i <;> rfl
  rw [hfinal] at q9
  refine ⟨u9, ?_, _, q9⟩
  have ht1' : t1 ≤ CanonicalDefaultWordScratch.RowMachine.rowBound q₁ s Q C.length := ht1
  have ht2' : t2 ≤ (2 * R.length + 2) + 4 + (2 * w + 2) +
      (w * (2 * ([true, false, false, false] ++ R).length + 3) + 1) + 1 + 7 := ht2
  have e1 : hw.length = ([true, false, false, false] ++ R).length := rfl
  have e2 : nR.length = (repeatWord Q (innerW q₁ s C)).length := rfl
  have e3 : nC.length = ([false] ++ repeatWord w ([true, false, false, false] ++ R)).length := rfl
  unfold bodyBound
  omega

#print axioms body_run

end

end Paper2.DefaultWordLoop
