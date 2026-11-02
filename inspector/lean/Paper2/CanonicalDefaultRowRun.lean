import Paper2.CanonicalDefaultWord

/-! Scratch successor of `CanonicalDefaultWord` (checked 2026-09-25, unchanged).
Whole-bank run of the fixed `RowMachine.program`: all ten phases, in the
program's actual order, from `RowMachine.initial` to its halt, with every
transition charged. No production module imports this file. -/

namespace Paper2.CanonicalDefaultWordScratch.RowMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem run_add (a b : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (a + b) c = run b (run a c) := by
  rw [Nat.add_comm]
  simp only [run, Function.iterate_add_apply]

theorem repeatWord_add (a b : Nat) (word : List Bool) :
    repeatWord (a + b) word = repeatWord a word ++ repeatWord b word := by
  induction a with
  | zero => simp [repeatWord]
  | succ a ih =>
      rw [Nat.succ_add, repeatWord_succ, repeatWord_succ, ih, List.append_assoc]

/-- The literal ten-stack bank. -/
def B (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : List Bool) : Stack → List Bool :=
  ![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]

/-- The inner word `[F,T,T,F] ++ column^(q₁+s+1)` that the program builds. -/
def innerWord (q₁ s : Nat) (column : List Bool) : List Bool :=
  [false,true,true,false] ++ repeatWord (q₁+s+1) column

def finalBank (q₁ s Q : Nat) (column payload : List Bool) : Stack → List Bool :=
  B (List.replicate q₁ true) (List.replicate s true) (List.replicate Q true)
    column [] [] (innerWord q₁ s column)
    (repeatWord Q (innerWord q₁ s column)) [] payload

/-- Exact sum of the ten charged phase bounds (copy, repeat, copy, repeat,
mark, repeat, header, copy, repeat, halt). -/
def rowBound (q₁ s Q L : Nat) : Nat :=
  (2*q₁+2) + (q₁*(2*L+3)+1) + (2*s+2) + (s*(2*L+3)+1) + 1 +
    (1*(2*L+3)+1) + 1 + (2*Q+2) + (Q*(2*(4+(q₁+s+1)*L)+3)+1) + 1

theorem innerWord_length (q₁ s : Nat) (column : List Bool) :
    (innerWord q₁ s column).length = 4 + (q₁+s+1)*column.length := by
  simp only [innerWord, List.length_append, repeatWord_length]
  simp only [List.length_cons, List.length_nil]

theorem bank1_eq (q₁ s Q : Nat) (column payload : List Bool) :
    bank1 q₁ s Q column payload =
      B (List.replicate q₁ true) (List.replicate s true) (List.replicate Q true)
        column (List.replicate q₁ true) [] [] [] [] payload := by
  funext i
  fin_cases i <;> rfl

theorem repeat_q1_run (q₁ s Q : Nat) (column payload : List Bool) :
    ∃ t ≤ q₁*(2*column.length+3)+1,
      run t ⟨some (.repeatQ1 .next),none,bank1 q₁ s Q column payload⟩ =
        ⟨some (.copyS .scan),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column [] [] (repeatWord q₁ column)
            [] [] payload⟩ := by
  rw [bank1_eq]
  obtain ⟨t,ht,hr⟩ := repeat_phase_update innerIndex Label.repeatQ1
    (.copyS .scan) (by intro l; rfl)
    (B (List.replicate q₁ true) (List.replicate s true) (List.replicate Q true)
        column (List.replicate q₁ true) [] [] [] [] payload)
    column [] payload q₁ rfl rfl rfl rfl rfl
  refine ⟨t,ht,?_⟩
  rw [hr]
  congr 1
  funext i
  fin_cases i <;> simp [B, innerIndex, Function.update]

theorem copy_s_run (q₁ s Q : Nat) (column front payload : List Bool) :
    ∃ t ≤ 2*s+2,
      run t ⟨some (.copyS .scan),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column [] [] front [] [] payload⟩ =
        ⟨some (.repeatS .next),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column (List.replicate s true) [] front
            [] [] payload⟩ := by
  obtain ⟨t,ht,hr⟩ := copy_phase_update copySIndex Label.copyS
    (.repeatS .next) (by intro l; rfl)
    (B (List.replicate q₁ true) (List.replicate s true)
      (List.replicate Q true) column [] [] front [] [] payload)
    (List.replicate s true) [] rfl rfl rfl
  refine ⟨t,by simpa using ht,?_⟩
  rw [hr]
  congr 1
  funext i
  fin_cases i <;> simp [B, copySIndex, Function.update]

theorem repeat_s_run (q₁ s Q : Nat) (column front payload : List Bool) :
    ∃ t ≤ s*(2*column.length+3)+1,
      run t ⟨some (.repeatS .next),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column (List.replicate s true) [] front
            [] [] payload⟩ =
        ⟨some .mark,none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column [] []
            (repeatWord s column ++ front) [] [] payload⟩ := by
  obtain ⟨t,ht,hr⟩ := repeat_phase_update innerIndex Label.repeatS
    .mark (by intro l; rfl)
    (B (List.replicate q₁ true) (List.replicate s true)
      (List.replicate Q true) column (List.replicate s true) [] front
      [] [] payload)
    column front payload s rfl rfl rfl rfl rfl
  refine ⟨t,ht,?_⟩
  rw [hr]
  congr 1
  funext i
  fin_cases i <;> simp [B, innerIndex, Function.update]

theorem mark_run (q₁ s Q : Nat) (column front payload : List Bool) :
    run 1 ⟨some .mark,none,
        B (List.replicate q₁ true) (List.replicate s true)
          (List.replicate Q true) column [] [] front [] [] payload⟩ =
      ⟨some (.repeatOne .next),none,
        B (List.replicate q₁ true) (List.replicate s true)
          (List.replicate Q true) column [true] [] front [] [] payload⟩ := by
  simp only [run, Function.iterate_one, advance, TM2.step, program,
    TM2.stepAux, Option.getD_some]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem repeat_one_run (q₁ s Q : Nat) (column front payload : List Bool) :
    ∃ t ≤ 1*(2*column.length+3)+1,
      run t ⟨some (.repeatOne .next),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column [true] [] front [] [] payload⟩ =
        ⟨some .header,none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column [] []
            (repeatWord 1 column ++ front) [] [] payload⟩ := by
  obtain ⟨t,ht,hr⟩ := repeat_phase_update innerIndex Label.repeatOne
    .header (by intro l; rfl)
    (B (List.replicate q₁ true) (List.replicate s true)
      (List.replicate Q true) column [true] [] front [] [] payload)
    column front payload 1 rfl rfl rfl rfl rfl
  refine ⟨t,ht,?_⟩
  rw [hr]
  congr 1
  funext i
  fin_cases i <;> simp [B, innerIndex, Function.update]

theorem header_run (q₁ s Q : Nat) (column front payload : List Bool) :
    run 1 ⟨some .header,none,
        B (List.replicate q₁ true) (List.replicate s true)
          (List.replicate Q true) column [] [] front [] [] payload⟩ =
      ⟨some (.copyQ .scan),none,
        B (List.replicate q₁ true) (List.replicate s true)
          (List.replicate Q true) column [] []
          ([false,true,true,false] ++ front) [] [] payload⟩ := by
  simp only [run, Function.iterate_one, advance, TM2.step, program,
    TM2.stepAux, Option.getD_some]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem copy_q_run (q₁ s Q : Nat) (column inner payload : List Bool) :
    ∃ t ≤ 2*Q+2,
      run t ⟨some (.copyQ .scan),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column [] [] inner [] [] payload⟩ =
        ⟨some (.repeatQ .next),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column (List.replicate Q true) [] inner
            [] [] payload⟩ := by
  obtain ⟨t,ht,hr⟩ := copy_phase_update copyQIndex Label.copyQ
    (.repeatQ .next) (by intro l; rfl)
    (B (List.replicate q₁ true) (List.replicate s true)
      (List.replicate Q true) column [] [] inner [] [] payload)
    (List.replicate Q true) [] rfl rfl rfl
  refine ⟨t,by simpa using ht,?_⟩
  rw [hr]
  congr 1
  funext i
  fin_cases i <;> simp [B, copyQIndex, Function.update]

theorem repeat_q_run (q₁ s Q : Nat) (column inner payload : List Bool) :
    ∃ t ≤ Q*(2*inner.length+3)+1,
      run t ⟨some (.repeatQ .next),none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column (List.replicate Q true) [] inner
            [] [] payload⟩ =
        ⟨some .done,none,
          B (List.replicate q₁ true) (List.replicate s true)
            (List.replicate Q true) column [] [] inner
            (repeatWord Q inner) [] payload⟩ := by
  obtain ⟨t,ht,hr⟩ := repeat_phase_update outerIndex Label.repeatQ
    .done (by intro l; rfl)
    (B (List.replicate q₁ true) (List.replicate s true)
      (List.replicate Q true) column (List.replicate Q true) [] inner
      [] [] payload)
    inner [] payload Q rfl rfl rfl rfl rfl
  refine ⟨t,ht,?_⟩
  rw [hr]
  congr 1
  funext i
  fin_cases i <;> simp [B, outerIndex, Function.update]

theorem done_run (S : Stack → List Bool) :
    run 1 ⟨some .done,none,S⟩ = ⟨none,none,S⟩ := by
  simp only [run, Function.iterate_one, advance, TM2.step, program,
    TM2.stepAux, Option.getD_some]

/-- Whole-bank row round: from the literal initial bank (unary `q₁`,`s`,`Q`,
the column word, an arbitrary retained payload) the fixed program halts with
the next row word `repeatWord Q (innerWord q₁ s column)` in stack 7, all
parameters, the column and the payload retained, and scratch cleared. -/
theorem row_run (q₁ s Q : Nat) (column payload : List Bool) :
    ∃ t ≤ rowBound q₁ s Q column.length,
      run t (initial q₁ s Q column payload) =
        ⟨none,none,finalBank q₁ s Q column payload⟩ := by
  obtain ⟨t1,ht1,h1⟩ := copy_q1_run q₁ s Q column payload
  obtain ⟨t2,ht2,h2⟩ := repeat_q1_run q₁ s Q column payload
  obtain ⟨t3,ht3,h3⟩ := copy_s_run q₁ s Q column (repeatWord q₁ column) payload
  obtain ⟨t4,ht4,h4⟩ := repeat_s_run q₁ s Q column (repeatWord q₁ column) payload
  have h5 := mark_run q₁ s Q column
    (repeatWord s column ++ repeatWord q₁ column) payload
  obtain ⟨t6,ht6,h6⟩ := repeat_one_run q₁ s Q column
    (repeatWord s column ++ repeatWord q₁ column) payload
  have h7 := header_run q₁ s Q column
    (repeatWord 1 column ++ (repeatWord s column ++ repeatWord q₁ column))
    payload
  have hinner : [false,true,true,false] ++
      (repeatWord 1 column ++ (repeatWord s column ++ repeatWord q₁ column)) =
      innerWord q₁ s column := by
    rw [innerWord, ← repeatWord_add, ← repeatWord_add]
    congr 2
    omega
  rw [hinner] at h7
  obtain ⟨t8,ht8,h8⟩ := copy_q_run q₁ s Q column (innerWord q₁ s column) payload
  obtain ⟨t9,ht9,h9⟩ := repeat_q_run q₁ s Q column (innerWord q₁ s column) payload
  have h10 := done_run (finalBank q₁ s Q column payload)
  refine ⟨t1+t2+t3+t4+1+t6+1+t8+t9+1, ?_, ?_⟩
  · have hL := innerWord_length q₁ s column
    rw [hL] at ht9
    unfold rowBound
    omega
  · simp only [run_add]
    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9]
    exact h10

/-- Same-object identity with the canonical recurrence: started on the
level-`k` column word, stack 7 ends with exactly the level-`k+1` row word. -/
theorem row_run_words (p s q₁ q₂ w Q k : Nat) (payload : List Bool) :
    finalBank q₁ s Q (words p s q₁ q₂ w Q k).2 payload 7 =
      (words p s q₁ q₂ w Q (k+1)).1 := by
  rfl

theorem row_run_canonical (p s q₁ q₂ w Q k : Nat) (payload : List Bool) :
    ∃ t ≤ rowBound q₁ s Q (words p s q₁ q₂ w Q k).2.length,
      run t (initial q₁ s Q (words p s q₁ q₂ w Q k).2 payload) =
        ⟨none,none,finalBank q₁ s Q (words p s q₁ q₂ w Q k).2 payload⟩ ∧
      finalBank q₁ s Q (words p s q₁ q₂ w Q k).2 payload 7 =
        (words p s q₁ q₂ w Q (k+1)).1 := by
  obtain ⟨t,ht,h⟩ := row_run q₁ s Q (words p s q₁ q₂ w Q k).2 payload
  exact ⟨t,ht,h,row_run_words p s q₁ q₂ w Q k payload⟩

theorem rowBound_mono {a b c a' b' c' : Nat} (L : Nat)
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    rowBound a b c L ≤ rowBound a' b' c' L := by
  unfold rowBound
  gcongr

/-- Coarse public clock for one row round. -/
theorem rowBound_le (q₁ s Q L : Nat) :
    rowBound q₁ s Q L ≤ 39*(q₁+s+Q+1)^2*(L+1) := by
  have h1 : rowBound q₁ s Q L ≤
      rowBound (q₁+s+Q+1) (q₁+s+Q+1) (q₁+s+Q+1) L :=
    rowBound_mono L (by omega) (by omega) (by omega)
  refine le_trans h1 ?_
  generalize hmdef : q₁+s+Q+1 = m at *
  have hpos : 1 ≤ m := by omega
  have hm : m ≤ m*m := Nat.le_mul_self m
  have hmL : m*L ≤ m*m*L := Nat.mul_le_mul_right L hm
  have h11 : 1 ≤ m*m := Nat.mul_le_mul hpos hpos
  have hL : L ≤ m*m*L := Nat.le_mul_of_pos_left L (by omega)
  unfold rowBound
  nlinarith

theorem row_run_public (q₁ s Q : Nat) (column payload : List Bool) :
    ∃ t ≤ 39*(q₁+s+Q+1)^2*(column.length+1),
      run t (initial q₁ s Q column payload) =
        ⟨none,none,finalBank q₁ s Q column payload⟩ := by
  obtain ⟨t,ht,h⟩ := row_run q₁ s Q column payload
  exact ⟨t,le_trans ht (rowBound_le q₁ s Q column.length),h⟩

#print axioms run_add
#print axioms repeatWord_add
#print axioms rowBound_mono
#print axioms rowBound_le
#print axioms row_run_public
#print axioms repeat_q1_run
#print axioms copy_s_run
#print axioms repeat_s_run
#print axioms mark_run
#print axioms repeat_one_run
#print axioms header_run
#print axioms copy_q_run
#print axioms repeat_q_run
#print axioms done_run
#print axioms row_run
#print axioms row_run_words
#print axioms row_run_canonical

end Paper2.CanonicalDefaultWordScratch.RowMachine
