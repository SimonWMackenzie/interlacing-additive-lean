import EthInapproximability.CurrentPaper.MatrixUnaryDivision
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Unit 3, segment (1): the physical numeric decoding of the public canonical
outer coordinate for `SourceActiveRank.scanAtCanonical` (value targets in
`ScanCoordDecode`: `g = a / r / 3 / m`, `e = a / r / 3 % m`,
`tag = a / r % 3`).

ONE fixed program on a twelve-cell bank: push the constant divisor `3`
(one charged step), then three runs of the production counted-subtraction
divider `MatrixUnaryDivision.program` (reused by name through the production
stack embedding `stackStmt`), sequenced by the production
`BitMachineRawSequence.program` (each handoff charged):

1. `a / r` (copy index `a % r` kept in cell 11),
2. `(a / r) / 3` and `tag = (a / r) % 3`,
3. `g = (a / r / 3) / m` and `e = (a / r / 3) % m`.

Entry: unary `a` (the outer token value, consumed), unary `r`, unary `m`
(public parameters, preserved), and a frame cell 12 (unary `ig`, untouched,
used by `ScanSelect`); every other cell blank. Exit bank exact. -/

namespace Paper2.ScanDecodeMachine

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev K := Fin 14

def u (n : ℕ) : List Bool := List.replicate n true

/-- Entry bank: `a` in 0, `r` in 1, `m` in 2, frame `ig` in 12, 13 blank. -/
def D0 (a r m ig : ℕ) : K → List Bool :=
  ![u a, u r, u m, [], [], [], [], [], [], [], [], [], u ig, []]

/-- Exit bank: `r`, `m` preserved, divisor `3` in 3, `tag` in 5, `g` in 7,
`e` in 8, copy index `a % r` in 11, frame `ig` in 12; cells 0, 4, 6
(consumed dividends), the division scratch 9, 10 and cell 13 blank. -/
def DF (a r m ig : ℕ) : K → List Bool :=
  ![[], u r, u m, u 3, [], u (a / r % 3), [], u (a / r / 3 / m), u (a / r / 3 % m),
    [], [], u (a % r), u ig, []]

def ι1f : Fin 6 → K := ![0, 1, 9, 11, 4, 10]
def ι2f : Fin 6 → K := ![4, 3, 9, 5, 6, 10]
def ι3f : Fin 6 → K := ![6, 2, 9, 8, 7, 10]

def ι1 : Fin 6 ↪ K := ⟨ι1f, by unfold ι1f; decide⟩
def ι2 : Fin 6 ↪ K := ⟨ι2f, by unfold ι2f; decide⟩
def ι3 : Fin 6 ↪ K := ⟨ι3f, by unfold ι3f; decide⟩

def three : Unit → TM2.Stmt (fun _ : K => Bool) Unit Bool :=
  fun _ => push 3 (fun _ => true) (push 3 (fun _ => true) (push 3 (fun _ => true) halt))

def dv (ι : Fin 6 ↪ K) : MatrixUnaryDivision.Label →
    TM2.Stmt (fun _ : K => Bool) MatrixUnaryDivision.Label Bool :=
  fun l => stackStmt ι (MatrixUnaryDivision.program l)

def p1 := BitMachineRawSequence.program three (dv ι1) .start false false
def p2 := BitMachineRawSequence.program p1 (dv ι2) .start (false, false) false
def program := BitMachineRawSequence.program p2 (dv ι3) .start ((false, false), false) false

def startCtl : ((Bool × Bool) × Bool) × Bool := (((false, false), false), false)

def decodeBound (a r m : ℕ) : ℕ :=
  1 + MatrixUnaryDivision.totalTime a r + 1 + MatrixUnaryDivision.totalTime (a / r) 3 + 1 +
    MatrixUnaryDivision.totalTime (a / r / 3) m + 1

theorem decodeBound_le (a r m : ℕ) : decodeBound a r m ≤ 24 * a + 3 * r + 3 * m + 30 := by
  unfold decodeBound
  have h1 := MatrixUnaryDivision.totalTime_bound a r
  have h2 := MatrixUnaryDivision.totalTime_bound (a / r) 3
  have h3 := MatrixUnaryDivision.totalTime_bound (a / r / 3) m
  have ha1 : a / r ≤ a := Nat.div_le_self a r
  have ha2 : a / r / 3 ≤ a / r := Nat.div_le_self _ 3
  omega

/-- One divider run through any injective placement whose six cells hold
dividend, divisor and four blanks. -/
theorem div_phase (ι : Fin 6 ↪ K) (W : K → List Bool) (x y : ℕ)
    (h0 : W (ι 0) = u x) (h1 : W (ι 1) = u y) (h2 : W (ι 2) = []) (h3 : W (ι 3) = [])
    (h4 : W (ι 4) = []) (h5 : W (ι 5) = []) :
    ((advance (dv ι))^[MatrixUnaryDivision.totalTime x y])
        (⟨some .start, false, W⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, Function.update (Function.update (Function.update W (ι 0) []) (ι 3)
        (u (x % y))) (ι 4) (u (x / y))⟩ := by
  have hr := MatrixUnaryDivision.division_total_run x y
  unfold MatrixUnaryDivision.run at hr
  have hs := BitMachineStackRun.run ι W MatrixUnaryDivision.program
    (MatrixUnaryDivision.cfg (some .start) false (List.replicate x true)
      (List.replicate y true) [] [] [] []) (MatrixUnaryDivision.totalTime x y)
  rw [hr] at hs
  have hin : bank ι W ![List.replicate x true, List.replicate y true, [], [], [], []] = W := by
    apply bank_eq_self
    intro k
    fin_cases k
    · exact h0.symm
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
  have hout : (![[], List.replicate y true, [], List.replicate (x % y) true,
      List.replicate (x / y) true, []] : Fin 6 → List Bool) =
      Function.update (Function.update (Function.update
        ![List.replicate x true, List.replicate y true, [], [], [], []] 0 [])
        3 (List.replicate (x % y) true)) 4 (List.replicate (x / y) true) := by
    funext k
    fin_cases k <;> rfl
  simp only [MatrixUnaryDivision.cfg, stackCfg] at hs
  rw [hin, hout, bank_update, bank_update, bank_update, hin] at hs
  exact hs

theorem three_step (S : K → List Bool) (v : Bool) :
    (advance three) (⟨some (), v, S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, v, Function.update (Function.update (Function.update S 3 (true :: S 3)) 3
        (true :: Function.update S 3 (true :: S 3) 3)) 3
        (true :: Function.update (Function.update S 3 (true :: S 3)) 3
          (true :: Function.update S 3 (true :: S 3) 3) 3)⟩ := by
  rfl

def D1 (a r m ig : ℕ) : K → List Bool :=
  ![u a, u r, u m, u 3, [], [], [], [], [], [], [], [], u ig, []]
def D2 (a r m ig : ℕ) : K → List Bool :=
  ![[], u r, u m, u 3, u (a / r), [], [], [], [], [], [], u (a % r), u ig, []]
def D3 (a r m ig : ℕ) : K → List Bool :=
  ![[], u r, u m, u 3, [], u (a / r % 3), u (a / r / 3), [], [], [], [], u (a % r), u ig, []]

theorem run_three (a r m ig : ℕ) :
    (advance three) (⟨some (), false, D0 a r m ig⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, D1 a r m ig⟩ := by
  rw [three_step]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_d1 (a r m ig : ℕ) :
    ((advance (dv ι1))^[MatrixUnaryDivision.totalTime a r])
        (⟨some .start, false, D1 a r m ig⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, D2 a r m ig⟩ := by
  rw [div_phase ι1 (D1 a r m ig) a r rfl rfl rfl rfl rfl rfl]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_d2 (a r m ig : ℕ) :
    ((advance (dv ι2))^[MatrixUnaryDivision.totalTime (a / r) 3])
        (⟨some .start, false, D2 a r m ig⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, D3 a r m ig⟩ := by
  rw [div_phase ι2 (D2 a r m ig) (a / r) 3 rfl rfl rfl rfl rfl rfl]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem run_d3 (a r m ig : ℕ) :
    ((advance (dv ι3))^[MatrixUnaryDivision.totalTime (a / r / 3) m])
        (⟨some .start, false, D3 a r m ig⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
      ⟨none, false, DF a r m ig⟩ := by
  rw [div_phase ι3 (D3 a r m ig) (a / r / 3) m rfl rfl rfl rfl rfl rfl]
  congr 1
  funext j
  fin_cases j <;> rfl

/-- The physical coordinate decoding: exact exit bank, explicit clock. -/
theorem decode_run (a r m ig : ℕ) :
    ∃ t ≤ decodeBound a r m,
      ((advance program)^[t])
        (⟨some (leftLabel (leftLabel (leftLabel ()))), startCtl, D0 a r m ig⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, startCtl, DF a r m ig⟩ := by
  obtain ⟨t1, ht1, h1⟩ := BitMachineRawSequence.runs three (dv ι1) () .start false false
    false false (D0 a r m ig) (D1 a r m ig) (D2 a r m ig) 1 _ (run_three a r m ig) (run_d1 a r m ig)
  obtain ⟨t2, ht2, h2⟩ := BitMachineRawSequence.runs p1 (dv ι2) (leftLabel ()) .start
    (false, false) (false, false) false false (D0 a r m ig) (D2 a r m ig) (D3 a r m ig) t1 _ h1
    (run_d2 a r m ig)
  obtain ⟨t3, ht3, h3⟩ := BitMachineRawSequence.runs p2 (dv ι3) (leftLabel (leftLabel ()))
    .start ((false, false), false) ((false, false), false) false false (D0 a r m ig) (D3 a r m ig)
    (DF a r m ig) t2 _ h2 (run_d3 a r m ig)
  refine ⟨t3, ?_, h3⟩
  unfold decodeBound
  omega

#print axioms div_phase
#print axioms decode_run
#print axioms decodeBound_le

end

end Paper2.ScanDecodeMachine
