import CurrentAdditive.QuarticQPhysical

/-! A fixed unary machine for the quartic width.  From unary `e` it writes
unary `2^(4e)`, using the checked multiplication and unary-power machines.
The later graph front will feed it `e = clog₂(clog₂ n+1)`. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront.WidthMachine

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open BitMachineRawSequence (leftLabel)

abbrev Stack := Fin 10

def multSlots : Fin 6 ↪ Stack := ⟨![0, 1, 2, 3, 4, 5], by decide⟩

def powerSlots : MatrixUnaryPower.Stack ↪ Stack := ⟨
  fun x => match x with
    | .inl i => ![9, 6, 7] i
    | .inr _ => 5,
  by
    intro x y h
    rcases x with i | x <;> rcases y with j | y
    · fin_cases i <;> fin_cases j <;> simp_all
    · fin_cases i <;> simp_all
    · fin_cases j <;> simp_all
    · cases x; cases y; rfl⟩

def initial (e : ℕ) : Stack → List Bool :=
  Function.update (fun _ => []) 0 (List.replicate e true)

def pushN (k : ℕ) (q : TM2.Stmt (fun _ : Stack => Bool) Unit Bool) :
    TM2.Stmt (fun _ : Stack => Bool) Unit Bool :=
  match k with
  | 0 => q
  | k + 1 => TM2.Stmt.push 1 (fun _ => true) (pushN k q)

def pushFour : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Bool :=
  fun _ => pushN 4 TM2.Stmt.halt

theorem pushN_step (k : ℕ) (q : TM2.Stmt (fun _ : Stack => Bool) Unit Bool)
    (v : Bool) (S : Stack → List Bool) :
    TM2.stepAux (pushN k q) v S =
      TM2.stepAux q v (Function.update S 1 (List.replicate k true ++ S 1)) := by
  induction k generalizing S with
  | zero => simp [pushN]
  | succ k ih =>
      show TM2.stepAux (pushN k q) v (Function.update S 1 (true :: S 1)) = _
      rw [ih, Function.update_self, Function.update_idem]
      congr 2
      rw [List.replicate_succ', List.append_assoc]
      rfl

theorem pushFour_run (S : Stack → List Bool) (v : Bool) :
    ((advance pushFour)^[1])
      (⟨some (), v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Bool) =
      ⟨none, v, Function.update S 1 (List.replicate 4 true ++ S 1)⟩ := by
  show Option.getD (some (TM2.stepAux (pushN 4 TM2.Stmt.halt) v S))
    (⟨some (), v, S⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Bool) = _
  rw [pushN_step]
  rfl

def multiply := MatrixStage4ScalarPreparationOps.multiplyProgram multSlots
def power := MatrixStage4ScalarPreparationOps.unaryPowerProgram powerSlots
def first := BitMachineRawSequence.program pushFour multiply .outer false false
def firstControl := (false, false)
def program := BitMachineRawSequence.program first power (.inr false) firstControl
  ((false, false), none)
def initialControl := (firstControl, (((false, false), none) : MatrixUnaryPower.Control))
def startLabel := Paper2.FullFront.labelOfP program (leftLabel (leftLabel ()))

def clock (e : ℕ) : ℕ :=
  1 + MatrixAddressMachine.exactTime e 4 0 +
    (4 * 2 ^ (4 * e) + 5 * (4 * e) + 7) + 2

theorem run (e : ℕ) :
    ∃ T ≤ clock e,
      ((advance program)^[T])
        (⟨some startLabel, initialControl, initial e⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, initialControl,
          Function.update (Function.update (Function.update (initial e) 1
            (List.replicate 4 true)) 5 (List.replicate (4 * e) true))
            9 (List.replicate (2 ^ (4 * e)) true)⟩ := by
  let S1 := Function.update (initial e) 1 (List.replicate 4 true)
  have h1 : ((advance pushFour)^[1])
      (⟨some (), false, initial e⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Bool) =
      ⟨none, false, S1⟩ := by
    simpa [S1, initial] using pushFour_run (initial e) false
  have h2 := MatrixStage4ScalarPreparationOps.multiply_run multSlots S1 e 4
    (by simp [S1, initial, multSlots])
    (by simp [S1, initial, multSlots])
    (by simp [S1, initial, multSlots])
    (by simp [S1, initial, multSlots])
    (by simp [S1, initial, multSlots])
  let S2 := Function.update S1 5 (List.replicate (e * 4) true)
  have h2' : ((advance multiply)^[MatrixAddressMachine.exactTime e 4 0])
      (⟨some .outer, false, S1⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, false, S2⟩ := by simpa [multiply, S2, S1, multSlots, initial] using h2
  have h3 := MatrixStage4ScalarPreparationOps.unary_power_run powerSlots S2 (4 * e)
    (by simp [S2, S1, initial, powerSlots, Nat.mul_comm])
    (by simp [S2, S1, initial, powerSlots])
    (by simp [S2, S1, initial, powerSlots])
    (by simp [S2, S1, initial, powerSlots])
  obtain ⟨t3, ht3, h3⟩ := h3
  have h3' : ((advance power)^[t3])
      (⟨some (.inr false), ((false, false), none), S2⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, ((false, false), none),
        Function.update S2 9 (List.replicate (2 ^ (4 * e)) true)⟩ := by
    simpa [power, powerSlots] using h3
  obtain ⟨t12, ht12, h12⟩ := BitMachineRawSequence.runs pushFour multiply () .outer
    false false false false (initial e) S1 S2 1 (MatrixAddressMachine.exactTime e 4 0) h1 h2'
  obtain ⟨T, hT, hT_run⟩ := BitMachineRawSequence.runs first power
    (leftLabel ()) (.inr false) firstControl firstControl ((false, false), none)
    ((false, false), none) (initial e) S2
    (Function.update S2 9 (List.replicate (2 ^ (4 * e)) true)) t12 t3 h12 h3'
  refine ⟨T, ?_, ?_⟩
  · dsimp [clock]
    omega
  · simpa only [program, startLabel, initialControl, S2, S1, Nat.mul_comm] using hT_run

end Paper2.CurrentAdditive.QuarticNumericFront.WidthMachine

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.WidthMachine.run
