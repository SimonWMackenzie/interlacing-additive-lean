import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineInline
import Mathlib.Tactic

/-! Fixed physical unary coefficient controller for the two-state draw bound. -/
namespace Paper2.DrawCoefficients
open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding MatrixStage4ScalarPreparationOps

abbrev Stack := Fin 32
def unary (n : Nat) : List Bool := List.replicate n true
theorem unary_append (a b : Nat) : unary a ++ unary b = unary (a+b) := by
  exact (List.replicate_add a b true).symm
theorem unary_push (a : Nat) : true :: unary a = unary (1+a) := by
  simp [unary, Nat.one_add, List.replicate_succ]
def A (s Q : Nat) := Q * (s + 2)
def B (s q1 Q : Nat) := Q * (s + 1 + s * (q1 + s + 1))
def D (w q2 : Nat) := w * q2
def C (w q2 : Nat) := 1 + 3 * w + D w q2

def initialBank (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  fun j => if j = 0 then unary s else if j = 1 then unary q1 else
    if j = 2 then unary q2 else if j = 3 then unary w else
    if j = 4 then unary Q else if j = 5 then unary p else
    if j = 6 then unary fuel else if j = 7 then unary mX else
    if j = 8 then unary mY else []

def finalBank (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  fun j => if j = 0 then unary s else if j = 1 then unary q1 else
    if j = 2 then unary q2 else if j = 3 then unary w else
    if j = 4 then unary Q else if j = 5 then unary p else
    if j = 6 then unary fuel else if j = 7 then unary mX else
    if j = 8 then unary mY else if j = 9 then unary (A s Q) else
    if j = 10 then unary (B s q1 Q) else
    if j = 11 then unary (C w q2) else
    if j = 12 then unary (D w q2) else []

def copySlots : Fin 9 → (Fin 3 ↪ Stack)
  | 0 => ⟨![0,24,20], by decide⟩
  | 1 => ⟨![1,25,20], by decide⟩
  | 2 => ⟨![0,25,20], by decide⟩
  | 3 => ⟨![0,27,20], by decide⟩
  | 4 => ⟨![26,27,20], by decide⟩
  | 5 => ⟨![12,11,20], by decide⟩
  | 6 => ⟨![3,11,20], by decide⟩
  | 7 => ⟨![3,11,20], by decide⟩
  | 8 => ⟨![3,11,20], by decide⟩

def mulSlots : Fin 4 → (Fin 6 ↪ Stack)
  | 0 => ⟨![4,24,17,18,19,9], by decide⟩
  | 1 => ⟨![0,25,17,18,19,26], by decide⟩
  | 2 => ⟨![4,27,17,18,19,10], by decide⟩
  | 3 => ⟨![3,2,17,18,19,12], by decide⟩

inductive Label where
  | copy (i : Fin 9) (l : BitMachineCopy.Label)
  | mul (i : Fin 4) (l : MatrixAddressMachine.Label)
  | addTwo | addOneQ | addOneS | addOneC
  | clear (i : Fin 5) | done
  deriving DecidableEq, Fintype

abbrev Control := (Option Bool × Bool) × Option Bool
def nextCopy : Fin 9 → Label
  | 0 => .addTwo
  | 1 => .copy 2 .scan
  | 2 => .addOneQ
  | 3 => .addOneS
  | 4 => .mul 2 .outer
  | 5 => .copy 6 .scan
  | 6 => .copy 7 .scan
  | 7 => .copy 8 .scan
  | 8 => .addOneC
def nextMul : Fin 4 → Label
  | 0 => .copy 1 .scan
  | 1 => .copy 3 .scan
  | 2 => .mul 3 .outer
  | 3 => .copy 5 .scan
def clearSlot : Fin 4 → Stack := ![24,25,26,27]

/-- The instruction table is fixed; no Nat input indexes into its labels. -/
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copy i l =>
      BitMachineInline.stmt (Label.copy i) (fun v => ((v, false), none))
        (fun v => v.1.1) (some (nextCopy i))
        (copyProgram (copySlots i) l)
  | .mul i l =>
      BitMachineInline.stmt (Label.mul i) (fun v => ((none, v), none))
        (fun v => v.1.2) (some (nextMul i))
        (multiplyProgram (mulSlots i) l)
  | .addTwo => .push 24 (fun _ => true)
      (.push 24 (fun _ => true) (.goto (fun _ => .mul 0 .outer)))
  | .addOneQ => .push 25 (fun _ => true) (.goto (fun _ => .mul 1 .outer))
  | .addOneS => .push 27 (fun _ => true) (.goto (fun _ => .copy 4 .scan))
  | .addOneC => .push 11 (fun _ => true) (.goto (fun _ => .clear 0))
  | .clear i => if h : i.val < 4 then
      BitMachineClearBank.clearStep (clearSlot ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => (none,false)) .done
  | .done => .halt

def initialControl : Control := ((none,false),none)

def run (n : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[n]) c

theorem run_add (m n : Nat) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :
    run (m+n) c = run n (run m c) := by
  rw [Nat.add_comm]
  exact Function.iterate_add_apply (advance program) n m c

theorem copy_phase (i : Fin 9) (S : Stack → List Bool)
    (hs : S ((copySlots i) 2) = []) :
    ∃ t ≤ 2 * (S ((copySlots i) 0)).length + 2,
      run t ⟨some (.copy i .scan), initialControl, S⟩ =
        ⟨some (nextCopy i), initialControl,
          Function.update S ((copySlots i) 1)
            (S ((copySlots i) 0) ++ S ((copySlots i) 1))⟩ := by
  let P := copyProgram (copySlots i)
  let n := 2 * (S ((copySlots i) 0)).length + 2
  have hr := copy_run (copySlots i) S hs
  let lc : TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool) :=
    ⟨some .scan, none, S⟩
  have hQ : ∀ l, program (.copy i l) =
      BitMachineInline.stmt (Label.copy i)
        (fun v : Option Bool => ((v,false),none))
        (fun v : Control => v.1.1) (some (nextCopy i)) (P l) := by
    intro l
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    (Label.copy i) (fun v : Option Bool => ((v,false),none))
    (fun v : Control => v.1.1) (by intro; rfl)
    (some (nextCopy i)) P program hQ lc n (by rw [hr])
  refine ⟨t, ht, ?_⟩
  simpa only [run, lc, P, n, BitMachineInline.cfg, hr,
    initialControl] using he

theorem mul_phase (i : Fin 4) (S : Stack → List Bool) (r w : Nat)
    (hr : S ((mulSlots i) 0) = unary r)
    (hw : S ((mulSlots i) 1) = unary w)
    (h2 : S ((mulSlots i) 2) = [])
    (h3 : S ((mulSlots i) 3) = [])
    (h4 : S ((mulSlots i) 4) = []) :
    ∃ t ≤ MatrixAddressMachine.exactTime r w 0,
      run t ⟨some (.mul i .outer), initialControl, S⟩ =
        ⟨some (nextMul i), initialControl,
          Function.update S ((mulSlots i) 5)
            (unary (r*w) ++ S ((mulSlots i) 5))⟩ := by
  let P := multiplyProgram (mulSlots i)
  let n := MatrixAddressMachine.exactTime r w 0
  have hm := multiply_run (mulSlots i) S r w hr hw h2 h3 h4
  let lc : TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool :=
    ⟨some .outer, false, S⟩
  have hQ : ∀ l, program (.mul i l) =
      BitMachineInline.stmt (Label.mul i)
        (fun v : Bool => ((none,v),none))
        (fun v : Control => v.1.2) (some (nextMul i)) (P l) := by
    intro l
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineInline.outputs
    (Label.mul i) (fun v : Bool => ((none,v),none))
    (fun v : Control => v.1.2) (by intro; rfl)
    (some (nextMul i)) P program hQ lc n (by rw [hm])
  refine ⟨t, ht, ?_⟩
  simpa only [run, lc, P, n, BitMachineInline.cfg, hm,
    initialControl, unary] using he

theorem addTwo_run (S : Stack → List Bool) :
    run 1 ⟨some .addTwo, initialControl, S⟩ =
      ⟨some (.mul 0 .outer), initialControl,
        Function.update S 24 (true :: true :: S 24)⟩ := by
  simp only [run, Function.iterate_one, advance, TM2.step, TM2.stepAux,
    program, Option.getD_some]
  congr 1
  funext j
  by_cases h : j = 24 <;> simp [h, Function.update]

theorem addOneQ_run (S : Stack → List Bool) :
    run 1 ⟨some .addOneQ, initialControl, S⟩ =
      ⟨some (.mul 1 .outer), initialControl,
        Function.update S 25 (true :: S 25)⟩ := by
  simp only [run, Function.iterate_one, advance, TM2.step, TM2.stepAux,
    program, Option.getD_some]

theorem addOneS_run (S : Stack → List Bool) :
    run 1 ⟨some .addOneS, initialControl, S⟩ =
      ⟨some (.copy 4 .scan), initialControl,
        Function.update S 27 (true :: S 27)⟩ := by
  simp only [run, Function.iterate_one, advance, TM2.step, TM2.stepAux,
    program, Option.getD_some]

theorem addOneC_run (S : Stack → List Bool) :
    run 1 ⟨some .addOneC, initialControl, S⟩ =
      ⟨some (.clear 0), initialControl,
        Function.update S 11 (true :: S 11)⟩ := by
  simp only [run, Function.iterate_one, advance, TM2.step, TM2.stepAux,
    program, Option.getD_some]

def clearCost (S : Stack → List Bool) :=
  (∑ i : Fin 4, (S (clearSlot i)).length) + 6

theorem clear_run (S : Stack → List Bool) :
    run (clearCost S) ⟨some (.clear 0), initialControl, S⟩ =
      ⟨none, initialControl, BitMachineClearBank.cleared clearSlot S⟩ := by
  have hs (i : Fin 4) : program (.clear i.castSucc) =
      BitMachineClearBank.clearStep (clearSlot i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [program, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : program (.clear (Fin.last 4)) =
      BitMachineClearBank.finishStep (fun _ => (none,false)) .done := by
    simp only [program, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hc := BitMachineClearBank.clear_bank_run program
    (fun _ => (none,false)) Label.done 4 clearSlot
    (by decide) Label.clear hs hf (none,false) S
  have hd : run 1
      ⟨some .done, initialControl, BitMachineClearBank.cleared clearSlot S⟩ =
      ⟨none, initialControl, BitMachineClearBank.cleared clearSlot S⟩ := by
    rfl
  have ht : clearCost S = ((∑ i : Fin 4, (S (clearSlot i)).length) + 4 + 1) + 1 := by
    unfold clearCost
    omega
  rw [ht, run_add]
  change run 1 (((advance program)^[(∑ i : Fin 4, (S (clearSlot i)).length) + 4 + 1])
    ⟨some (.clear 0), initialControl, S⟩) = _
  simp only [initialControl]
  rw [hc]
  exact hd

def bank1 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (initialBank s q1 q2 w Q p fuel mX mY) 24 (unary s)
def bank2 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank1 s q1 q2 w Q p fuel mX mY) 24 (unary (s+2))
def bank3 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank2 s q1 q2 w Q p fuel mX mY) 9 (unary (A s Q))

theorem first_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*s+2,
      run t ⟨some (.copy 0 .scan), initialControl,
        initialBank s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some .addTwo, initialControl, bank1 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := initialBank s q1 q2 w Q p fuel mX mY
  have hs : S ((copySlots 0) 2) = [] := by simp [S, copySlots, initialBank]
  obtain ⟨t, ht, hr⟩ := copy_phase 0 S hs
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, initialBank, unary] using ht
  · simpa [S, copySlots, bank1, initialBank, unary] using hr

theorem first_push (s q1 q2 w Q p fuel mX mY : Nat) :
    run 1 ⟨some .addTwo, initialControl, bank1 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.mul 0 .outer), initialControl,
        bank2 s q1 q2 w Q p fuel mX mY⟩ := by
  rw [addTwo_run]
  congr 1

theorem first_mul (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ MatrixAddressMachine.exactTime Q (s+2) 0,
      run t ⟨some (.mul 0 .outer), initialControl,
        bank2 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 1 .scan), initialControl,
        bank3 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank2 s q1 q2 w Q p fuel mX mY
  have ha : S ((mulSlots 0) 0) = unary Q := by
    simp [S, mulSlots, bank2, bank1, initialBank]
  have hb : S ((mulSlots 0) 1) = unary (s+2) := by
    simp [S, mulSlots, bank2]
  have h2 : S ((mulSlots 0) 2) = [] := by
    simp [S, mulSlots, bank2, bank1, initialBank]
  have h3 : S ((mulSlots 0) 3) = [] := by
    simp [S, mulSlots, bank2, bank1, initialBank]
  have h4 : S ((mulSlots 0) 4) = [] := by
    simp [S, mulSlots, bank2, bank1, initialBank]
  obtain ⟨t, ht, hr⟩ := mul_phase 0 S Q (s+2) ha hb h2 h3 h4
  refine ⟨t, ht, ?_⟩
  simpa [S, mulSlots, bank3, bank2, bank1, initialBank, A, unary] using hr

def bank4 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank3 s q1 q2 w Q p fuel mX mY) 25 (unary q1)
def bank5 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank4 s q1 q2 w Q p fuel mX mY) 25 (unary (s+q1))
def bank6 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank5 s q1 q2 w Q p fuel mX mY) 25 (unary (1+s+q1))
def bank7 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank6 s q1 q2 w Q p fuel mX mY) 26
    (unary (s*(1+s+q1)))

theorem second_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*q1+2,
      run t ⟨some (.copy 1 .scan), initialControl,
        bank3 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 2 .scan), initialControl,
        bank4 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank3 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 1 S
    (by simp [S, copySlots, bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank3, bank2, bank1, initialBank, unary] using ht
  · simpa [S, copySlots, bank4, bank3, bank2, bank1, initialBank, unary] using hr

theorem third_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*s+2,
      run t ⟨some (.copy 2 .scan), initialControl,
        bank4 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some .addOneQ, initialControl,
        bank5 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank4 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 2 S
    (by simp [S, copySlots, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank4, bank3, bank2, bank1, initialBank, unary] using ht
  · have he : unary s ++ unary q1 = unary (s+q1) := by
      unfold unary
      exact (List.replicate_add s q1 true).symm
    simpa [S, copySlots, bank5, bank4, he,
      bank3, bank2, bank1, initialBank] using hr

theorem second_push (s q1 q2 w Q p fuel mX mY : Nat) :
    run 1 ⟨some .addOneQ, initialControl, bank5 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.mul 1 .outer), initialControl,
        bank6 s q1 q2 w Q p fuel mX mY⟩ := by
  rw [addOneQ_run]
  congr 1
  funext j
  by_cases hj : j = 25
  · subst j
    simp [bank6, bank5, unary]
    rw [show 1+s+q1 = 1+(s+q1) by omega, List.replicate_add]
    simpa only [← List.replicate_add, Nat.one_add, List.replicate_succ]
  · simp [bank6, hj]

theorem second_mul (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ MatrixAddressMachine.exactTime s (1+s+q1) 0,
      run t ⟨some (.mul 1 .outer), initialControl,
        bank6 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 3 .scan), initialControl,
        bank7 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank6 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := mul_phase 1 S s (1+s+q1)
    (by simp [S, mulSlots, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank6])
    (by simp [S, mulSlots, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ht, ?_⟩
  simpa [S, mulSlots, bank7, bank6, bank5, bank4, bank3,
    bank2, bank1, initialBank, unary] using hr

def bank8 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank7 s q1 q2 w Q p fuel mX mY) 27 (unary s)
def bank9 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank8 s q1 q2 w Q p fuel mX mY) 27 (unary (1+s))
def bank10 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank9 s q1 q2 w Q p fuel mX mY) 27
    (unary (s*(1+s+q1)+1+s))
def bank11 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank10 s q1 q2 w Q p fuel mX mY) 10
    (unary (Q*(s*(1+s+q1)+1+s)))
def bank12 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank11 s q1 q2 w Q p fuel mX mY) 12 (unary (D w q2))
def bank13 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank12 s q1 q2 w Q p fuel mX mY) 11 (unary (D w q2))
def bank14 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank13 s q1 q2 w Q p fuel mX mY) 11 (unary (w+D w q2))
def bank15 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank14 s q1 q2 w Q p fuel mX mY) 11
    (unary (w+(w+D w q2)))
def bank16 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank15 s q1 q2 w Q p fuel mX mY) 11
    (unary (w+(w+(w+D w q2))))
def bank17 (s q1 q2 w Q p fuel mX mY : Nat) : Stack → List Bool :=
  Function.update (bank16 s q1 q2 w Q p fuel mX mY) 11
    (unary (1+(w+(w+(w+D w q2)))))

theorem fourth_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*s+2,
      run t ⟨some (.copy 3 .scan), initialControl,
        bank7 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some .addOneS, initialControl,
        bank8 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank7 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 3 S
    (by simp [S, copySlots, bank7, bank6, bank5, bank4,
      bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank7, bank6, bank5, bank4,
      bank3, bank2, bank1, initialBank, unary] using ht
  · simpa [S, copySlots, bank8, bank7, bank6, bank5, bank4,
      bank3, bank2, bank1, initialBank] using hr

theorem third_push (s q1 q2 w Q p fuel mX mY : Nat) :
    run 1 ⟨some .addOneS, initialControl, bank8 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 4 .scan), initialControl,
        bank9 s q1 q2 w Q p fuel mX mY⟩ := by
  rw [addOneS_run]
  congr 1
  funext j
  by_cases hj : j = 27
  · subst j
    simp [bank9, bank8, unary_push]
  · simp [bank9, hj]

theorem fifth_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*(s*(1+s+q1))+2,
      run t ⟨some (.copy 4 .scan), initialControl,
        bank9 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.mul 2 .outer), initialControl,
        bank10 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank9 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 4 S
    (by simp [S, copySlots, bank9, bank8, bank7, bank6,
      bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank9, bank8, bank7, bank6,
      bank5, bank4, bank3, bank2, bank1, initialBank, unary] using ht
  · have he : unary (s*(1+s+q1)) ++ unary (1+s) =
        unary (s*(1+s+q1)+1+s) := by
      rw [unary_append]
      congr 1
      omega
    simpa [S, copySlots, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank, he] using hr

theorem third_mul (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ MatrixAddressMachine.exactTime Q (s*(1+s+q1)+1+s) 0,
      run t ⟨some (.mul 2 .outer), initialControl,
        bank10 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.mul 3 .outer), initialControl,
        bank11 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank10 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := mul_phase 2 S Q (s*(1+s+q1)+1+s)
    (by simp [S, mulSlots, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank10])
    (by simp [S, mulSlots, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ht, ?_⟩
  simpa [S, mulSlots, bank11, bank10, bank9, bank8, bank7,
    bank6, bank5, bank4, bank3, bank2, bank1, initialBank, unary] using hr

theorem fourth_mul (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ MatrixAddressMachine.exactTime w q2 0,
      run t ⟨some (.mul 3 .outer), initialControl,
        bank11 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 5 .scan), initialControl,
        bank12 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank11 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := mul_phase 3 S w q2
    (by simp [S, mulSlots, bank11, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank11, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank11, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank11, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
    (by simp [S, mulSlots, bank11, bank10, bank9, bank8, bank7,
      bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ht, ?_⟩
  simpa [S, mulSlots, bank12, bank11, bank10, bank9, bank8,
    bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank, D, unary] using hr

theorem sixth_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*(D w q2)+2,
      run t ⟨some (.copy 5 .scan), initialControl,
        bank12 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 6 .scan), initialControl,
        bank13 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank12 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 5 S
    (by simp [S, copySlots, bank12, bank11, bank10, bank9,
      bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank12, unary] using ht
  · simpa [S, copySlots, bank13, bank12, bank11, bank10, bank9,
      bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank] using hr

theorem seventh_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*w+2,
      run t ⟨some (.copy 6 .scan), initialControl,
        bank13 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 7 .scan), initialControl,
        bank14 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank13 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 6 S
    (by simp [S, copySlots, bank13, bank12, bank11, bank10, bank9,
      bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank13, bank12, bank11, bank10, bank9,
      bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank, unary] using ht
  · have he : unary w ++ unary (D w q2) = unary (w+D w q2) := unary_append _ _
    have hw : S 3 = unary w := by
      simp [S, bank13, bank12, bank11, bank10, bank9, bank8,
        bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank]
    have hd : S 11 = unary (D w q2) := by simp [S, bank13]
    have h0 : (copySlots 6) 0 = 3 := rfl
    have h1 : (copySlots 6) 1 = 11 := rfl
    rw [h0, h1, hw, hd, he] at hr
    simpa only [S, nextCopy, bank14] using hr

theorem eighth_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*w+2,
      run t ⟨some (.copy 7 .scan), initialControl,
        bank14 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 8 .scan), initialControl,
        bank15 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank14 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 7 S
    (by simp [S, copySlots, bank14, bank13, bank12, bank11, bank10,
      bank9, bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank14, bank13, bank12, bank11, bank10,
      bank9, bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank, unary] using ht
  · have he : unary w ++ unary (w+D w q2) = unary (w+(w+D w q2)) := unary_append _ _
    have hw : S 3 = unary w := by
      simp [S, bank14, bank13, bank12, bank11, bank10, bank9,
        bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank]
    have hd : S 11 = unary (w+D w q2) := by simp [S, bank14]
    have h0 : (copySlots 7) 0 = 3 := rfl
    have h1 : (copySlots 7) 1 = 11 := rfl
    rw [h0, h1, hw, hd, he] at hr
    simpa only [S, nextCopy, bank15] using hr

theorem ninth_copy (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 2*w+2,
      run t ⟨some (.copy 8 .scan), initialControl,
        bank15 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some .addOneC, initialControl,
        bank16 s q1 q2 w Q p fuel mX mY⟩ := by
  let S := bank15 s q1 q2 w Q p fuel mX mY
  obtain ⟨t, ht, hr⟩ := copy_phase 8 S
    (by simp [S, copySlots, bank15, bank14, bank13, bank12, bank11,
      bank10, bank9, bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank])
  refine ⟨t, ?_, ?_⟩
  · simpa [S, copySlots, bank15, bank14, bank13, bank12, bank11,
      bank10, bank9, bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank, unary] using ht
  · have he : unary w ++ unary (w+(w+D w q2)) =
        unary (w+(w+(w+D w q2))) := unary_append _ _
    have hw : S 3 = unary w := by
      simp [S, bank15, bank14, bank13, bank12, bank11, bank10,
        bank9, bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, initialBank]
    have hd : S 11 = unary (w+(w+D w q2)) := by simp [S, bank15]
    have h0 : (copySlots 8) 0 = 3 := rfl
    have h1 : (copySlots 8) 1 = 11 := rfl
    rw [h0, h1, hw, hd, he] at hr
    simpa only [S, nextCopy, bank16] using hr

theorem fourth_push (s q1 q2 w Q p fuel mX mY : Nat) :
    run 1 ⟨some .addOneC, initialControl, bank16 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.clear 0), initialControl,
        bank17 s q1 q2 w Q p fuel mX mY⟩ := by
  rw [addOneC_run]
  congr 1
  funext j
  by_cases hj : j = 11
  · subst j
    simp [bank17, bank16, unary_push]
  · simp [bank17, hj]

theorem cleared_bank17_eq_final (s q1 q2 w Q p fuel mX mY : Nat) :
    BitMachineClearBank.cleared clearSlot
      (bank17 s q1 q2 w Q p fuel mX mY) =
      finalBank s q1 q2 w Q p fuel mX mY := by
  have hB : s*(1+s+q1)+1+s = s+1+s*(q1+s+1) := by ring
  have hslot (j : Stack) :
      (∃ i : Fin 4, clearSlot i = j) ↔
        j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 := by
    fin_cases j <;> decide
  funext j
  -- Stack 11 is the only residual goal after the bank simplification:
  -- `unary (1+(w+(w+(w+w*q2)))) = unary (1+3*w+w*q2)`, closed by `ring`.
  fin_cases j <;>
    simp [BitMachineClearBank.cleared, hslot, bank17, bank16,
      bank15, bank14, bank13, bank12, bank11, bank10, bank9,
      bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1,
      initialBank, finalBank, A, B, C, D, hB]
  congr 1
  ring

theorem cleanup (s q1 q2 w Q p fuel mX mY : Nat) :
    run (clearCost (bank17 s q1 q2 w Q p fuel mX mY))
      ⟨some (.clear 0), initialControl,
        bank17 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨none, initialControl,
        finalBank s q1 q2 w Q p fuel mX mY⟩ := by
  rw [clear_run, cleared_bank17_eq_final]

theorem join {l m : Label} {S T U : Stack → List Bool} {a b : Nat}
    (ha : ∃ t ≤ a, run t ⟨some l, initialControl, S⟩ =
      ⟨some m, initialControl, T⟩)
    (hb : ∃ t ≤ b, run t ⟨some m, initialControl, T⟩ =
      ⟨none, initialControl, U⟩) :
    ∃ t ≤ a+b, run t ⟨some l, initialControl, S⟩ =
      ⟨none, initialControl, U⟩ := by
  obtain ⟨x, hx, hxr⟩ := ha
  obtain ⟨y, hy, hyr⟩ := hb
  refine ⟨x+y, by omega, ?_⟩
  rw [run_add, hxr, hyr]

theorem join_running {l m n : Label} {S T U : Stack → List Bool} {a b : Nat}
    (ha : ∃ t ≤ a, run t ⟨some l, initialControl, S⟩ =
      ⟨some m, initialControl, T⟩)
    (hb : ∃ t ≤ b, run t ⟨some m, initialControl, T⟩ =
      ⟨some n, initialControl, U⟩) :
    ∃ t ≤ a+b, run t ⟨some l, initialControl, S⟩ =
      ⟨some n, initialControl, U⟩ := by
  obtain ⟨x, hx, hxr⟩ := ha
  obtain ⟨y, hy, hyr⟩ := hb
  refine ⟨x+y, by omega, ?_⟩
  rw [run_add, hxr, hyr]

/-! ## Whole-bank endpoint and explicit charged clock -/

/-- Exact cost of the physical clear of scratch stacks 24..27 in `bank17`. -/
def cleanupCost (s q1 : Nat) : Nat :=
  (s+2) + (1+s+q1) + s*(1+s+q1) + (s*(1+s+q1)+1+s) + 6

theorem clearCost_bank17 (s q1 q2 w Q p fuel mX mY : Nat) :
    clearCost (bank17 s q1 q2 w Q p fuel mX mY) = cleanupCost s q1 := by
  simp [clearCost, cleanupCost, Fin.sum_univ_four, clearSlot, bank17, bank16,
    bank15, bank14, bank13, bank12, bank11, bank10, bank9,
    bank8, bank7, bank6, bank5, bank4, bank3, bank2, bank1, unary]

/-- The charged clock: the sum of the eighteen phase bounds (nine inlined
copies, four inlined unary multiplications, four constant pushes and the
physical clear-and-reset of 24..27). It depends only on the raw counts. -/
def clock (s q1 q2 w Q : Nat) : Nat :=
  (2*s+2) + 1 + MatrixAddressMachine.exactTime Q (s+2) 0 +
  (2*q1+2) + (2*s+2) + 1 + MatrixAddressMachine.exactTime s (1+s+q1) 0 +
  (2*s+2) + 1 + (2*(s*(1+s+q1))+2) +
  MatrixAddressMachine.exactTime Q (s*(1+s+q1)+1+s) 0 +
  MatrixAddressMachine.exactTime w q2 0 +
  (2*(D w q2)+2) + (2*w+2) + (2*w+2) + (2*w+2) + 1 + cleanupCost s q1

/-- Whole-bank endpoint: one fixed controller, started at `.copy 0 .scan` on
the raw nine-count bank with every other stack empty, halts within `clock`
with exactly `finalBank`: raw 0..8 preserved, A/B/C/D at 9..12, and every
other stack (including scratch 17..20 and 24..27) empty. -/
theorem whole_run (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ clock s q1 q2 w Q,
      run t ⟨some (.copy 0 .scan), initialControl,
        initialBank s q1 q2 w Q p fuel mX mY⟩ =
      ⟨none, initialControl, finalBank s q1 q2 w Q p fuel mX mY⟩ := by
  have e2 : ∃ t ≤ 1, run t ⟨some .addTwo, initialControl,
      bank1 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.mul 0 .outer), initialControl, bank2 s q1 q2 w Q p fuel mX mY⟩ :=
    ⟨1, le_rfl, first_push s q1 q2 w Q p fuel mX mY⟩
  have e6 : ∃ t ≤ 1, run t ⟨some .addOneQ, initialControl,
      bank5 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.mul 1 .outer), initialControl, bank6 s q1 q2 w Q p fuel mX mY⟩ :=
    ⟨1, le_rfl, second_push s q1 q2 w Q p fuel mX mY⟩
  have e9 : ∃ t ≤ 1, run t ⟨some .addOneS, initialControl,
      bank8 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.copy 4 .scan), initialControl, bank9 s q1 q2 w Q p fuel mX mY⟩ :=
    ⟨1, le_rfl, third_push s q1 q2 w Q p fuel mX mY⟩
  have e17 : ∃ t ≤ 1, run t ⟨some .addOneC, initialControl,
      bank16 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨some (.clear 0), initialControl, bank17 s q1 q2 w Q p fuel mX mY⟩ :=
    ⟨1, le_rfl, fourth_push s q1 q2 w Q p fuel mX mY⟩
  have e18 : ∃ t ≤ cleanupCost s q1, run t ⟨some (.clear 0), initialControl,
      bank17 s q1 q2 w Q p fuel mX mY⟩ =
      ⟨none, initialControl, finalBank s q1 q2 w Q p fuel mX mY⟩ :=
    ⟨_, le_of_eq (clearCost_bank17 s q1 q2 w Q p fuel mX mY),
      cleanup s q1 q2 w Q p fuel mX mY⟩
  obtain ⟨t, ht, h⟩ :=
    join (first_copy s q1 q2 w Q p fuel mX mY) <| join e2 <|
    join (first_mul s q1 q2 w Q p fuel mX mY) <|
    join (second_copy s q1 q2 w Q p fuel mX mY) <|
    join (third_copy s q1 q2 w Q p fuel mX mY) <| join e6 <|
    join (second_mul s q1 q2 w Q p fuel mX mY) <|
    join (fourth_copy s q1 q2 w Q p fuel mX mY) <| join e9 <|
    join (fifth_copy s q1 q2 w Q p fuel mX mY) <|
    join (third_mul s q1 q2 w Q p fuel mX mY) <|
    join (fourth_mul s q1 q2 w Q p fuel mX mY) <|
    join (sixth_copy s q1 q2 w Q p fuel mX mY) <|
    join (seventh_copy s q1 q2 w Q p fuel mX mY) <|
    join (eighth_copy s q1 q2 w Q p fuel mX mY) <|
    join (ninth_copy s q1 q2 w Q p fuel mX mY) <| join e17 e18
  refine ⟨t, ht.trans (le_of_eq ?_), h⟩
  simp only [clock]
  ring

theorem run_halted (n : Nat) (v : Control) (S : Stack → List Bool) :
    run n ⟨none, v, S⟩ = ⟨none, v, S⟩ :=
  Function.iterate_fixed (f := advance program) rfl n

/-- The same endpoint at any clock value at least `clock`: the halted
configuration is a fixed point of `advance`. -/
theorem whole_run_at (s q1 q2 w Q p fuel mX mY T : Nat)
    (hT : clock s q1 q2 w Q ≤ T) :
    run T ⟨some (.copy 0 .scan), initialControl,
        initialBank s q1 q2 w Q p fuel mX mY⟩ =
      ⟨none, initialControl, finalBank s q1 q2 w Q p fuel mX mY⟩ := by
  obtain ⟨t, ht, h⟩ := whole_run s q1 q2 w Q p fuel mX mY
  have hsplit : T = t + (T - t) := by omega
  rw [hsplit, run_add, h, run_halted]

theorem exactTime_mono {r w r' w' : Nat} (hr : r ≤ r') (hw : w ≤ w') :
    MatrixAddressMachine.exactTime r w 0 ≤
      MatrixAddressMachine.exactTime r' w' 0 := by
  unfold MatrixAddressMachine.exactTime
  have h : 2 * r * w ≤ 2 * r' * w' :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr) hw
  omega

theorem clock_mono {s q1 q2 w Q n : Nat} (hs : s ≤ n) (h1 : q1 ≤ n)
    (h2 : q2 ≤ n) (hw : w ≤ n) (hQ : Q ≤ n) :
    clock s q1 q2 w Q ≤ clock n n n n n := by
  have hsq : s*(1+s+q1) ≤ n*(1+n+n) := Nat.mul_le_mul hs (by omega)
  have e1 := exactTime_mono (w := s+2) (w' := n+2) hQ (by omega)
  have e2 := exactTime_mono (w := 1+s+q1) (w' := 1+n+n) hs (by omega)
  have e3 := exactTime_mono (w := s*(1+s+q1)+1+s) (w' := n*(1+n+n)+1+n)
    hQ (by omega)
  have e4 := exactTime_mono hw h2
  have hD : D w q2 ≤ D n n := Nat.mul_le_mul hw h2
  have hc : cleanupCost s q1 ≤ cleanupCost n n := by
    unfold cleanupCost
    omega
  unfold clock
  omega

theorem clock_diag (n : Nat) :
    clock n n n n n = 4*n^3 + 22*n^2 + 46*n + 48 := by
  simp only [clock, cleanupCost, D, MatrixAddressMachine.exactTime]
  ring

/-- Explicit polynomial clock in the raw unary lengths. -/
theorem clock_le (s q1 q2 w Q : Nat) :
    clock s q1 q2 w Q ≤ 120 * (s+q1+q2+w+Q+1)^3 := by
  set n := s+q1+q2+w+Q+1 with hn
  have hmono := clock_mono (s := s) (q1 := q1) (q2 := q2) (w := w) (Q := Q)
    (n := n) (by omega) (by omega) (by omega) (by omega) (by omega)
  rw [clock_diag] at hmono
  have h1 : 1 ≤ n := by omega
  have h2 : n ≤ n^2 := by nlinarith
  have h3 : n^2 ≤ n^3 := by
    rw [pow_succ]
    nlinarith
  have h4 : 1 ≤ n^3 := by nlinarith
  nlinarith

/-- Public whole-bank endpoint with the explicit polynomial clock. -/
theorem whole_run_poly (s q1 q2 w Q p fuel mX mY : Nat) :
    ∃ t ≤ 120 * (s+q1+q2+w+Q+1)^3,
      run t ⟨some (.copy 0 .scan), initialControl,
        initialBank s q1 q2 w Q p fuel mX mY⟩ =
      ⟨none, initialControl, finalBank s q1 q2 w Q p fuel mX mY⟩ := by
  obtain ⟨t, ht, h⟩ := whole_run s q1 q2 w Q p fuel mX mY
  exact ⟨t, ht.trans (clock_le s q1 q2 w Q), h⟩

#print axioms cleared_bank17_eq_final
#print axioms cleanup
#print axioms clearCost_bank17
#print axioms whole_run
#print axioms run_halted
#print axioms whole_run_at
#print axioms exactTime_mono
#print axioms clock_mono
#print axioms clock_diag
#print axioms clock_le
#print axioms whole_run_poly
end Paper2.DrawCoefficients
