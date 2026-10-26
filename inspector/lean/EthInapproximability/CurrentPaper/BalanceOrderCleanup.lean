import EthInapproximability.CurrentPaper.BalanceOrderArithmetic
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Charged clearing of every arithmetic scratch cell after unary power. -/

namespace EthInapproximability.CurrentPaper.BalanceOrderCleanup

open Turing BitMachineEncoding BalanceOrderArithmetic
open BitMachineClearBank

inductive Label where
  | c0 | c1 | c2 | c3 | c4 | finish | done
  deriving DecidableEq, Fintype

def clearSlots : Fin 5 → Stack := ![2,6,7,8,10]
def labels : Fin 6 → Label := ![.c0,.c1,.c2,.c3,.c4,.finish]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Unit × Option Bool)
  | .c0 => clearStep 2 .c0 .c1
  | .c1 => clearStep 6 .c1 .c2
  | .c2 => clearStep 7 .c2 .c3
  | .c3 => clearStep 8 .c3 .c4
  | .c4 => clearStep 10 .c4 .finish
  | .finish => finishStep id .done
  | .done => .halt

def finalBank (s : ℕ) : Stack → List Bool :=
  ![unary s, unary (2^(exponent s)), [], [], [], [], [], [], [], [], [], [], []]

def clearTime (s : ℕ) : ℕ :=
  (∑ i : Fin 5, ((afterPower s) (clearSlots i)).length) + 7

private theorem cleared_eq (s : ℕ) :
    cleared clearSlots (afterPower s) = finalBank s := by
  have hm (k : Stack) :
      (∃ i : Fin 5, clearSlots i = k) ↔
        (k = 2 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 10) := by
    fin_cases k <;> decide
  funext k
  fin_cases k <;>
    simp [cleared, hm, afterPower, afterMult2, finalBank]

theorem cleanup_run (s : ℕ) :
    ((advance program)^[clearTime s])
      (⟨some .c0,((),none),afterPower s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Unit × Option Bool)) =
      ⟨none,((),none),finalBank s⟩ := by
  have hinj : Function.Injective clearSlots := by decide
  have hsteps : ∀ i : Fin 5,
      program (labels i.castSucc) =
        clearStep (clearSlots i) (labels i.castSucc) (labels i.succ) := by
    intro i; fin_cases i <;> rfl
  have hfinish : program (labels (Fin.last 5)) =
      finishStep id .done := rfl
  have hr := clear_bank_run program id Label.done 5 clearSlots hinj
    labels hsteps hfinish () (afterPower s)
  have hend : advance program
      (⟨some .done,((),none),cleared clearSlots (afterPower s)⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Unit × Option Bool)) =
      ⟨none,((),none),cleared clearSlots (afterPower s)⟩ := by
    rfl
  have hr' : ((advance program)^[(∑ i : Fin 5,
      ((afterPower s) (clearSlots i)).length) + 5 + 1])
      (⟨some .c0,((),none),afterPower s⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Label (Unit × Option Bool)) =
      ⟨some .done,((),none),cleared clearSlots (afterPower s)⟩ := by
    simpa only [show labels 0 = Label.c0 from rfl, id_eq] using hr
  unfold clearTime
  rw [show (∑ i : Fin 5, ((afterPower s) (clearSlots i)).length) + 7 =
      ((∑ i : Fin 5, ((afterPower s) (clearSlots i)).length) + 5 + 1) + 1
    by omega, Function.iterate_succ_apply']
  rw [hr', hend, cleared_eq]

def fullProgram := BitMachineRawSequence.program prog01234 program
  Label.c0 ((((false,false),none),false),((false,false),none)) ((),none)

def start := BitMachineRawSequence.leftLabel (LB := Label) start01234
def fullTime (s : ℕ) : ℕ := arithmeticTime s + clearTime s + 1

theorem balance_order_run (s : ℕ) :
    ∃ u ≤ fullTime s,
      ((advance fullProgram)^[u])
        (⟨some start,
          (((((false,false),none),false),((false,false),none)),((),none)),
          initial s⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (((((false,false),none),false),((false,false),none)),((),none)),
          finalBank s⟩ := by
  obtain ⟨u,hu,hr⟩ := joined_run s
  obtain ⟨v,hv,hvr⟩ := BitMachineRawSequence.runs
    prog01234 program start01234 .c0
    ((((false,false),none),false),((false,false),none))
    ((((false,false),none),false),((false,false),none))
    ((),none) ((),none)
    (initial s) (afterPower s) (finalBank s)
    u (clearTime s)
    (by simpa only [prog01234, start01234] using hr) (cleanup_run s)
  exact ⟨v, by unfold fullTime; omega,
    by simpa only [fullProgram, start] using hvr⟩

#print axioms cleanup_run
#print axioms balance_order_run

end EthInapproximability.CurrentPaper.BalanceOrderCleanup
