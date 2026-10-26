import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.Construction
import Mathlib.Data.Fin.VecNotation

/-! Produce the exact `qOne a = 2^a - 2` unary word from writer cell54.
The two subtractions are two literal Boolean-stack pops. -/

namespace EthInapproximability.CurrentPaper.WeightedMWidth

open Turing BitMachineEncoding
noncomputable section

abbrev Stack := Fin 64 ⊕ Fin 15
def writer (j : Fin 64) : Stack := .inl j
def scalar (j : Fin 15) : Stack := .inr j
def width : Stack := scalar 3

def powerSlots : MatrixUnaryPower.Stack ↪ Stack where
  toFun
    | .inl 0 => width
    | .inl 1 => scalar 4
    | .inl _ => scalar 5
    | .inr () => writer 54
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> simp [width,scalar] at h ⊢
    · cases b; fin_cases a <;> simp [width,scalar,writer] at h
    · cases a; fin_cases b <;> simp [width,scalar,writer] at h
    · cases a; cases b; rfl

def powerProgram := MatrixStage4ScalarPreparationOps.unaryPowerProgram powerSlots

theorem power_run (S : Stack → List Bool) (a : ℕ)
    (ha : S (writer 54) = List.replicate a true)
    (h3 : S width = []) (h4 : S (scalar 4) = [])
    (h5 : S (scalar 5) = []) :
    ∃ t ≤ 4*2^a + 5*a + 7,
      ((advance powerProgram)^[t])
        (⟨some (.inr false),((false,false),none),S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none,((false,false),none),
          Function.update S width (List.replicate (2^a) true)⟩ := by
  simpa [powerProgram,powerSlots,width,scalar,writer] using
    MatrixStage4ScalarPreparationOps.unary_power_run powerSlots S a
      ha h3 h4 h5

def popProgram : Unit → TM2.Stmt (fun _ : Stack => Bool) Unit Unit :=
  fun _ => .pop width (fun _ _ => ())
    (.pop width (fun _ _ => ()) .halt)

theorem pop_run (S : Stack → List Bool) (a : ℕ)
    (h : S width = List.replicate (2^a) true) :
    advance popProgram
      (⟨some (),(),S⟩ : TM2.Cfg (fun _ : Stack => Bool) Unit Unit) =
      ⟨none,(),Function.update S width
        (List.replicate (Construction.qOne a) true)⟩ := by
  simp [popProgram,advance,TM2.step,TM2.stepAux,h,
    Construction.qOne,Function.update,Nat.sub_sub]

#print axioms power_run
#print axioms pop_run

end
end EthInapproximability.CurrentPaper.WeightedMWidth
