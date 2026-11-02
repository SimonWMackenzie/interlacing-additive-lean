import EthInapproximability.CurrentPaper.QLog
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.ParameterizedNP.GuardedSourceSlab
import Mathlib.Data.Fin.VecNotation

/-! The checked physical unary-power controller writes the q₂ word directly
to previously blank weighted-writer cell 56. -/

namespace EthInapproximability.CurrentPaper.QPower

open Turing BitMachineEncoding
noncomputable section

abbrev Stack := QProduct.Stack

def slots : MatrixUnaryPower.Stack ↪ Stack where
  toFun
    | .inl 0 => QProduct.q
    | .inl 1 => QProduct.temp 7
    | .inl _ => QProduct.temp 8
    | .inr () => QLog.answer
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b
    · fin_cases a <;> fin_cases b <;> simp [QProduct.q,QProduct.temp] at h ⊢
    · cases b; fin_cases a <;> simp [QProduct.q,QProduct.temp,QLog.answer,
        QProduct.log] at h
    · cases a; fin_cases b <;> simp [QProduct.q,QProduct.temp,QLog.answer,
        QProduct.log] at h
    · cases a; cases b; rfl

def program := MatrixStage4ScalarPreparationOps.unaryPowerProgram slots

theorem power_run (S : Stack → List Bool) (n : ℕ)
    (ha : S QLog.answer = List.replicate (Nat.clog 2 n) true)
    (hq : S QProduct.q = [])
    (h7 : S (QProduct.temp 7) = [])
    (h8 : S (QProduct.temp 8) = []) :
    ∃ t ≤ 4 * 2 ^ Nat.clog 2 n + 5 * Nat.clog 2 n + 7,
      ((advance program)^[t])
        (⟨some (.inr false),((false,false),none),S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            MatrixUnaryPower.Label MatrixUnaryPower.Control) =
        ⟨none,((false,false),none),
          Function.update S QProduct.q
            (List.replicate (2 ^ Nat.clog 2 n) true)⟩ := by
  simpa [program,slots,QProduct.q,QProduct.temp,QLog.answer] using
    MatrixStage4ScalarPreparationOps.unary_power_run slots S
      (Nat.clog 2 n) ha hq h7 h8

theorem output_exact {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : ParameterizedNP.GuardedSourceGraph.EndpointGraph V E)
    (bins : ℕ) (S : Stack → List Bool)
    (ha : S QLog.answer =
      List.replicate (Nat.clog 2 (12*bins*Fintype.card E)) true)
    (hq : S QProduct.q = [])
    (h7 : S (QProduct.temp 7) = [])
    (h8 : S (QProduct.temp 8) = []) :
    ∃ t ≤ 4 * ParameterizedNP.GuardedSourceSlab.q2 G bins +
      5 * Nat.clog 2 (12*bins*Fintype.card E) + 7,
      ∃ F : Stack → List Bool,
        ((advance program)^[t])
          (⟨some (.inr false),((false,false),none),S⟩ :
            TM2.Cfg (fun _ : Stack => Bool)
              MatrixUnaryPower.Label MatrixUnaryPower.Control) =
          ⟨none,((false,false),none),F⟩ ∧
        F QProduct.q =
          List.replicate (ParameterizedNP.GuardedSourceSlab.q2 G bins) true := by
  obtain ⟨t,ht,hr⟩ := power_run S (12*bins*Fintype.card E) ha hq h7 h8
  refine ⟨t,by simpa [ParameterizedNP.GuardedSourceSlab.q2] using ht,
    _,hr,?_⟩
  simp [ParameterizedNP.GuardedSourceSlab.q2]

#print axioms power_run
#print axioms output_exact

end
end EthInapproximability.CurrentPaper.QPower
