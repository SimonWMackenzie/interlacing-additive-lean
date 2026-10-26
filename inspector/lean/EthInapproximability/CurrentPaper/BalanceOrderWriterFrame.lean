import EthInapproximability.CurrentPaper.BalanceOrderActualScale
import EthInapproximability.CurrentPaper.BalanceOrderCost
import EthInapproximability.CurrentPaper.ColumnInputStaging

/-! Writer-preserving embedding of the raw-parameter balance-order producer. -/

namespace EthInapproximability.CurrentPaper.BalanceOrderWriterFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

abbrev Stack := BalanceOrderActualScale.Stack ⊕ Fin 64
def slots : BalanceOrderActualScale.Stack ↪ Stack :=
  ⟨Sum.inl, by intro a b h; exact Sum.inl_injective h⟩

def foreign (W : Fin 64 → List Bool) : Stack → List Bool
  | .inl _ => []
  | .inr k => W k

def initialBank (i : Parameters.Input) (W : Fin 64 → List Bool) :
    Stack → List Bool :=
  bank slots (foreign W) (BalanceOrderActualScale.initialBank i)

def program := fun l => stackStmt slots (BalanceOrderActualScale.program l)

theorem writer_framed_run (i : Parameters.Input)
    (W : Fin 64 → List Bool) :
    ∃ u ≤ BalanceOrderActualScale.totalBound i,
      ∃ F : ETHScaleActualComplete.Stack → List Bool,
      ((advance program)^[u])
        (⟨some BalanceOrderActualScale.start,
          ((BalanceOrderActualScale.scaleControl,none),
            BalanceOrderActualScale.arithmeticControl),
          initialBank i W⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          ((BalanceOrderActualScale.scaleControl,none),
            BalanceOrderActualScale.arithmeticControl),
          bank slots (foreign W)
            (Function.update
              (Function.update
                (bank BalanceOrderActualScale.scaleSlots
                  BalanceOrderActualScale.foreignBank F)
                (.inr 0) (BalanceOrderArithmetic.unary (Parameters.scale i)))
              (.inr 1)
              (BalanceOrderArithmetic.unary (Parameters.balanceOrder i)))⟩ ∧
      F (.inr ScaleFinalScratch.answerKey) =
        BalanceOrderArithmetic.unary (Parameters.scale i) ∧
      (∀ j : Fin 6, F (.inl (ETHScaleGlobalLog.raw j)) =
        ETHParameterScaleMachineInput.words i j) ∧
      (∀ k : Fin 64,
        (bank slots (foreign W)
          (Function.update
            (Function.update
              (bank BalanceOrderActualScale.scaleSlots
                BalanceOrderActualScale.foreignBank F)
              (.inr 0) (BalanceOrderArithmetic.unary (Parameters.scale i)))
            (.inr 1)
              (BalanceOrderArithmetic.unary (Parameters.balanceOrder i))))
          (.inr k) = W k) := by
  obtain ⟨u,hu,F,hr,hs,hraw⟩ :=
    BalanceOrderActualScale.actual_balance_order_run i
  have he := BitMachineStackRun.run slots (foreign W)
    BalanceOrderActualScale.program
    (⟨some BalanceOrderActualScale.start,
      ((BalanceOrderActualScale.scaleControl,none),
        BalanceOrderActualScale.arithmeticControl),
      BalanceOrderActualScale.initialBank i⟩ :
        TM2.Cfg (fun _ : BalanceOrderActualScale.Stack => Bool) _ _) u
  rw [hr] at he
  refine ⟨u,hu,F,?_,hs,hraw,?_⟩
  · simpa only [program, initialBank, stackCfg] using he
  · intro k
    exact bank_outside slots (foreign W) _ (.inr k)
      (by rintro ⟨j,h⟩; cases h)

theorem writer_framed_output_clock (i : Parameters.Input) :
    BalanceOrderActualScale.totalBound i ≤
      ETHScaleActualComplete.totalBound i + 2*Parameters.scale i + 4 +
        1000000000*(Parameters.balanceOrder i+1)^2 := by
  have hc : BalanceOrderCleanup.fullTime (Parameters.scale i) ≤
      1000000000*(Parameters.balanceOrder i+1)^2 := by
    simpa only [Parameters.balanceOrder, Parameters.balanceExponent,
      BalanceOrderArithmetic.exponent] using
      BalanceOrderCost.fullTime_output_bound (Parameters.scale i)
  unfold BalanceOrderActualScale.totalBound
  omega

#print axioms writer_framed_run
#print axioms writer_framed_output_clock

end
end EthInapproximability.CurrentPaper.BalanceOrderWriterFrame
