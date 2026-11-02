import EthInapproximability.CurrentPaper.PhysicalLevelRun
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineInput

/-! Lane owner:b-weighted-level-4, unit 2, segment 2 (levels j > 0), piece 2a:
the TARGET of the per-level charged update program, as literal identities.
No machine claim.

For the physical sequence `physRun` (frozen `PhysicalLevelRun`), the six raw
words `ETHParameterScaleMachineInput.words` consumed at level `j+1` are:
`c`, `b`, the cost word `y_j + j + firstExponent p + secondExponent p +
binExponent p + outerExponent p + restorationExponent p + 1` (`p` = level-`j`
parameters), the rows and columns of the PHYSICAL level-`j+1` matrix, and
`|E|`; and the physical budget satisfies
`y_{j+1} + (j+1) = y_j + j + (the same five exponents) + 1`.
Reused by exact name: production `EffectiveIteration.runParameters_succ`
(= `step_next_parameters`), `Iteration.step_width_matches`, frozen
`PhysicalLevelRun.physRun_budget_eq/rows_eq/columns_eq/physParameters_eq`. -/

namespace EthInapproximability.CurrentPaper.PhysicalLevelWords

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open Iteration EffectiveIteration PhysicalLevelRun

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem words_cell (i : Parameters.Input) :
    ETHParameterScaleMachineInput.words i 0 = List.replicate i.sourceConstant true ∧
    ETHParameterScaleMachineInput.words i 1 = List.replicate i.nextDepth true ∧
    ETHParameterScaleMachineInput.words i 2 = List.replicate i.cost true ∧
    ETHParameterScaleMachineInput.words i 3 = List.replicate i.rows true ∧
    ETHParameterScaleMachineInput.words i 4 = List.replicate i.columns true ∧
    ETHParameterScaleMachineInput.words i 5 = List.replicate i.edges true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The six raw words at level `j+1` of the physical run, cell by cell. -/
theorem words_succ (G : EndpointGraph V E) (c b j : ℕ) :
    ETHParameterScaleMachineInput.words (runParameters G c b (seedState b) (j + 1)) 0 =
        List.replicate c true ∧
    ETHParameterScaleMachineInput.words (runParameters G c b (seedState b) (j + 1)) 1 =
        List.replicate b true ∧
    ETHParameterScaleMachineInput.words (runParameters G c b (seedState b) (j + 1)) 2 =
        List.replicate ((runParameters G c b (seedState b) j).cost +
          Parameters.firstExponent (runParameters G c b (seedState b) j) +
          Parameters.secondExponent (runParameters G c b (seedState b) j) +
          Parameters.binExponent (runParameters G c b (seedState b) j) +
          Parameters.outerExponent (runParameters G c b (seedState b) j) +
          Parameters.restorationExponent (runParameters G c b (seedState b) j) + 1) true ∧
    ETHParameterScaleMachineInput.words (runParameters G c b (seedState b) (j + 1)) 3 =
        List.replicate (physRun G c b (seedState b) (j + 1)).matrix.rows true ∧
    ETHParameterScaleMachineInput.words (runParameters G c b (seedState b) (j + 1)) 4 =
        List.replicate (physRun G c b (seedState b) (j + 1)).matrix.columns true ∧
    ETHParameterScaleMachineInput.words (runParameters G c b (seedState b) (j + 1)) 5 =
        List.replicate (Fintype.card E) true := by
  obtain ⟨w0, w1, w2, w3, w4, w5⟩ := words_cell (runParameters G c b (seedState b) (j + 1))
  have hs := runParameters_succ G c b (seedState b) j
  have hr := physRun_rows_eq G c b (seedState b) (j + 1)
  have hc := physRun_columns_eq G c b (seedState b) (j + 1)
  have e2 : (runParameters G c b (seedState b) (j + 1)).cost =
      (runParameters G c b (seedState b) j).cost +
          Parameters.firstExponent (runParameters G c b (seedState b) j) +
          Parameters.secondExponent (runParameters G c b (seedState b) j) +
          Parameters.binExponent (runParameters G c b (seedState b) j) +
          Parameters.outerExponent (runParameters G c b (seedState b) j) +
          Parameters.restorationExponent (runParameters G c b (seedState b) j) + 1 := by
    rw [hs]
    rfl
  have e3 : (runParameters G c b (seedState b) (j + 1)).rows =
      (physRun G c b (seedState b) (j + 1)).matrix.rows := by
    rw [hr]
    rfl
  have e4 : (runParameters G c b (seedState b) (j + 1)).columns =
      (physRun G c b (seedState b) (j + 1)).matrix.columns := by
    rw [hc]
    rfl
  refine ⟨w0, w1, ?_, ?_, ?_, w5⟩
  · rw [w2, e2]
  · rw [w3, e3]
  · rw [w4, e4]

/-- The public budget recurrence of the physical run, in the raw-word form. -/
theorem budget_succ (G : EndpointGraph V E) (c b j : ℕ) :
    (physRun G c b (seedState b) (j + 1)).budget + (j + 1) =
      (physRun G c b (seedState b) j).budget + j +
        Parameters.firstExponent (runParameters G c b (seedState b) j) +
        Parameters.secondExponent (runParameters G c b (seedState b) j) +
        Parameters.binExponent (runParameters G c b (seedState b) j) +
        Parameters.outerExponent (runParameters G c b (seedState b) j) +
        Parameters.restorationExponent (runParameters G c b (seedState b) j) + 1 := by
  have hs := congrArg Parameters.Input.cost (runParameters_succ G c b (seedState b) j)
  have h1 := physRun_budget_eq G c b (seedState b) (j + 1)
  have h0 := physRun_budget_eq G c b (seedState b) j
  have e1 : (runParameters G c b (seedState b) (j + 1)).cost =
      (run G c b (seedState b) (j + 1)).budget + (j + 1) := rfl
  have e0 : (runParameters G c b (seedState b) j).cost =
      (run G c b (seedState b) j).budget + j := rfl
  rw [h1, h0, ← e1, ← e0, hs]
  rfl

/-- The second width used by the physical step is the parameter record's
`secondWidth` (production `step_width_matches`, restated at the run). -/
theorem width_matches_run (G : EndpointGraph V E) (c b j : ℕ) :
    q₂ G c b (run G c b (seedState b) j).budget j (run G c b (seedState b) j).matrix =
      Parameters.secondWidth (runParameters G c b (seedState b) j) :=
  step_width_matches G c b _ j _

#print axioms words_succ
#print axioms budget_succ
#print axioms width_matches_run

end EthInapproximability.CurrentPaper.PhysicalLevelWords
