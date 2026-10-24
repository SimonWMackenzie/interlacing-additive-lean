import EthInapproximability.CurrentPaper.ETHTailRuntimeAbsorption

/-!
# Exact machine-level contradiction supplied by ETH

ETH first fixes its forbidden exponent. A smaller source exponent may then be
chosen. This theorem rules out a finite Boolean-stack SAT machine with the
displayed source-count-times-table-power running time on every encoded input.
It does not construct such a machine from the pending source and mapper
programs.
-/

namespace EthInapproximability.CurrentPaper.ETHTailActualContradiction

open EncodedETHTail BitMachine

theorem eth_forbids_actual_source_table_solver (hETH : ETH) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε < δ →
        ∀ (c A d B C D : ℕ) (M : Machine),
          ¬ ∀ input : List Bool,
            M.OutputsWithin input [satAnswer input]
              (C * ⌈(2 : ℝ) ^ (ε * variableCount input)⌉₊ *
                FinalPadding.tableSize
                  (ETHTailGrowth.repetitions c A d)
                  (variableCount input) ^ B *
                (input.length + 1) ^ D) := by
  obtain ⟨δ, hδ, hno⟩ := hETH
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ c A d B C D M hrun
  obtain ⟨K, hbudget⟩ :=
    ETHTailRuntimeAbsorption.solver_budget_global c A d B C D ε δ hε hεδ
  apply hno
  refine ⟨M, K, D, ?_⟩
  intro input
  exact BitMachine.outputsWithin_mono M (hrun input) (hbudget input)

end EthInapproximability.CurrentPaper.ETHTailActualContradiction
