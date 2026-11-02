import CurrentAdditive.EdgeDecodeMachine
import Paper2.ScanSelect

namespace CurrentAdditive.LiteralEdgeScanTest

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open LiteralEdgeDecodeDependency (K u)

def program := BitMachineRawSequence.program
  LiteralEdgeDecodeMachine.program Paper2.ScanSelect.prog .peek
    (false,false) ((none : Option Bool),(none : Option Bool))

def finalBank (a r m ig : ℕ) : K → List Bool :=
  ![[], u r, u m, [], [], [], [], [], u (a / r % m), [], [], u (a % r), [],
    [decide (0 < m ∧ a / r / m = ig)]]

theorem selection_final (a r m ig : ℕ) (b : Bool) :
    Paper2.ScanSelect.F (LiteralEdgeDecodeMachine.finalBank a r m ig) b =
      ![[], u r, u m, [], [], [], [], [], u (a / r % m), [], [], u (a % r), [], [b]] := by
  funext k
  fin_cases k <;> rfl

theorem test_run (a r m ig : ℕ) :
    ∃ t ≤ LiteralEdgeDecodeMachine.clock a r m + (a / r / m + ig + 4) + 1,
      ∃ c,
      ((advance program)^[t])
        (⟨some (leftLabel (leftLabel .start)),
          ((false,false),((none : Option Bool),(none : Option Bool))),
          LiteralEdgeDecodeMachine.initialBank a r m ig⟩ :
            TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, c, finalBank a r m ig⟩ := by
  obtain ⟨t₁, ht₁, h₁⟩ := LiteralEdgeDecodeMachine.decode_run a r m ig
  obtain ⟨t₂, ht₂, c₂, h₂⟩ := Paper2.ScanSelect.select_run (a/r/m) ig m
    (LiteralEdgeDecodeMachine.finalBank a r m ig)
    ((none : Option Bool),(none : Option Bool)) rfl rfl rfl
  rw [selection_final] at h₂
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    LiteralEdgeDecodeMachine.program Paper2.ScanSelect.prog
    (leftLabel .start) .peek (false,false) (false,false)
    ((none : Option Bool),(none : Option Bool)) c₂
    (LiteralEdgeDecodeMachine.initialBank a r m ig)
    (LiteralEdgeDecodeMachine.finalBank a r m ig) _ t₁ t₂ h₁ h₂
  exact ⟨t, by omega, _, hr⟩

#print axioms test_run

end

end CurrentAdditive.LiteralEdgeScanTest
