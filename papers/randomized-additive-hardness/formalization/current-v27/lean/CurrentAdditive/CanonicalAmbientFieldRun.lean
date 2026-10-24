import CurrentAdditive.CanonicalAmbientWidthFull
import CurrentAdditive.FieldUnaryUnifiedRun

/-! The physically initialized first-passing search and packed field-list
printer embedded in the common Yao renderer stack namespace. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FieldSearchCompletion
open CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine
open CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff

def fieldStage (t : ℕ) :=
  fun l => stackStmt (fieldCombinedEmbed t 16)
    (FieldUnaryUnifiedMachine.program l)

theorem physical_ambient_field (t d n : ℕ) (hd : 0 < d)
    (S : Cell t 16 → List Bool)
    (hlocal : ∀ i : FieldUnaryUnifiedMachine.Stack,
      S (fieldCombinedEmbed t 16 i) =
        FieldUnaryUnifiedMachine.initialStack d n i) :
    ∃ c < 2^d,
      CurrentAdditive.FiniteFieldConstructor.TrialSearch.firstPassing d =
        some (CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d c) ∧
      ∃ steps ≤ FieldUnaryUnifiedMachine.prepTime d n +
          55 * 2^d * 2^(d/2) * (d+1)^2 + 2 +
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n,
        let q := ((advance (fieldStage t))^[steps])
          (⟨some (.prep .scanD), FieldUnaryUnifiedMachine.prepEmbed none, S⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _)
        q = stackCfg (fieldCombinedEmbed t 16) S
          (FieldUnaryUnifiedMachine.run steps
            (FieldUnaryUnifiedMachine.initialConfig d n)) ∧
        q.l = none ∧
        q.stk (.field (printerSlots
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
          CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine.packedBits d c n := by
  obtain ⟨c, hc, hfirst, steps, hsteps, hhalt, hout⟩ :=
    FieldUnaryUnifiedMachine.physical_firstPassing_packed_from_unary d n hd
  refine ⟨c, hc, hfirst, steps, hsteps, ?_⟩
  dsimp only
  let q := FieldUnaryUnifiedMachine.initialConfig d n
  have hbank := bank_eq_self (fieldCombinedEmbed t 16) S _
    (by intro i; exact (hlocal i).symm)
  have he := EthInapproximability.CurrentPaper.BitMachineStackRun.run
    (fieldCombinedEmbed t 16) S FieldUnaryUnifiedMachine.program q steps
  have hrun :
      ((advance (fieldStage t))^[steps])
        (⟨some (.prep .scanD), FieldUnaryUnifiedMachine.prepEmbed none, S⟩ :
          TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
      stackCfg (fieldCombinedEmbed t 16) S
        (FieldUnaryUnifiedMachine.run steps
          (FieldUnaryUnifiedMachine.initialConfig d n)) := by
    simpa [fieldStage, q, FieldUnaryUnifiedMachine.initialConfig,
      stackCfg, hbank,
      FieldUnaryUnifiedMachine.run_eq_any
        (inferInstance : DecidableEq FieldUnaryUnifiedMachine.Stack)] using he
  refine ⟨hrun, ?_, ?_⟩
  · rw [hrun]
    simpa [stackCfg] using hhalt
  · rw [hrun]
    have hslot : fieldCombinedEmbed t 16
        (FieldUnaryUnifiedMachine.fieldSlots
          (printerSlots
            CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output)) =
        (.field (printerSlots
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output) : Cell t 16) := rfl
    rw [← hslot]
    change bank (fieldCombinedEmbed t 16) S
      (FieldUnaryUnifiedMachine.run steps
        (FieldUnaryUnifiedMachine.initialConfig d n)).stk
      (fieldCombinedEmbed t 16
        (FieldUnaryUnifiedMachine.fieldSlots
          (printerSlots
            CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output))) = _
    rw [bank_at]
    exact hout

#print axioms physical_ambient_field

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
