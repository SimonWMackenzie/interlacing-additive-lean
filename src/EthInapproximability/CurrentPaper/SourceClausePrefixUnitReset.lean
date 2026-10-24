import EthInapproximability.CurrentPaper.SourceClausePrefixUnitClean

/-!
An actual clear-and-restage handoff from one prefix unit call to another.
The three fixed unary operands are physically pushed after all scratch is
cleared. This is not yet the at-least callback: its two intervening OR gates
have a different local bank and still need a shared physical carrier.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitReset

open Turing BitMachineEncoding
open PrefixUnitClean

abbrev Stack := PrefixUnitRun.Stack

noncomputable def program (w ell : ℕ) :=
  BitMachineRawSequence.program
    (SourceClauseClearExcept.program keep)
    (SourceClauseFixedBatch.program constantTarget (constantSize w ell))
    (SourceClauseFixedBatch.labelAt (constantSize w ell) 0)
    ((), none) ()

noncomputable def cost (S : Stack → List Bool) (w ell : ℕ) : ℕ :=
  PrefixUnitClean.cost S +
    SourceClauseFixedBatch.costPrefix (constantSize w ell) 3 + 2

theorem run (S : Stack → List Bool) (w ell : ℕ) :
    ∃ T ≤ cost S w ell,
      ((advance (program w ell))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseClearExcept.Label.clear 0)),
          (((), none), ()), S⟩) =
        ⟨none, (((), none), ()), stage w ell (clean S)⟩ := by
  have hc := PrefixUnitClean.run S
  have hs := PrefixUnitClean.stage_run w ell (clean S)
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (SourceClauseClearExcept.program keep)
    (SourceClauseFixedBatch.program constantTarget (constantSize w ell))
    (SourceClauseClearExcept.Label.clear 0)
    (SourceClauseFixedBatch.labelAt (constantSize w ell) 0)
    ((), none) ((), none) () ()
    S (clean S) (stage w ell (clean S))
    (PrefixUnitClean.cost S)
    (SourceClauseFixedBatch.costPrefix (constantSize w ell) 3 + 1)
    hc hs
  exact ⟨T, by dsimp [cost]; omega, by simpa only [program] using hr⟩

theorem finished_to_next_initial (n ordinalValue w ell w' ell' : ℕ)
    (sign : Bool) (savedBits outputBits countBits : List Bool) :
    ∃ T ≤ cost (PrefixUnitRun.finished n ordinalValue w ell sign
        savedBits outputBits countBits) w' ell',
      ((advance (program w' ell'))^[T])
        (⟨some (BitMachineRawSequence.leftLabel
          (SourceClauseClearExcept.Label.clear 0)),
          (((), none), ()),
          PrefixUnitRun.finished n ordinalValue w ell sign
            savedBits outputBits countBits⟩) =
        ⟨none, (((), none), ()),
          PrefixUnitRun.initial n ordinalValue w' ell'
            ((EncodedCNF.encodeClause (SourceClauseUnitMachine.unitClause
              (ordinalValue * w + (2 * n + ell)) sign)).reverse ++ savedBits)
            outputBits (true :: countBits)⟩ := by
  obtain ⟨T, hT, hr⟩ := run
    (PrefixUnitRun.finished n ordinalValue w ell sign
      savedBits outputBits countBits) w' ell'
  refine ⟨T, hT, ?_⟩
  rw [hr, PrefixUnitClean.clean_finished_eq_blank,
    PrefixUnitClean.stage_blank_eq_initial]

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixUnitReset
