import Paper2.RepRun
import Paper2.ParameterizedCanonicalSource

/-! Unit 3, segment (1): identification of the producer's quotient with the scheduled repetition
factor `ParameterizedCanonicalSource.rep L m = outerWidth L / sourceQ0 (Fin (4 width L)) (Fin m)`
(literal definition; `SourceRepetitionScratch.sourceQ0_schedule`), and the zero remainder under the
first admissibility comparison `coordinateAdmissible L (Fin m)` (= `hc.1` of
`CompletePublicScheduleScratch.Checks`). -/

set_option maxRecDepth 16384

namespace Paper2.RepProducer

open Paper2.SourceProfileParameters
open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding

theorem rep_eq (L m : ℕ) :
    ParameterizedCanonicalSource.rep L m = outerWidth L / 2 ^ Nat.clog 2 (12 * width L * m) := by
  unfold ParameterizedCanonicalSource.rep SourceRepetitionScratch.sourceRep
  rw [SourceRepetitionScratch.sourceQ0_schedule, Fintype.card_fin]
  rfl

theorem rem_zero (L m : ℕ) (h : SourceRepetitionScratch.coordinateAdmissible L (Fin m)) :
    outerWidth L % 2 ^ Nat.clog 2 (12 * width L * m) = 0 := by
  have hd := SourceRepetitionScratch.sourceQ0_dvd_outerWidth L (Fin m) h
  rw [SourceRepetitionScratch.sourceQ0_schedule, Fintype.card_fin] at hd
  obtain ⟨c, hc⟩ := hd
  rw [hc]
  exact Nat.mul_mod_right _ _

/-- The producer at the scheduled widths: quotient cell = unary `rep L m`; under the first
admissibility comparison the remainder cell is blank. -/
theorem fin1_sched (L m : ℕ) :
    fin1 (width L) (outerWidth L) m 12 = u (ParameterizedCanonicalSource.rep L m) := by
  rw [rep_eq]; rfl

theorem fin1_11 (s q₂ m : ℕ) : fin1 s q₂ m 11 = u (q₂ % 2 ^ Nat.clog 2 (12 * s * m)) := by
  simp [fin1]

theorem fin1_sched_rem (L m : ℕ) (h : SourceRepetitionScratch.coordinateAdmissible L (Fin m)) :
    fin1 (width L) (outerWidth L) m 11 = [] := by
  rw [fin1_11, rem_zero L m h]; rfl

/-- Segment (1) endpoint: ONE fixed program `repProg` from `u (width L)`, `u (outerWidth L)`,
`u m` (everything else blank) halts with `u (rep L m)` in the quotient cell, every `Fin 13` cell
exact, and (under `coordinateAdmissible L (Fin m)`) a blank remainder cell. -/
theorem rep_run_sched (L m : ℕ) :
    ∃ t ≤ repBd (width L) (outerWidth L) m, ∃ vc,
      ∃ c : EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy.logMachine.Config,
      ((advance repProg)^[t])
          (⟨some repStart, repCtl, R0 (width L) (outerWidth L) m⟩ :
            Turing.TM2.Cfg (fun _ : RK => Bool) _ _) =
        ⟨none, vc, Sum.elim (fin1 (width L) (outerWidth L) m)
          (EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy.afterLog
            (u (12 * width L * m)) c).stk⟩ ∧
      fin1 (width L) (outerWidth L) m 12 = u (ParameterizedCanonicalSource.rep L m) := by
  obtain ⟨t, ht, vc, c, hr, -, -⟩ := rep_run (width L) (outerWidth L) m
  exact ⟨t, ht, vc, c, hr, fin1_sched L m⟩

#print axioms rep_eq
#print axioms rem_zero
#print axioms fin1_sched
#print axioms fin1_sched_rem
#print axioms rep_run_sched

end Paper2.RepProducer
