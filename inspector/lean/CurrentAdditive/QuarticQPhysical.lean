import CurrentAdditive.QuarticQValue
import Paper2.QMain

/-! The existing fixed Q machine, started with the *quartic* unary width,
physically writes the exact v27 Q and has its original charged clock. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront

set_option maxRecDepth 4096

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.RandomizedSchedule
open SourceProfileParameters

theorem q_program_writes_Q27 (n m L Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m) :
    ∃ T ≤ QProducer.qBd γ.num.toNat γ.den Δ n m L (width L) (width27 L),
      ∃ vc, ∃ F : QProducer.QK → List Bool,
        ((advance (QProducer.qProg γ.num.toNat γ.den Δ))^[T])
          (⟨some (QProducer.qStart γ.num.toNat γ.den Δ), QProducer.qCtl,
            QProducer.Q0 n m L (width L) (width27 L)⟩ :
            TM2.Cfg (fun _ : QProducer.QK => Bool) _ _) =
          ⟨none, vc, F⟩ ∧
        F (.inl 1) = List.replicate m true ∧
        F (.inl 24) = List.replicate
          (Q27 (V := Fin n) (E := Fin m) L γ Δ) true := by
  obtain ⟨T, hT, vc, c, F, hr, facts⟩ :=
    QProducer.q_run γ.num.toNat γ.den Δ n m L (width L) (width27 L)
  obtain ⟨-, hm1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h24, -⟩ := facts
  refine ⟨T, hT, vc, F, hr, hm1, ?_⟩
  change F (.inl 24) = List.replicate
    (QProducer.qVal γ.num.toNat γ.den Δ n m L (width L) (width27 L)) true at h24
  rw [qVal_quartic_eq_Q27 n m L Δ γ hγ hΔ hn hm] at h24
  exact h24

end Paper2.CurrentAdditive.QuarticNumericFront

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.q_program_writes_Q27
