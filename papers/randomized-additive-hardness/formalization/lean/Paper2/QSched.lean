import Paper2.QMain

/-! Unit 3, segment (1): the cover-width producer at the H-A3 schedule. For the fixed machine
constants `a = γ.num.toNat`, `b = γ.den` and `Δ`, from unary `n`, `m`, `L`, `s = width L`,
`w = restorationWidth L` the producer writes unary `ParameterizedCanonicalSource.coverWidth n m L Δ γ`
into cell 24. -/

set_option maxHeartbeats 4000000

namespace Paper2.QProducer

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

theorem q_run_sched (n m L Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ) (hn : 0 < n) (hm : 0 < m) :
    ∃ t ≤ qBd γ.num.toNat γ.den Δ n m L (SourceProfileParameters.width L)
        (ParameterizedCanonicalSource.restorationWidth L),
      ∃ vc, ∃ F : QK → List Bool,
      ((advance (qProg γ.num.toNat γ.den Δ))^[t])
          (⟨some (qStart γ.num.toNat γ.den Δ), qCtl,
            Q0 n m L (SourceProfileParameters.width L)
              (ParameterizedCanonicalSource.restorationWidth L)⟩ :
            TM2.Cfg (fun _ : QK => Bool) _ _) = ⟨none, vc, F⟩ ∧
      F (.inl 0) = u n ∧ F (.inl 1) = u m ∧ F (.inl 2) = u L ∧
      F (.inl 3) = u (SourceProfileParameters.width L) ∧
      F (.inl 4) = u (ParameterizedCanonicalSource.restorationWidth L) ∧
      F (.inl 24) = u (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := by
  obtain ⟨t, ht, vc, c, F, hrun, h0, h1, h2, h3, h4, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, h24, -⟩ :=
    q_run γ.num.toNat γ.den Δ n m L (SourceProfileParameters.width L)
      (ParameterizedCanonicalSource.restorationWidth L)
  refine ⟨t, ht, vc, F, hrun, h0, h1, h2, h3, h4, ?_⟩
  rw [h24, coverWidth_eq n m L Δ γ hγ hΔ hn hm]
  rfl

end Paper2.QProducer

#print axioms Paper2.QProducer.q_run_sched
