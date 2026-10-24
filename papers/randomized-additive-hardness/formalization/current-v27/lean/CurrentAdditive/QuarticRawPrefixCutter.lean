import CurrentAdditive.QuarticPreparedCut
import CurrentAdditive.QuarticCutCount

/-! The physical cutter at the literal v27 numeric schedule. -/

namespace Paper2.CurrentAdditive.QuarticRawPrefixCutter

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

noncomputable section

noncomputable local instance : DecidableEq SuccessOrient.Stack := Classical.decEq _

def clock (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) (raw : List Bool) : ℕ :=
  QuarticPreparedCut.clock n (LookupSeed.width L)
    (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (width27 L)
    (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
    (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) raw

theorem run (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) (raw : List Bool) :
    ∃ t ≤ clock n m L Δ γ k raw,
      ∃ H : SamplerParameterBank.Stack → List Bool,
      ((advance QuarticPreparedCut.program)^[t])
        (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
          (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none)),
          SuccessOrient.startBank n (LookupSeed.width L)
            (SourceProfileParameters.width L)
            (SourceProfileParameters.width L - 2)
            (SourceProfileParameters.outerWidth L) (width27 L)
            (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
            (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) raw⟩ :
          TM2.Cfg (fun _ : SuccessOrient.Stack => Bool) _ _) =
        ⟨none,
          (((SamplerParameterJoin.finalControl, (false, false)), (none, ())), ((), none)),
          EthInapproximability.CurrentPaper.BitMachineStackEmbedding.bank
            SuccessOrient.preSlots
            (SuccessOrient.startBank n (LookupSeed.width L)
              (SourceProfileParameters.width L)
              (SourceProfileParameters.width L - 2)
              (SourceProfileParameters.outerWidth L) (width27 L)
              (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
              (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) raw) H⟩ ∧
      H (SamplerParameterJoin.bitCountSlot 0) =
        raw.take (QuarticCutCount.count27 n m L Δ γ k) := by
  simpa only [clock, QuarticCutCount.count27, QuarticPreparedCut.count] using
    (QuarticPreparedCut.run n (LookupSeed.width L)
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L) (width27 L)
      (Q27 (V := Fin n) (E := Fin m) L γ Δ) k
      (rows27 n m L Δ γ k) (cols27 n m L Δ γ k) raw)

theorem scheduled_cut_count {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) :
    QuarticCutCount.count27 n m (Nat.clog 2 n) Δ γ k =
      (select27 hn edge Δ γ k).inputBits :=
  QuarticCutCount.count27_eq_select27_inputBits hn edge Δ γ k hc

#print axioms run
#print axioms scheduled_cut_count

end
end Paper2.CurrentAdditive.QuarticRawPrefixCutter
