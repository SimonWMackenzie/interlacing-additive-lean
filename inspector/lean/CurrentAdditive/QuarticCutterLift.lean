import CurrentAdditive.QuarticFrontCapTransfer
import CurrentAdditive.QuarticRawPrefixCutter

/-! A fixed lift of the physical v27 prefix cutter into the master region of
the physical numeric front. The public input packet remains in disjoint cells. -/

namespace Paper2.CurrentAdditive.QuarticCutterLift

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticConstructor

noncomputable section

noncomputable local instance : DecidableEq SuccessOrient.Stack := Classical.decEq _

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

noncomputable def program :=
  Lift.liftP (Lift.ιOS FS) QuarticPreparedCut.program

theorem run (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) (raw : List Bool)
    (S : K → List Bool)
    (hS : ∀ x : SuccessOrient.Stack, S (Lift.ιOS FS x) =
      SuccessOrient.startBank n (LookupSeed.width L)
        (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L)
        (CurrentAdditive.RandomizedSchedule.width27 L)
        (CurrentAdditive.RandomizedSchedule.Q27
          (V := Fin n) (E := Fin m) L γ Δ) k
        (rows27 n m L Δ γ k)
        (cols27 n m L Δ γ k) raw x) :
    ∃ t ≤ QuarticRawPrefixCutter.clock n m L Δ γ k raw,
      ∃ H : SamplerParameterBank.Stack → List Bool,
      ((advance program)^[t])
        (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
          (((SamplerParameterJoin.startControl, (false, false)), (none, ())),
            ((), none)), S⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none,
          (((SamplerParameterJoin.finalControl, (false, false)), (none, ())),
            ((), none)),
          bank (Lift.ιOS FS) S
            (bank SuccessOrient.preSlots
              (SuccessOrient.startBank n (LookupSeed.width L)
                (SourceProfileParameters.width L)
                (SourceProfileParameters.width L - 2)
                (SourceProfileParameters.outerWidth L)
                (CurrentAdditive.RandomizedSchedule.width27 L)
                (CurrentAdditive.RandomizedSchedule.Q27
                  (V := Fin n) (E := Fin m) L γ Δ) k
                (rows27 n m L Δ γ k)
                (cols27 n m L Δ γ k) raw) H)⟩ ∧
      H (SamplerParameterJoin.bitCountSlot 0) =
        raw.take (QuarticCutCount.count27 n m L Δ γ k) := by
  obtain ⟨t, ht, H, hr, hcut⟩ :=
    QuarticRawPrefixCutter.run n m L Δ γ k raw
  have hrun := BitMachineStackRun.run (Lift.ιOS FS) S
    QuarticPreparedCut.program
    (⟨some (.inl (.inl (.inl SamplerParameterJoin.startLabel))),
      (((SamplerParameterJoin.startControl, (false, false)), (none, ())),
        ((), none)),
      SuccessOrient.startBank n (LookupSeed.width L)
        (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L)
        (CurrentAdditive.RandomizedSchedule.width27 L)
        (CurrentAdditive.RandomizedSchedule.Q27
          (V := Fin n) (E := Fin m) L γ Δ) k
        (rows27 n m L Δ γ k)
        (cols27 n m L Δ γ k) raw⟩ :
      TM2.Cfg (fun _ : SuccessOrient.Stack => Bool) _ _) t
  rw [hr] at hrun
  have hstart : bank (Lift.ιOS FS) S
      (SuccessOrient.startBank n (LookupSeed.width L)
        (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L)
        (CurrentAdditive.RandomizedSchedule.width27 L)
        (CurrentAdditive.RandomizedSchedule.Q27
          (V := Fin n) (E := Fin m) L γ Δ) k
        (rows27 n m L Δ γ k)
        (cols27 n m L Δ γ k) raw) = S := by
    apply bank_eq_self
    intro x
    exact (hS x).symm
  refine ⟨t, ht, H, ?_, hcut⟩
  simpa only [program, stackCfg, hstart] using hrun

#print axioms run

end
end Paper2.CurrentAdditive.QuarticCutterLift
