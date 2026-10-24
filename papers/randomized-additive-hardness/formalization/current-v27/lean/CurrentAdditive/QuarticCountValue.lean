import CurrentAdditive.QuarticWidthClock
import Paper2.TMFront
import Paper2.MIdent

/-! The generic threshold and sample-dimension machines need no arithmetic
changes: their inputs can be retargeted to the literal quartic vector. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.RandomizedSchedule
open SourceProfileParameters SourceRecursiveNoSampling

def vector27 (n m L Δ : ℕ) (γ : ℚ) : Fin 5 → ℕ :=
  ![LookupSeed.width L, SourceProfileParameters.width L,
    SourceProfileParameters.outerWidth L, width27 L,
    Q27 (V := Fin n) (E := Fin m) L γ Δ]

theorem threshold_value27 (n m L Δ k : ℕ) (γ : ℚ) :
    TMFront.thrVal k (vector27 n m L Δ γ) =
      sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k := by
  have h1 : Nat.clog 2 (LookupSeed.width L) = LookupSeed.exponent L := by
    unfold LookupSeed.width; exact Nat.clog_pow 2 _ (by norm_num)
  have h2 : Nat.clog 2 (SourceProfileParameters.width L) =
      SourceProfileParameters.exponent L := by
    unfold SourceProfileParameters.width; exact Nat.clog_pow 2 _ (by norm_num)
  have h3 : Nat.clog 2 (SourceProfileParameters.outerWidth L) =
      SourceProfileParameters.outerExponent L := by
    unfold SourceProfileParameters.outerWidth; exact Nat.clog_pow 2 _ (by norm_num)
  have h4 : Nat.clog 2 (width27 L) =
      4 * RestorationWidthScheduleScratch.ell L := by
    unfold width27; exact Nat.clog_pow 2 _ (by norm_num)
  have h5 : Nat.clog 2 (Q27 (V := Fin n) (E := Fin m) L γ Δ) =
      q27 (V := Fin n) (E := Fin m) L γ Δ := rfl
  change k * (Nat.clog 2 (Q27 (V := Fin n) (E := Fin m) L γ Δ) +
      (Nat.clog 2 (width27 L) +
        (Nat.clog 2 (SourceProfileParameters.width L) +
          (Nat.clog 2 (SourceProfileParameters.outerWidth L) +
            Nat.clog 2 (SourceProfileParameters.width L))))) +
      (Nat.clog 2 (LookupSeed.width L) + 1) = _
  rw [h1, h2, h3, h4, h5]
  unfold sourceBudget
  ring

theorem sample_values27 (n m L Δ k : ℕ) (γ : ℚ) :
    FullFront.mXV (TMFront.thrVal k (vector27 n m L Δ γ)) k L =
        sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k ∧
    FullFront.mYV (TMFront.thrVal k (vector27 n m L Δ γ)) k =
        sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
          (q27 (V := Fin n) (E := Fin m) L γ Δ) k := by
  rw [threshold_value27]
  constructor
  · rw [MProducer.rows_eq]
    rfl
  · rw [MProducer.cols_eq]
    rfl

/-- The fixed generic threshold/sample machine physically writes the v27
budget and exact two sample dimensions when given the quartic vector. -/
theorem tm_program_writes_dims27 (n m L Δ k : ℕ) (γ : ℚ) :
    let v := vector27 n m L Δ γ
    ∃ T ≤ TMFront.tmBd k v L, ∃ vc,
      ∃ FT : TMFront.TK → List Bool, ∃ FM : TMFront.MK → List Bool,
        ((advance TMFront.tmProg)^[T])
          (⟨some TMFront.tmStart, TMFront.tmCtl, TMFront.TM0 k v L⟩ :
            TM2.Cfg (fun _ : TMFront.JM => Bool) _ _) =
          ⟨none, vc, Sum.elim FT (Sum.elim FM (fun _ => []))⟩ ∧
        FT ThrProducer.thrC = List.replicate
          (sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
            (q27 (V := Fin n) (E := Fin m) L γ Δ) k) true ∧
        FM 10 = List.replicate
          (sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
            (q27 (V := Fin n) (E := Fin m) L γ Δ) k) true ∧
        FM 13 = List.replicate
          (sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
            (q27 (V := Fin n) (E := Fin m) L γ Δ) k) true := by
  intro v
  obtain ⟨T, hT, vc, FT, FM, hr, hTF, hMF⟩ := TMFront.tm_run k v L
  have hbudget : TMFront.thrVal k v =
      sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
        (q27 (V := Fin n) (E := Fin m) L γ Δ) k :=
    threshold_value27 n m L Δ k γ
  have hsample := sample_values27 n m L Δ k γ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hm10, -, -, hm13, -⟩ := hMF
  refine ⟨T, hT, vc, FT, FM, hr, ?_, ?_, ?_⟩
  · have hthr := hTF.1
    change FT ThrProducer.thrC = List.replicate (TMFront.thrVal k v) true at hthr
    rw [hbudget] at hthr
    exact hthr
  · change FM 10 = List.replicate (FullFront.mYV (TMFront.thrVal k v) k) true at hm10
    rw [hsample.2] at hm10
    exact hm10
  · change FM 13 = List.replicate (FullFront.mXV (TMFront.thrVal k v) k L) true at hm13
    rw [hsample.1] at hm13
    exact hm13

end Paper2.CurrentAdditive.QuarticNumericFront

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.threshold_value27
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.sample_values27
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.tm_program_writes_dims27
