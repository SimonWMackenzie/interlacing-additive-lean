import Paper2.CodeFullRun
import Paper2.GeneratorFullSample
import Mathlib.Tactic

/-! Transport from the actual source `GeneratorCode.run` result to the frozen
fixed physical interpreter, under the source program's draw-count bound. -/

namespace Paper2.CodeFullRunConsumer

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorPositive Paper2.GeneratorStateSize
open Paper2.GeneratorFullSample Paper2.RecursiveSampling
open Paper2.RecursiveSamplingProgram Paper2.RecursiveSamplingSeed

noncomputable section

theorem run_none_iff_capped (M B R N : Nat)
    (hMB : Nat.clog 2 M ≤ B)
    (s : BoundedState M)
    (hN : (semantic s).val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) :
    GeneratorCode.run B R hMB N s t = none ↔
      GeneratorCode.capped B R hMB N s t = none := by
  rw [GeneratorCode.run_eq]
  rw [RecursiveSamplingCapped.run_none_iff B R hMB N (semantic s) hN t]
  rw [← GeneratorCode.capped_semantic B R hMB N s t]
  cases hc : GeneratorCode.capped B R hMB N s t <;> simp

theorem run_some_parts (M B R N : Nat)
    (hMB : Nat.clog 2 M ≤ B)
    (s : BoundedState M)
    (t : CappedSampler.Adaptive.Tape B R N)
    (bytes : List Bool)
    (hr : GeneratorCode.run B R hMB N s t = some bytes) :
    ∃ u, GeneratorCode.capped B R hMB N s t = some u ∧
      GeneratorCode.read u.val = some bytes := by
  unfold GeneratorCode.run at hr
  cases hc : GeneratorCode.capped B R hMB N s t with
  | none => simp [hc] at hr
  | some u =>
      refine ⟨u,rfl,?_⟩
      simpa [hc] using hr

theorem run_some_physical (root : Code) (M B R N : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (t : CappedSampler.Adaptive.Tape B R N)
    (bytes : List Bool)
    (hr : GeneratorCode.run B R hMB N s t = some bytes) :
    ∃ clock ≤ (codeSize root+1) *
      CodeFullRepeatPublic.repeatStepCap root B R + N*(R*B)+2,
      let c := CodeFullPadding.run clock
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N t).val B R)
      c.l = none ∧ CodeFullRun.observed c = some bytes ∧
        c.stk CodeFullPadding.tapeSlot = [] := by
  obtain ⟨u,hu,hread⟩ := run_some_parts M B R N hMB s t bytes hr
  exact CodeFullRun.capped_success_observed root M B R hMB hR N s hp ht
    t u bytes hu hread

theorem run_none_physical (root : Code) (M B R N : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (hN : (semantic s).val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N)
    (zero : List Bool)
    (hr : GeneratorCode.run B R hMB N s t = none) :
    ∃ clock ≤ (codeSize root+1) *
      CodeFullRepeatPublic.repeatStepCap root B R,
      let c := CodeFullPadding.run clock
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N t).val B R)
      c.l = none ∧ CodeFullRun.observed c = none ∧
        CappedSampler.completed (CodeFullRun.observed c) zero = zero := by
  have hf := (run_none_iff_capped M B R N hMB s hN t).mp hr
  exact CodeFullRun.capped_failure_observed root M B R hMB hR N s hp ht
    t hf zero

/-- Outcome-unconditional same-tape interpreter statement. The actual source
`run` result controls the final observation; only successful outcomes drain
the entire tape, while failure retains the first-rejection residual bank. -/
theorem run_physical (root : Code) (M B R N : Nat)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (s : BoundedState M)
    (hp : PositiveState s.val) (ht : Trace root s.val)
    (hN : (semantic s).val.maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N) :
    ∃ clock ≤ (codeSize root+1) *
      CodeFullRepeatPublic.repeatStepCap root B R + N*(R*B)+2,
      let c := CodeFullPadding.run clock
        (CodeFullPadding.start s.val
          (RecursiveSamplingTape.writeTape B R N t).val B R)
      c.l = none ∧
      CodeFullRun.observed c = GeneratorCode.run B R hMB N s t ∧
      (GeneratorCode.run B R hMB N s t ≠ none →
        c.stk CodeFullPadding.tapeSlot = []) := by
  cases hr : GeneratorCode.run B R hMB N s t with
  | none =>
      obtain ⟨clock,hclock,hl,hobs,_⟩ :=
        run_none_physical root M B R N hMB hR s hp ht hN t [] hr
      refine ⟨clock,by omega,hl,?_,?_⟩
      · simpa only [hr] using hobs
      · simp
  | some bytes =>
      obtain ⟨clock,hclock,hl,hobs,htape⟩ :=
        run_some_physical root M B R N hMB hR s hp ht t bytes hr
      refine ⟨clock,hclock,hl,?_,?_⟩
      · simpa only [hr] using hobs
      · intro _
        exact htape

theorem initial_semantic_draws (root : Code) (M : Nat)
    (hM : (meaning root).maxAlphabet ≤ M) :
    (semantic (initialBounded root hM)).val.maxDraws =
      (meaning root).maxDraws := by
  simp [semantic,initialBounded,initial_meaning]

theorem initial_run_none_physical (root : Code) (M B R N : Nat)
    (hM : (meaning root).maxAlphabet ≤ M)
    (hMB : Nat.clog 2 M ≤ B) (hR : 0 < R)
    (hp : Positive root)
    (hN : (meaning root).maxDraws ≤ N)
    (t : CappedSampler.Adaptive.Tape B R N)
    (zero : List Bool)
    (hr : GeneratorCode.run B R hMB N
      (initialBounded root hM) t = none) :
    ∃ clock ≤ (codeSize root+1) *
      CodeFullRepeatPublic.repeatStepCap root B R,
      let c := CodeFullPadding.run clock
        (CodeFullPadding.start (initial root)
          (RecursiveSamplingTape.writeTape B R N t).val B R)
      c.l = none ∧ CodeFullRun.observed c = none ∧
        CappedSampler.completed (CodeFullRun.observed c) zero = zero := by
  have hb : (semantic (initialBounded root hM)).val.maxDraws ≤ N := by
    rw [initial_semantic_draws]
    exact hN
  exact run_none_physical root M B R N hMB hR
    (initialBounded root hM) (positive_initial root hp) Trace.initial
    hb t zero hr

/-- The scheduled source draw cap is adequate for its *same* first-order
seed sample syntax: this is a semantic draw count, not a machine-time claim. -/
theorem seed_sample_code_draw_cap {n p s q₁ q₂ w Q : Nat}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s) (k mX mY : Nat) :
    (meaning (seedSampleCode n p s q₁ q₂ w Q k mX mY)).maxDraws ≤
      RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY := by
  rw [seedSampleCode_exact (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k mX mY]
  simp only [Program.maxDraws_map,RecursiveSamplingExecution.drawCap]
  exact samples_drawBound (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    (finCongr (Fintype.card_fin n)) hs
    (seedRow p) (seedColumn p hp) p 1
    (maxDraws_seedRow_le p)
    (le_of_eq (maxDraws_seedColumn p hp)) k mX mY

theorem seed_sample_code_alphabet_cap {n p s q₁ q₂ w Q : Nat}
    [NeZero n] [NeZero s] [NeZero q₁] [NeZero q₂]
    [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s (Fin n) →
      Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : Nat) :
    (meaning (seedSampleCode n p s q₁ q₂ w Q k mX mY)).maxAlphabet ≤
      RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q n p := by
  rw [seedSampleCode_exact (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k mX mY]
  simpa only [Program.maxAlphabet_map,Fintype.card_fin] using
    (seed_samples_alphabetBound (n := n) (p := p) (s := s)
      (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      hp hs activity ξ k mX mY)

theorem scheduled_sample_code_draw_cap {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat) (k mX mY : Nat) :
    (meaning (scheduledSampleCode n m L Δ γ k mX mY)).maxDraws ≤
      RecursiveSamplingExecution.drawCap
        (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L)
        (ParameterizedCanonicalSource.restorationWidth L)
        (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
        (LookupSeed.width L) k mX mY := by
  letI : NeZero (SourceProfileParameters.width L) := ⟨by
    unfold SourceProfileParameters.width
    positivity⟩
  letI : NeZero (SourceProfileParameters.width L - 2) := ⟨by
    have h := SourceProfileParameters.width_admissible L
    omega⟩
  letI : NeZero (SourceProfileParameters.outerWidth L) := ⟨by
    unfold SourceProfileParameters.outerWidth
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.restorationWidth L) := ⟨by
    unfold ParameterizedCanonicalSource.restorationWidth
      RestorationWidthScheduleScratch.width
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := ⟨by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity⟩
  exact seed_sample_code_draw_cap
    (n := n) (p := LookupSeed.width L)
    (s := SourceProfileParameters.width L)
    (q₁ := SourceProfileParameters.width L - 2)
    (q₂ := SourceProfileParameters.outerWidth L)
    (w := ParameterizedCanonicalSource.restorationWidth L)
    (Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    (by unfold LookupSeed.width; positivity)
    (SourceProfiles.width_ge_four L) k mX mY

theorem scheduled_sample_code_alphabet_cap {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat)
    (activity : SourceConstruction.Items (SourceProfileParameters.width L)
      (Fin n) → Fin (SourceProfileParameters.outerWidth L) →
      Option (Fin (SourceProfileParameters.width L)))
    (ξ : RecursiveEntries.Tails (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ))
    (k mX mY : Nat) :
    (meaning (scheduledSampleCode n m L Δ γ k mX mY)).maxAlphabet ≤
      RecursiveSamplingExecution.alphabetCap
        (SourceProfileParameters.width L)
        (SourceProfileParameters.width L - 2)
        (SourceProfileParameters.outerWidth L)
        (ParameterizedCanonicalSource.restorationWidth L)
        (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
        n (LookupSeed.width L) := by
  letI : NeZero (SourceProfileParameters.width L) := ⟨by
    unfold SourceProfileParameters.width
    positivity⟩
  letI : NeZero (SourceProfileParameters.width L - 2) := ⟨by
    have h := SourceProfileParameters.width_admissible L
    omega⟩
  letI : NeZero (SourceProfileParameters.outerWidth L) := ⟨by
    unfold SourceProfileParameters.outerWidth
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.restorationWidth L) := ⟨by
    unfold ParameterizedCanonicalSource.restorationWidth
      RestorationWidthScheduleScratch.width
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := ⟨by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity⟩
  exact seed_sample_code_alphabet_cap
    (n := n) (p := LookupSeed.width L)
    (s := SourceProfileParameters.width L)
    (q₁ := SourceProfileParameters.width L - 2)
    (q₂ := SourceProfileParameters.outerWidth L)
    (w := ParameterizedCanonicalSource.restorationWidth L)
    (Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    (by unfold LookupSeed.width; positivity)
    (SourceProfiles.width_ge_four L) activity ξ k mX mY

def scheduledM (n m L Δ : Nat) (γ : Rat) : Nat :=
  RecursiveSamplingExecution.alphabetCap
    (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    n (LookupSeed.width L)

def scheduledN (n m L Δ : Nat) (γ : Rat)
    (k mX mY : Nat) : Nat :=
  RecursiveSamplingExecution.drawCap
    (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    (LookupSeed.width L) k mX mY

/-- The public scheduled code, tape, alphabet and draw count instantiate the
outcome-unconditional physical interpreter with no extra source/runtime
assumption. The encoded-table decoder and zero-table writer are later stages. -/
theorem scheduled_run_physical {n m : Nat} [NeZero n]
    (L Δ : Nat) (γ : Rat)
    (activity : SourceConstruction.Items (SourceProfileParameters.width L)
      (Fin n) → Fin (SourceProfileParameters.outerWidth L) →
      Option (Fin (SourceProfileParameters.width L)))
    (ξ : RecursiveEntries.Tails (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L)
      (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ))
    (k mX mY : Nat)
    (t : CappedSampler.Adaptive.Tape
      (Nat.clog 2 (scheduledM n m L Δ γ))
      (Paper2.rejectionAttemptCap (scheduledN n m L Δ γ k mX mY))
      (scheduledN n m L Δ γ k mX mY)) :
    let root := scheduledSampleCode n m L Δ γ k mX mY
    let M := scheduledM n m L Δ γ
    let N := scheduledN n m L Δ γ k mX mY
    let B := Nat.clog 2 M
    let R := Paper2.rejectionAttemptCap N
    let hM := scheduled_sample_code_alphabet_cap L Δ γ activity ξ k mX mY
    let s := initialBounded root hM
    ∃ clock ≤ (codeSize root+1) *
      CodeFullRepeatPublic.repeatStepCap root B R + N*(R*B)+2,
      let c := CodeFullPadding.run clock
        (CodeFullPadding.start (initial root)
          (RecursiveSamplingTape.writeTape B R N t).val B R)
      c.l = none ∧
      CodeFullRun.observed c = GeneratorCode.run B R le_rfl N s t ∧
      (GeneratorCode.run B R le_rfl N s t ≠ none →
        c.stk CodeFullPadding.tapeSlot = []) := by
  let root := scheduledSampleCode n m L Δ γ k mX mY
  let M := scheduledM n m L Δ γ
  let N := scheduledN n m L Δ γ k mX mY
  let B := Nat.clog 2 M
  let R := Paper2.rejectionAttemptCap N
  let hM := scheduled_sample_code_alphabet_cap L Δ γ activity ξ k mX mY
  let s := initialBounded root hM
  have hN : (semantic s).val.maxDraws ≤ N := by
    rw [initial_semantic_draws]
    exact scheduled_sample_code_draw_cap L Δ γ k mX mY
  have hp : PositiveState s.val := by
    exact positive_initial root
      (positive_scheduledSampleCode L Δ γ k mX mY)
  have hR : 0 < R := CodeFullRun.scheduled_attempts_pos N
  exact run_physical root M B R N le_rfl hR s hp Trace.initial hN t

#print axioms run_none_iff_capped
#print axioms run_some_physical
#print axioms run_none_physical
#print axioms run_physical
#print axioms initial_run_none_physical
#print axioms seed_sample_code_draw_cap
#print axioms seed_sample_code_alphabet_cap
#print axioms scheduled_sample_code_draw_cap
#print axioms scheduled_sample_code_alphabet_cap
#print axioms scheduled_run_physical

end
end Paper2.CodeFullRunConsumer
