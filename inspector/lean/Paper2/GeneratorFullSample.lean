import Paper2.GeneratorSource
import Paper2.GeneratorResult
import Paper2.RecursiveSamplingExecution

/-! Exact columns-first complete source sample and same-tape capped transport. -/

namespace Paper2.GeneratorFullSample

open SourceMatrix RecursiveSamplingProgram RecursiveSamplingLaws RecursiveSampling
open RecursiveLabelCodecScratch GeneratorCode GeneratorSource

def sampleCode (n s q₁ q₂ w Q : ℕ) (row₀ col₀ : Code)
    (k mX mY : ℕ) : Code :=
  let c := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
  .append (copies mY c.2) (copies mX c.1)

def sampleCodec {X₀ Y₀ : Type} (n s q₁ q₂ w Q k mX mY : ℕ)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀) :=
  let c := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ (defaultItemCodec n s) k
  prodCodec (piCodec c.2 mY) (piCodec c.1 mX)

theorem sampleCode_exact {X₀ Y₀ : Type} {n s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hs : 4 ≤ s) (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀)
    (row₀ : Program X₀) (col₀ : Program Y₀) (cr₀ cc₀ : Code)
    (hr₀ : meaning cr₀ = Program.map cx₀.encode row₀)
    (hc₀ : meaning cc₀ = Program.map cy₀.encode col₀)
    (k mX mY : ℕ) :
    meaning (sampleCode n s q₁ q₂ w Q cr₀ cc₀ k mX mY) =
      Program.map (sampleCodec n s q₁ q₂ w Q k mX mY cx₀ cy₀).encode
        (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) hs row₀ col₀ k mX mY) := by
  let c := recursiveCodes n s q₁ q₂ w Q cr₀ cc₀ k
  let C := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ (defaultItemCodec n s) k
  let P := programs (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    (finCongr (Fintype.card_fin n)) hs row₀ col₀ k
  obtain ⟨hr, hc⟩ := recursiveCodes_exact (n := n) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hs cx₀ cy₀ row₀ col₀ cr₀ cc₀ hr₀ hc₀ k
  have hy := copies_exact mY C.2 P.2 c.2 hc
  have hx := copies_exact mX C.1 P.1 c.1 hr
  exact pairCode_exact (piCodec C.2 mY).encode (piCodec C.1 mX).encode
    (iid P.2 mY) (iid P.1 mX) (copies mY c.2) (copies mX c.1) hy hx

def mappedState {A B : Type} {M : ℕ} (f : A → B)
    (s : RecursiveSamplingCapped.State A M) : RecursiveSamplingCapped.State B M :=
  ⟨Program.map f s.val, by simpa only [Program.maxAlphabet_map] using s.property⟩

theorem mappedDen {A B : Type} {M : ℕ} (f : A → B)
    (s : RecursiveSamplingCapped.State A M) :
    RecursiveSamplingCapped.stateDenominator (mappedState f s) =
      RecursiveSamplingCapped.stateDenominator s := by
  rcases s with ⟨p, hp⟩
  cases p <;> rfl

def mappedTicket {A B : Type} {M : ℕ} (f : A → B)
    (s : RecursiveSamplingCapped.State A M)
    (i : Fin (RecursiveSamplingCapped.stateDenominator (mappedState f s))) :
    Fin (RecursiveSamplingCapped.stateDenominator s) :=
  Fin.cast (mappedDen f s) i

theorem mappedStep {A B : Type} {M : ℕ} (f : A → B)
    (s : RecursiveSamplingCapped.State A M)
    (i : Fin (RecursiveSamplingCapped.stateDenominator (mappedState f s))) :
    RecursiveSamplingCapped.stateStep (mappedState f s) i =
      mappedState f (RecursiveSamplingCapped.stateStep s (mappedTicket f s i)) := by
  apply Subtype.ext
  rcases s with ⟨p, hp⟩
  cases p <;> rfl

theorem runState_map {A B : Type} {M : ℕ} (f : A → B)
    (Bwidth R : ℕ) (hMB : Nat.clog 2 M ≤ Bwidth)
    (N : ℕ) (s : RecursiveSamplingCapped.State A M)
    (t : CappedSampler.Adaptive.Tape Bwidth R N) :
    RecursiveSamplingCapped.runState Bwidth R hMB N (mappedState f s) t =
      (RecursiveSamplingCapped.runState Bwidth R hMB N s t).map (mappedState f) := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
      change (CappedSampler.runWideBits
          (RecursiveSamplingCapped.stateDenominator (mappedState f s)) Bwidth R
          (RecursiveSamplingCapped.state_width hMB (mappedState f s)) t.1).bind
            (fun i => RecursiveSamplingCapped.runState Bwidth R hMB N
              (RecursiveSamplingCapped.stateStep (mappedState f s) i) t.2) =
        Option.map (mappedState f)
          ((CappedSampler.runWideBits
            (RecursiveSamplingCapped.stateDenominator s) Bwidth R
            (RecursiveSamplingCapped.state_width hMB s) t.1).bind
              (fun i => RecursiveSamplingCapped.runState Bwidth R hMB N
                (RecursiveSamplingCapped.stateStep s i) t.2))
      rw [Option.map_bind]
      apply GeneratorCode.wide_bind_congr (mappedDen f s)
      intro i
      dsimp only [Function.comp_def]
      rw [mappedStep, ih]
      rfl

theorem readResult_map {A B : Type} (f : A → B) (p : Program A) :
    RecursiveSamplingCapped.readResult (Program.map f p) =
      (RecursiveSamplingCapped.readResult p).map f := by
  cases p <;> rfl

theorem run_map {A B : Type} {M : ℕ} (f : A → B)
    (Bwidth R : ℕ) (hMB : Nat.clog 2 M ≤ Bwidth)
    (N : ℕ) (s : RecursiveSamplingCapped.State A M)
    (t : CappedSampler.Adaptive.Tape Bwidth R N) :
    RecursiveSamplingCapped.run Bwidth R hMB N (mappedState f s) t =
      (RecursiveSamplingCapped.run Bwidth R hMB N s t).map f := by
  rw [RecursiveSamplingCapped.run, RecursiveSamplingCapped.run, runState_map]
  cases h : RecursiveSamplingCapped.runState Bwidth R hMB N s t with
  | none => rfl
  | some u => exact readResult_map f u.val

def encodedState {A : Type} {M : ℕ} (c : Code)
    (ca : PrefixCodec A) (p : Program A)
    (hc : meaning c = Program.map ca.encode p)
    (hM : p.maxAlphabet ≤ M) : GeneratorCode.BoundedState M :=
  ⟨GeneratorCode.initial c, by
    rw [GeneratorCode.initial_meaning, hc, Program.maxAlphabet_map]
    exact hM⟩

theorem encodedState_semantic {A : Type} {M : ℕ} (c : Code)
    (ca : PrefixCodec A) (p : Program A)
    (hc : meaning c = Program.map ca.encode p)
    (hM : p.maxAlphabet ≤ M) :
    GeneratorCode.semantic (encodedState c ca p hc hM) =
      mappedState ca.encode (⟨p, hM⟩ : RecursiveSamplingCapped.State A M) := by
  apply Subtype.ext
  exact (GeneratorCode.initial_meaning c).trans hc

theorem encoded_run_exact {A : Type} {M : ℕ} (c : Code)
    (ca : PrefixCodec A) (p : Program A)
    (hc : meaning c = Program.map ca.encode p)
    (hM : p.maxAlphabet ≤ M)
    (Bwidth R : ℕ) (hMB : Nat.clog 2 M ≤ Bwidth)
    (N : ℕ) (t : CappedSampler.Adaptive.Tape Bwidth R N) :
    GeneratorCode.run Bwidth R hMB N (encodedState c ca p hc hM) t =
      (RecursiveSamplingCapped.run Bwidth R hMB N
        (⟨p, hM⟩ : RecursiveSamplingCapped.State A M) t).map ca.encode := by
  rw [GeneratorCode.run_eq, encodedState_semantic, run_map]

def seedSampleCode (n p s q₁ q₂ w Q k mX mY : ℕ) : Code :=
  sampleCode n s q₁ q₂ w Q (copies p .bit) (.ticket p) k mX mY

def scheduledSampleCode (n m L Δ : ℕ) (γ : ℚ) (k mX mY : ℕ) : Code :=
  seedSampleCode n (LookupSeed.width L)
    (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k mX mY

theorem scheduledSampleCode_columns_first (n m L Δ : ℕ) (γ : ℚ)
    (k mX mY : ℕ) :
    scheduledSampleCode n m L Δ γ k mX mY =
      .append (copies mY (scheduledCodes n m L Δ γ k).2)
        (copies mX (scheduledCodes n m L Δ γ k).1) := rfl

theorem seedSampleCode_exact {n p s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s) (k mX mY : ℕ) :
    meaning (seedSampleCode n p s q₁ q₂ w Q k mX mY) =
      Program.map
        (sampleCodec n s q₁ q₂ w Q k mX mY (piCodec boolCodec p) (finCodec p)).encode
        (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
          (finCongr (Fintype.card_fin n)) hs
          (RecursiveSamplingSeed.seedRow p)
          (RecursiveSamplingSeed.seedColumn p hp) k mX mY) := by
  exact sampleCode_exact (n := n) (s := s) (q₁ := q₁) (q₂ := q₂)
    (w := w) (Q := Q) hs (piCodec boolCodec p) (finCodec p)
    (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp)
    (copies p .bit) (.ticket p) (seedRow_exact p) (seedColumn_exact p hp) k mX mY

theorem decode_encoded_option {A B : Type} (ca : PrefixCodec A) (f : A → B)
    (q : Option A) :
    ((q.map ca.encode).bind (fun bits =>
      (ca.decode bits).map (fun z => f z.1))) = q.map f := by
  cases q with
  | none => rfl
  | some a =>
      have h : ca.decode (ca.encode a) = some (a, []) := by
        simpa only [List.append_nil] using ca.roundtrip a []
      simp only [Option.map_some, Option.bind_some, h]

theorem completed_encoded_run {A B : Type} {M : ℕ}
    (c : Code) (ca : PrefixCodec A) (p : Program A)
    (hc : meaning c = Program.map ca.encode p)
    (hM : p.maxAlphabet ≤ M) (f : A → B) (fallback : B)
    (Bwidth R : ℕ) (hMB : Nat.clog 2 M ≤ Bwidth)
    (N : ℕ) (t : CappedSampler.Adaptive.Tape Bwidth R N) :
    CappedSampler.completed
      ((GeneratorCode.run Bwidth R hMB N (encodedState c ca p hc hM) t).bind
        (fun bits => (ca.decode bits).map (fun z => f z.1))) fallback =
    CappedSampler.completed
      (RecursiveSamplingCapped.run Bwidth R hMB N
        (mappedState f (⟨p, hM⟩ : RecursiveSamplingCapped.State A M)) t) fallback := by
  rw [encoded_run_exact]
  rw [decode_encoded_option]
  rw [run_map]

theorem seed_samples_alphabetBound {n p s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ) :
    (samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
      (finCongr (Fintype.card_fin n)) hs
      (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp)
      k mX mY).maxAlphabet ≤
        RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q n p := by
  have h := RecursiveSamplingExecution.program_alphabetBound
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    (finCongr (Fintype.card_fin n)) hs p hp activity ξ k mX mY
  simpa only [RecursiveSamplingExecution.program, tableProgram,
    Program.maxAlphabet_map, Fintype.card_fin] using h

/-- Decode generated columns and rows, evaluate their intersections, and use
the source's all-zero fallback if any capped request aborts. -/
def codedCompleted {n p s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : RecursiveSamplingExecution.Tape (Fin n) s q₁ q₂ w Q p k mX mY) :
    Fin mX → Fin mY → Bool :=
  let P := samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    (finCongr (Fintype.card_fin n)) hs
    (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k mX mY
  let C := sampleCodec n s q₁ q₂ w Q k mX mY (piCodec boolCodec p) (finCodec p)
  let c := seedSampleCode n p s q₁ q₂ w Q k mX mY
  let hc := seedSampleCode_exact (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k mX mY
  let M := RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q (Fintype.card (Fin n)) p
  let N := RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY
  let hM : P.maxAlphabet ≤ M := by
    simpa only [P, M, Fintype.card_fin] using
      seed_samples_alphabetBound (n := n) (p := p) (s := s)
        (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        hp hs activity ξ k mX mY
  CappedSampler.completed
    ((GeneratorCode.run (Nat.clog 2 M) (rejectionAttemptCap N)
      le_rfl N (encodedState c C P hc hM) t).bind
      (fun bits => (C.decode bits).map
        (fun z => RecursiveEntries.table (LookupSeed.matrix p) activity ξ k z.1.2 z.1.1)))
    (fun _ _ => false)

theorem codedCompleted_eq_sourceRun {n p s q₁ q₂ w Q : ℕ}
    [NeZero n] [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]
    (hp : 0 < p) (hs : 4 ≤ s)
    (activity : SourceConstruction.Items s (Fin n) → Fin q₂ → Option (Fin s))
    (ξ : RecursiveEntries.Tails (Fin p → Bool) (Fin p)
      (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q)
    (k mX mY : ℕ)
    (t : RecursiveSamplingExecution.Tape (Fin n) s q₁ q₂ w Q p k mX mY) :
    codedCompleted hp hs activity ξ k mX mY t =
      RecursiveSamplingExecution.run
        (finCongr (Fintype.card_fin n)) hs p hp activity ξ k mX mY t := by
  let P := samples (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    (finCongr (Fintype.card_fin n)) hs
    (RecursiveSamplingSeed.seedRow p) (RecursiveSamplingSeed.seedColumn p hp) k mX mY
  let C := sampleCodec n s q₁ q₂ w Q k mX mY (piCodec boolCodec p) (finCodec p)
  let c := seedSampleCode n p s q₁ q₂ w Q k mX mY
  let hc := seedSampleCode_exact (n := n) (p := p) (s := s)
    (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q) hp hs k mX mY
  let M := RecursiveSamplingExecution.alphabetCap s q₁ q₂ w Q (Fintype.card (Fin n)) p
  let N := RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY
  let hM : P.maxAlphabet ≤ M := by
    simpa only [P, M, Fintype.card_fin] using
      seed_samples_alphabetBound (n := n) (p := p) (s := s)
        (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
        hp hs activity ξ k mX mY
  let f := fun z :
      (Fin mY → RecursiveEntries.Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k) ×
      (Fin mX → RecursiveEntries.Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k) =>
        RecursiveEntries.table (LookupSeed.matrix p) activity ξ k z.2 z.1
  have h := completed_encoded_run c C P hc hM f (fun _ _ => false)
    (Nat.clog 2 M) (rejectionAttemptCap N) le_rfl N t
  simpa only [codedCompleted, RecursiveSamplingExecution.run,
    RecursiveSamplingExecution.state, RecursiveSamplingExecution.program,
    tableProgram, mappedState, Fintype.card_fin] using h

def scheduledCodedCompleted {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (activity : SourceConstruction.Items (SourceProfileParameters.width L) (Fin n) →
      Fin (SourceProfileParameters.outerWidth L) →
        Option (Fin (SourceProfileParameters.width L)))
    (ξ : RecursiveEntries.Tails (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ))
    (k mX mY : ℕ)
    (t : RecursiveSamplingExecution.Tape (Fin n)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
      (LookupSeed.width L) k mX mY) : Fin mX → Fin mY → Bool :=
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
    unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := ⟨by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity⟩
  codedCompleted (by unfold LookupSeed.width; positivity)
    (SourceProfiles.width_ge_four L) activity ξ k mX mY t

def scheduledSourceRun {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (activity : SourceConstruction.Items (SourceProfileParameters.width L) (Fin n) →
      Fin (SourceProfileParameters.outerWidth L) →
        Option (Fin (SourceProfileParameters.width L)))
    (ξ : RecursiveEntries.Tails (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ))
    (k mX mY : ℕ)
    (t : RecursiveSamplingExecution.Tape (Fin n)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
      (LookupSeed.width L) k mX mY) : Fin mX → Fin mY → Bool :=
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
    unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := ⟨by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity⟩
  RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n))
    (SourceProfiles.width_ge_four L) (LookupSeed.width L)
    (by unfold LookupSeed.width; positivity) activity ξ k mX mY t

theorem scheduledCodedCompleted_eq_sourceRun {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ)
    (activity : SourceConstruction.Items (SourceProfileParameters.width L) (Fin n) →
      Fin (SourceProfileParameters.outerWidth L) →
        Option (Fin (SourceProfileParameters.width L)))
    (ξ : RecursiveEntries.Tails (Fin (LookupSeed.width L) → Bool)
      (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ))
    (k mX mY : ℕ)
    (t : RecursiveSamplingExecution.Tape (Fin n)
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
      (LookupSeed.width L) k mX mY) :
    scheduledCodedCompleted L Δ γ activity ξ k mX mY t =
      scheduledSourceRun L Δ γ activity ξ k mX mY t := by
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
    unfold ParameterizedCanonicalSource.restorationWidth RestorationWidthScheduleScratch.width
    positivity⟩
  letI : NeZero (ParameterizedCanonicalSource.coverWidth n m L Δ γ) := ⟨by
    rw [show ParameterizedCanonicalSource.coverWidth n m L Δ γ =
      2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    positivity⟩
  exact codedCompleted_eq_sourceRun
    (by unfold LookupSeed.width; positivity)
    (SourceProfiles.width_ge_four L) activity ξ k mX mY t

#print axioms sampleCode_exact
#print axioms run_map
#print axioms codedCompleted_eq_sourceRun
#print axioms scheduledCodedCompleted_eq_sourceRun

end Paper2.GeneratorFullSample
