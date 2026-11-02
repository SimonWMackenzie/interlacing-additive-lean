import CurrentAdditive.QuarticEncodedOutput
import Paper2.SuccessIdent
import Paper2.ThrJoin

/-! Semantic and threshold identities for the generic physical success
machine, instantiated at the literal v27 schedule. -/

namespace Paper2.CurrentAdditive.QuarticConstructor

open SourceProfileParameters SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule
open EthInapproximability.CurrentPaper
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
  Paper2.GeneratorFullSample Paper2.RecursiveSamplingProgram
  Paper2.RecursiveSamplingLaws Paper2.RecursiveLabelCodecScratch
  Paper2.RecursiveSampling Paper2.RecursiveRequestCodeShape
open Paper2.RecursiveEntries Paper2.RecursiveSamplingExecution

theorem threshold27_eq_budget (n m Δ : ℕ) (γ : ℚ) (k : ℕ) :
    let L := Nat.clog 2 n
    k * Paper2.ThrProducer.Xv ![LookupSeed.width L, width L,
        outerWidth L, width27 L,
        Q27 (V := Fin n) (E := Fin m) L γ Δ] +
      (Nat.clog 2 (LookupSeed.width L) + 1) =
    sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k := by
  intro L
  have h1 : Nat.clog 2 (LookupSeed.width L) = LookupSeed.exponent L := by
    unfold LookupSeed.width
    exact Nat.clog_pow 2 _ (by norm_num)
  have h2 : Nat.clog 2 (width L) = exponent L := by
    unfold width
    exact Nat.clog_pow 2 _ (by norm_num)
  have h3 : Nat.clog 2 (outerWidth L) = outerExponent L := by
    unfold outerWidth
    exact Nat.clog_pow 2 _ (by norm_num)
  have h4 : Nat.clog 2 (width27 L) = 4 * RestorationWidthScheduleScratch.ell L := by
    unfold width27
    exact Nat.clog_pow 2 _ (by norm_num)
  have h5 : Nat.clog 2 (Q27 (V := Fin n) (E := Fin m) L γ Δ) =
      q27 (V := Fin n) (E := Fin m) L γ Δ := rfl
  change k * (Nat.clog 2 (Q27 (V := Fin n) (E := Fin m) L γ Δ) +
      (Nat.clog 2 (width27 L) +
        (Nat.clog 2 (width L) +
          (Nat.clog 2 (outerWidth L) + Nat.clog 2 (width L))))) +
      (Nat.clog 2 (LookupSeed.width L) + 1) = _
  rw [h1, h2, h3, h4, h5]
  unfold sourceBudget
  ring

/-- Transport only the selected tape, without changing its bit list. -/
def selTape27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select27 hn edge Δ γ k).Tape) :
    (scheduledOutput27 hn edge Δ γ k hc).Tape :=
  cast (congrArg TotalFiniteConstructorScratch.SelectedOutput.Tape
    (select27_good hn edge Δ γ k hc)) tp

theorem selTape27_bits {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select27 hn edge Δ γ k).Tape) :
    (selTape27 hn edge Δ γ k hc tp).val =
      (select27 hn edge Δ γ k).tapeBits tp := by
  have key : ∀ (o : TotalFiniteConstructorScratch.SelectedOutput)
      (h : o = scheduledOutput27 hn edge Δ γ k hc) (t : o.Tape),
      (cast (congrArg TotalFiniteConstructorScratch.SelectedOutput.Tape h) t).val =
        o.tapeBits t := by
    intro o h t
    subst h
    rfl
  exact key _ (select27_good hn edge Δ γ k hc) tp

theorem selected_eq_scheduled27 {n m : ℕ} (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select27 hn edge Δ γ k).Tape) :
    selectedInstance27 hn edge Δ γ k tp =
      EncodedSelectedOutput.instanceOf
        ((scheduledOutput27 hn edge Δ γ k hc).table
          (selTape27 hn edge Δ γ k hc tp))
        (scheduledOutput27 hn edge Δ γ k hc).budget := by
  exact Paper2.SuccessIdent.instance_transport _ _
    (select27_good hn edge Δ γ k hc) tp

/-- If the generic physical sampler returns the encoded selected rows and
columns, its v27 selected instance is exactly the table it printed. This
does not assume that a successful run occurs. -/
theorem success_selected27 {n m : ℕ} [NeZero n] (hn : 0 < n)
    (edge : Fin m → Bool → Fin n) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    [NeZero (width (Nat.clog 2 n))]
    [NeZero (width (Nat.clog 2 n) - 2)]
    [NeZero (outerWidth (Nat.clog 2 n))]
    [NeZero (width27 (Nat.clog 2 n))]
    [NeZero (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select27 hn edge Δ γ k).Tape) (bytes : List Bool) :
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := width27 L
    let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
    let mX := rows27 n m L Δ γ k
    let mY := cols27 n m L Δ γ k
    let thr := sourceBudget L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let activity := SourceActiveRank.scanAtCanonical edge
      (by have := SourceProfiles.width_ge_four L; omega)
      (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1)
    let ξ := CanonicalDefaultSource.canonicalDefaultTails L n w Q hn
      (NeZero.pos w) (NeZero.pos Q)
    ∀ (_hres : GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
        (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
        (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
        (GeneratorStateSize.initialBounded
          (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
          (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
            (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
            (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂)
            (NeZero.pos w) (NeZero.pos Q)))
        (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
          (selTape27 hn edge Δ γ k hc tp)) = some bytes)
      (ys : Fin mY → Column (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k)
      (xs : Fin mX → Row (Fin p → Bool) (Fin p)
        (SourceConstruction.Items s (Fin n)) s q₁ q₂ w Q k),
      bytes =
        (List.ofFn (fun j =>
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).2.encode (ys j))).flatten ++
        (List.ofFn (fun i =>
          (defaultCarrierCodecs n p s q₁ q₂ w Q k).1.encode (xs i))).flatten →
      let f : Fin mX → Fin mY → Bool := fun i j =>
        RecursiveEntries.matrix (LookupSeed.matrix p) activity ξ k (xs i) (ys j)
      selectedInstance27 hn edge Δ γ k tp =
          ⟨mX, mY, thr, MatrixMaterialization.rowMajor f⟩ ∧
        outputBits27 hn edge Δ γ k tp =
          EncodedCommunication.natField mX ++ EncodedCommunication.natField mY ++
            EncodedCommunication.natField thr ++ MatrixMaterialization.rowMajor f := by
  intro L p s q₁ q₂ w Q mX mY thr activity ξ hres ys xs hbytes f
  have hp : 0 < p := by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity
  have hrun := Paper2.SuccessIdent.run_success
    (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp (SourceProfiles.width_ge_four L) activity ξ k mX mY
    (selTape27 hn edge Δ γ k hc tp) bytes hres ys xs hbytes
  have hsel : selectedInstance27 hn edge Δ γ k tp =
      ⟨mX, mY, thr, MatrixMaterialization.rowMajor f⟩ := by
    rw [selected_eq_scheduled27 hn edge Δ γ k hc tp]
    show EncodedSelectedOutput.instanceOf
      (YaoMaterialization.tabulate
        (RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n))
          (SourceProfiles.width_ge_four L) p hp activity ξ k mX mY
          (RecursiveSamplingTape.readTape _ _ _
            (selTape27 hn edge Δ γ k hc tp)))) thr = _
    rw [hrun]
    rfl
  refine ⟨hsel, ?_⟩
  unfold outputBits27
  rw [hsel]
  rfl

#print axioms threshold27_eq_budget
#print axioms selected_eq_scheduled27
#print axioms selTape27_bits
#print axioms success_selected27

end Paper2.CurrentAdditive.QuarticConstructor
