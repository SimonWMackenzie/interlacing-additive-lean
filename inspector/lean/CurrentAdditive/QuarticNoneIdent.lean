import CurrentAdditive.QuarticMachineIdent
import Paper2.A3N

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticConstructor

noncomputable section

open EthInapproximability.CurrentPaper
open Paper2.A3Assembly.NoneOut
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
open Paper2.RecursiveLabelCodecScratch Paper2.RecursiveEntries Paper2.ParameterizedCanonicalSource
open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule

theorem none_selected27 {n m : ℕ} [NeZero n] (hn : 0 < n) (edge : Fin m → Bool → Fin n)
    (Δ : ℕ) (γ : ℚ) (k : ℕ)
    [NeZero (width (Nat.clog 2 n))] [NeZero (width (Nat.clog 2 n) - 2)]
    [NeZero (outerWidth (Nat.clog 2 n))]
    [NeZero (width27 (Nat.clog 2 n))]
    [NeZero (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ)
    (tp : (select27 hn edge Δ γ k).Tape) :
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := width27 L
    let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
    let mX := sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let thr := sourceBudget L ((4 * RestorationWidthScheduleScratch.ell L))
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
        (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
        (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
        (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
          (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
            (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
            (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
            (NeZero.pos Q)))
        (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY (selTape27 hn edge Δ γ k hc tp))
        = none →
      selectedInstance27 hn edge Δ γ k tp =
          ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false)⟩ ∧
        outputBits27 hn edge Δ γ k tp =
          EncodedCommunication.encodeInstance
            ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false)⟩ := by
  intro L p s q₁ q₂ w Q mX mY thr hres
  have hp : 0 < p := by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity
  let activity := SourceActiveRank.scanAtCanonical edge
    (by have := SourceProfiles.width_ge_four L; omega)
    (SourceRepetitionScratch.outerWidth_eq_sourceQ0_mul_rep L (Fin m) hc.1)
  let ξ := CanonicalDefaultSource.canonicalDefaultTails L n w Q hn (NeZero.pos w) (NeZero.pos Q)
  have h := run_none (n := n) (p := p) (s := s) (q₁ := q₁) (q₂ := q₂) (w := w) (Q := Q)
    hp (SourceProfiles.width_ge_four L) activity ξ k mX mY
    (selTape27 hn edge Δ γ k hc tp) hres
  have hsel : selectedInstance27 hn edge Δ γ k tp =
      ⟨mX, mY, thr, MatrixMaterialization.rowMajor (fun (_ : Fin mX) (_ : Fin mY) => false)⟩ := by
    rw [selected_eq_scheduled27 hn edge Δ γ k hc tp]
    show EncodedSelectedOutput.instanceOf (YaoMaterialization.tabulate
      (RecursiveSamplingExecution.run (finCongr (Fintype.card_fin n))
        (SourceProfiles.width_ge_four L) p hp activity ξ k mX mY
        (RecursiveSamplingTape.readTape _ _ _ (selTape27 hn edge Δ γ k hc tp)))) thr = _
    rw [h]
    rfl
  refine ⟨hsel, ?_⟩
  unfold outputBits27
  rw [hsel]


end

#print axioms none_selected27

end Paper2.CurrentAdditive.QuarticConstructor
