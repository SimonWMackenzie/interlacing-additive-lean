import CurrentAdditive.QuarticNoneIdent
import Paper2.A3NC

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 16384

namespace Paper2.CurrentAdditive.QuarticConstructor

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open Paper2.ThrProducer (TK thrC scrC Xv)
open Paper2.A3Assembly.NoneOut
open SourceProfileParameters SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule

theorem none_run_canonical27 (g : EncodedGraph.Graph) (hg : g.Valid) [NeZero g.vertices]
    (hn : 0 < g.vertices) (Δ : ℕ) (γ : ℚ) (k : ℕ)
    [NeZero (width (Nat.clog 2 g.vertices))] [NeZero (width (Nat.clog 2 g.vertices) - 2)]
    [NeZero (outerWidth (Nat.clog 2 g.vertices))]
    [NeZero (CurrentAdditive.RandomizedSchedule.width27 (Nat.clog 2 g.vertices))]
    [NeZero (CurrentAdditive.RandomizedSchedule.Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ)]
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (tp : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    let n := g.vertices
    let m := g.edges.length
    let edge := CanonicalEdgeTape.graphEdge g hg
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := CurrentAdditive.RandomizedSchedule.width27 L
    let Q := CurrentAdditive.RandomizedSchedule.Q27 (V := Fin n) (E := Fin m) L γ Δ
    let mX := sourceRows L ((4 * RestorationWidthScheduleScratch.ell L))
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L ((4 * RestorationWidthScheduleScratch.ell L))
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let thr := sourceBudget L ((4 * RestorationWidthScheduleScratch.ell L))
      (CurrentAdditive.RandomizedSchedule.q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let word := (select27 hn edge Δ γ k).tapeBits tp
    GeneratorCode.run (SuccessOrient.Bv n p s q₁ q₂ w Q)
        (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (le_refl _)
        (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
        (GeneratorStateSize.initialBounded (SuccessOrient.root n p s q₁ q₂ w Q k mX mY)
          (SamplerFallbackJoin.alphabet_bound n p s q₁ q₂ w Q k mX mY
            (NeZero.pos n) (by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity)
            (SourceProfiles.width_ge_four L) (NeZero.pos q₁) (NeZero.pos q₂) (NeZero.pos w)
            (NeZero.pos Q)))
        (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
          (selTape27 hn edge Δ γ k hc tp)) = none →
    ∃ T ≤ clockN n p s q₁ q₂ w Q k mX mY, ∃ ctl,
      ∃ (d : CodeTableFallback.Config) (G : SamplerParameterBank.Private → List Bool)
        (F : TK → List Bool) (H : HB → List Bool),
        CodeFallbackAllOutcomes.Outcome mX mY none d ∧
        ((advance progN)^[T]) (⟨some (leftLabel (leftLabel (leftLabel (leftLabel
            (.inl ⟨0, by omega⟩))))), ctlN, entryN n p s q₁ q₂ w Q k mX mY word⟩ :
            TM2.Cfg (fun _ : JN => Bool) _ _) =
          ⟨none, ctl, Sum.elim (SuccessOrient.fallbackBank n p s q₁ q₂ w Q k mX mY word
              (SuccessOrient.Bv n p s q₁ q₂ w Q) (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) d G)
            (Sum.elim F H)⟩ ∧
        F thrC = List.replicate thr true ∧ F scrC = [] ∧
        H HeaderA.outH = outputBits27 hn edge Δ γ k tp := by
  intro n m edge L p s q₁ q₂ w Q mX mY thr word hres
  have hp : 0 < p := by show 0 < LookupSeed.width L; unfold LookupSeed.width; positivity
  have hs : 4 ≤ s := SourceProfiles.width_ge_four L
  have hword : (RecursiveSamplingTape.writeTape (SuccessOrient.Bv n p s q₁ q₂ w Q)
      (SuccessOrient.Rv p s q₁ q₂ w Q k mX mY) (SuccessOrient.Nv p s q₁ q₂ w Q k mX mY)
      (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY
        (selTape27 hn edge Δ γ k hc tp))).val = word := by
    rw [SuccessIdent.physTape_word]
    exact selTape27_bits hn edge Δ γ k hc tp
  have hthr : thrV p s q₂ w Q k = thr := QuarticConstructor.threshold27_eq_budget n m Δ γ k
  obtain ⟨hsel, hbits⟩ := none_selected27 hn edge Δ γ k hc tp hres
  have hrun := none_run n p s q₁ q₂ w Q k mX mY (NeZero.pos n) hp hs (NeZero.pos q₁)
    (NeZero.pos q₂) (NeZero.pos w) (NeZero.pos Q)
    (SuccessIdent.physTape n p s q₁ q₂ w Q k mX mY (selTape27 hn edge Δ γ k hc tp)) hres
  simp only [] at hrun
  rw [hword, hthr] at hrun
  obtain ⟨T, hT, ctl, d, G, F, H, hout, hr, hFt, hFz, hH⟩ := hrun
  refine ⟨T, hT, ctl, d, G, F, H, hout, hr, hFt, hFz, ?_⟩
  rw [hH, hbits]
  rfl

end

#print axioms none_run_canonical27

end Paper2.CurrentAdditive.QuarticConstructor
