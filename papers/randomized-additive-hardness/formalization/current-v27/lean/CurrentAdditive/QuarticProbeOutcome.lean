import CurrentAdditive.QuarticNoPreloadRun
import CurrentAdditive.QuarticClockN
import CurrentAdditive.QuarticMachineIdent
import Paper2.A3LProbe

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticProbeOutcome

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open Paper2
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource
open Paper2.SourceProfileParameters Paper2.SourceRecursiveNoSampling
open Paper2.A3Assembly.Lift (pos_p pos_q1 pos_q2)
open Paper2.FallbackNoPreloadRun
open Paper2.CurrentAdditive.QuarticNoPreloadRun
open CurrentAdditive.RandomizedSchedule
open Paper2.CurrentAdditive.QuarticConstructor

local instance : DecidableEq SamplerParameterBank.Stack := instDecidableEqSum

def tapeOf27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :=
  SuccessIdent.physTape g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
    (outerWidth (Nat.clog 2 g.vertices))
    (width27 (Nat.clog 2 g.vertices))
    (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ) k
    (sourceRows (Nat.clog 2 g.vertices)
      ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
      ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k)
    (sourceCols (Nat.clog 2 g.vertices)
      ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
      ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k)
    (selTape27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc t)

/-- The actual capped generator run on the physical tape (the `result` of `SuccessOrient.run`
at the canonical schedule). -/
def genOut27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) : Option (List Bool) :=
  GeneratorCode.run
    (SuccessOrient.Bv g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
      (outerWidth (Nat.clog 2 g.vertices))
      (width27 (Nat.clog 2 g.vertices))
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ))
    (SuccessOrient.Rv (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
      (outerWidth (Nat.clog 2 g.vertices))
      (width27 (Nat.clog 2 g.vertices))
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ) k
      (sourceRows (Nat.clog 2 g.vertices)
        ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k)
      (sourceCols (Nat.clog 2 g.vertices)
        ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k))
    (le_refl _)
    (SuccessOrient.Nv (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
      (outerWidth (Nat.clog 2 g.vertices))
      (width27 (Nat.clog 2 g.vertices))
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ) k
      (sourceRows (Nat.clog 2 g.vertices)
        ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k)
      (sourceCols (Nat.clog 2 g.vertices)
        ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
        ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k))
    (GeneratorStateSize.initialBounded
      (SuccessOrient.root g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
        (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
        (outerWidth (Nat.clog 2 g.vertices))
        (width27 (Nat.clog 2 g.vertices))
        (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ) k
        (sourceRows (Nat.clog 2 g.vertices)
          ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k)
        (sourceCols (Nat.clog 2 g.vertices)
          ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k))
      (SamplerFallbackJoin.alphabet_bound g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
        (width (Nat.clog 2 g.vertices)) (width (Nat.clog 2 g.vertices) - 2)
        (outerWidth (Nat.clog 2 g.vertices))
        (width27 (Nat.clog 2 g.vertices))
        (Q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ) k
        (sourceRows (Nat.clog 2 g.vertices)
          ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k)
        (sourceCols (Nat.clog 2 g.vertices)
          ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices)))
          ((q27 (V := Fin g.vertices) (E := Fin g.edges.length) (Nat.clog 2 g.vertices) γ Δ)) k)
        hn (pos_p _) (SourceProfiles.width_ge_four _) (pos_q1 _) (pos_q2 _)
        (by unfold width27; positivity)
        (by rw [CurrentAdditive.RandomizedSchedule.Q27_dyadic]; positivity)))
    (tapeOf27 Δ γ g hg hn k hc t)

theorem tapeOf27_word (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (k : ℕ) (hc : CurrentAdditive.QuarticSchedule.Checks27 (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    (RecursiveSamplingTape.writeTape _ _ _ (tapeOf27 Δ γ g hg hn k hc t)).val =
      (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t := by
  unfold tapeOf27
  rw [SuccessIdent.physTape_word]
  exact selTape27_bits hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc t

/-- The physical sampler's final control bit reports precisely whether its
actual capped generator result is present. -/
theorem outcome_status_isSome27 (mX mY : ℕ) (result : Option (List Bool))
    (d : CodeTableFallback.Config)
    (hout : CodeFallbackAllOutcomes.Outcome mX mY result d) :
    SuccessOrient.status (SamplerParameterJoin.startControl,
      (CodeFallbackFullJoin.prepControl, d.var)) = result.isSome := by
  cases result with
  | none =>
    obtain ⟨a, wc, hd⟩ := hout
    subst hd
    rfl
  | some bytes =>
    obtain ⟨a, hd, -, -⟩ := hout
    subst hd
    rfl

/-- On every selected v27 tape, the no-preload fixed sampler halts, starts
with that exact selected tape word, and leaves the correct outcome bit. -/
theorem selected_probe_run27 (Δ : ℕ) (γ : ℚ) (g : EncodedGraph.Graph)
    (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (tp : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    let n := g.vertices
    let m := g.edges.length
    let L := Nat.clog 2 n
    let p := LookupSeed.width L
    let s := width L
    let q₁ := width L - 2
    let q₂ := outerWidth L
    let w := width27 L
    let Q := Q27 (V := Fin n) (E := Fin m) L γ Δ
    let mX := sourceRows L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let mY := sourceCols L (4 * RestorationWidthScheduleScratch.ell L)
      (q27 (V := Fin n) (E := Fin m) L γ Δ) k
    let B := SamplerFallbackJoin.Bv n p s q₁ q₂ w Q
    let R := SamplerFallbackJoin.Rv p s q₁ q₂ w Q k mX mY
    let word := (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits tp
    ∃ t ≤ 2 ^ (FallbackNoPreloadRun.noPreloadExponent * (k + 1) * L),
      ∃ (d : CodeTableFallback.Config)
        (G : SamplerParameterBank.Private → List Bool),
        d.l = none ∧ G (.inr (.inr 0)) = [] ∧
        ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance
            SamplerFallbackJoin.program)^[t])
          (⟨some SamplerFallbackJoin.startLabel, SamplerFallbackJoin.startControl,
            SamplerParameterJoin.startBank n p s q₁ q₂ w Q k mX mY word⟩ :
            TM2.Cfg (fun _ : SamplerParameterBank.Stack => Bool) _ _) =
          ⟨none, (SamplerParameterJoin.startControl,
              (CodeFallbackFullJoin.prepControl, d.var)),
            Sum.elim (CodeFallbackSourceResult.finalBank n p s q₁ q₂ w Q k mX mY
              word B R d) G⟩ ∧
        SuccessOrient.status (SamplerParameterJoin.startControl,
          (CodeFallbackFullJoin.prepControl, d.var)) =
          (genOut27 Δ γ g hg hn k hc tp).isSome := by
  intro n m L p s q₁ q₂ w Q mX mY B R word
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero q₁ := ⟨by
    dsimp [q₁]
    have h := SourceProfileParameters.width_admissible L
    omega⟩
  letI : NeZero q₂ := ⟨by dsimp [q₂]; unfold outerWidth; positivity⟩
  letI : NeZero w := ⟨by dsimp [w]; unfold width27; positivity⟩
  letI : NeZero Q := ⟨by
    dsimp [Q]
    rw [CurrentAdditive.RandomizedSchedule.Q27_dyadic]
    positivity⟩
  obtain ⟨t, ht, d, G, hd, hG, hr, hout⟩ :=
    QuarticNoPreloadRun.every_tape_halts27 (n := n) (m := m) L Δ γ hc k
      (tapeOf27 Δ γ g hg hn k hc tp)
  have hword := tapeOf27_word Δ γ g hg hn k hc tp
  rw [hword] at hr
  change CodeFallbackAllOutcomes.Outcome mX mY (genOut27 Δ γ g hg hn k hc tp) d at hout
  exact ⟨t, ht, d, G, hd, hG, hr,
    outcome_status_isSome27 mX mY (genOut27 Δ γ g hg hn k hc tp) d hout⟩

#print axioms outcome_status_isSome27
#print axioms selected_probe_run27


end

end Paper2.CurrentAdditive.QuarticProbeOutcome
