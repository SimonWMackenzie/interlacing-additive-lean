import CurrentAdditive.QuarticNumericTailSource

/-! The charged physical numeric tail has only a linear outer overhead once its
public values, dimensions, tape, and threshold-machine time share a cap. -/

namespace Paper2.CurrentAdditive.QuarticTailClockArithmetic

open EthInapproximability.CurrentPaper
open Paper2.CurrentAdditive.QuarticNumericFront
open SourceProfileParameters SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule

noncomputable section

theorem tail_cost_linear (g : EncodedGraph.Graph) (k Δ : ℕ) (γ : ℚ)
    (word : List Bool) (Z : ℕ) (hZ : 1 ≤ Z)
    (hL : Nat.clog 2 g.vertices ≤ Z)
    (hn : g.vertices ≤ Z)
    (hk : k ≤ Z)
    (hp : LookupSeed.width (Nat.clog 2 g.vertices) ≤ Z)
    (hs : width (Nat.clog 2 g.vertices) ≤ Z)
    (hq₂ : outerWidth (Nat.clog 2 g.vertices) ≤ Z)
    (hw : width27 (Nat.clog 2 g.vertices) ≤ Z)
    (hQ : Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ ≤ Z)
    (hrow : sourceRows (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k ≤ Z)
    (hcol : sourceCols (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k ≤ Z)
    (hword : word.length ≤ Z)
    (htm : TMFront.tmBd k (vector27 g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ) (Nat.clog 2 g.vertices) ≤ Z) :
    TailSource27.cost g k Δ γ word ≤ 500 * Z := by
  unfold TailSource27.cost
  omega

#print axioms tail_cost_linear

end
end Paper2.CurrentAdditive.QuarticTailClockArithmetic
