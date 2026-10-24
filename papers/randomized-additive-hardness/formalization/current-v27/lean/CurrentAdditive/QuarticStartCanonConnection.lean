import CurrentAdditive.QuarticInstallValues

namespace Paper2.CurrentAdditive.QuarticNumericFront.Install27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open EthInapproximability.CurrentPaper
open SourceProfileParameters SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule
open Paper2.CurrentAdditive.QuarticConstructor

theorem afterInstall_canon27 (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (k : ℕ) (Δ : ℕ) (γ : ℚ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (x : SuccessOrient.Stack) :
    afterInstall g hg k
      ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)
      FLold FQold FLnew FQnew FT FM
      g.vertices
      (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices) - 2)
      (outerWidth (Nat.clog 2 g.vertices))
      (width27 (Nat.clog 2 g.vertices))
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ)
      (sourceRows (Nat.clog 2 g.vertices)
        (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) k)
      (sourceCols (Nat.clog 2 g.vertices)
        (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) k)
      (Packet27.so x) = QuarticLayout.startCanon27 Δ γ g hg hn k t x := by
  rfl

end
end Paper2.CurrentAdditive.QuarticNumericFront.Install27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Install27.afterInstall_canon27
