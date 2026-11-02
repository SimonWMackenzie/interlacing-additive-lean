import CurrentAdditive.QuarticInstallValuesGeneric

namespace Paper2.CurrentAdditive.QuarticNumericFront.Install27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open CurrentAdditive.RandomizedSchedule
open SourceRecursiveNoSampling
open EthInapproximability.CurrentPaper

theorem source_values (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (Δ : ℕ) (γ : ℚ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (hFacts : CountFront.LFacts g.vertices FLnew)
    (hQ : FQnew (.inl 24) = List.replicate
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) true)
    (hRows : FM 13 = List.replicate
      (sourceRows (Nat.clog 2 g.vertices)
        (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) k) true)
    (hCols : FM 10 = List.replicate
      (sourceCols (Nat.clog 2 g.vertices)
        (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) k) true)
    (i : Fin 11) :
    TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM
      (copies i 0) =
      ![List.replicate (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices)) true,
        List.replicate (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2) true,
        List.replicate (SourceProfileParameters.width (Nat.clog 2 g.vertices)) true,
        List.replicate g.vertices true,
        List.replicate (width27 (Nat.clog 2 g.vertices)) true,
        List.replicate (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) true,
        List.replicate (LookupSeed.width (Nat.clog 2 g.vertices)) true,
        List.replicate k true,
        List.replicate (sourceRows (Nat.clog 2 g.vertices)
          (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
          (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
            (Nat.clog 2 g.vertices) γ Δ) k) true,
        List.replicate (sourceCols (Nat.clog 2 g.vertices)
          (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
          (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
            (Nat.clog 2 g.vertices) γ Δ) k) true,
        word] i := by
  obtain ⟨hn, -, -, -, -, -, -, hp, hs, hq2, -, hq1, -, -, -, -, -, -, -, -, -, -⟩ := hFacts
  have hp' : FLnew LProducer.pC =
      List.replicate (LookupSeed.width (Nat.clog 2 g.vertices)) true := by
    rw [LProducer.p_eq]
    exact hp
  have hs' : FLnew LProducer.sC =
      List.replicate (SourceProfileParameters.width (Nat.clog 2 g.vertices)) true := by
    rw [LProducer.s_eq]
    exact hs
  have hq2' : FLnew LProducer.q2C =
      List.replicate (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices)) true := by
    rw [LProducer.q₂_eq]
    exact hq2
  have hq1' : FLnew LProducer.q1C =
      List.replicate (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2) true := by
    rw [LProducer.s_eq]
    exact hq1
  exact values_generic g hg k word FLold FQold FLnew FQnew FT FM
    g.vertices
    (LookupSeed.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2)
    (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
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
    hn hp' hs' hq1' hq2'
    (TM27.width_in_graph_exit g hg FLold FQold FLnew FQnew)
    hQ hRows hCols i

end
end Paper2.CurrentAdditive.QuarticNumericFront.Install27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Install27.source_values
