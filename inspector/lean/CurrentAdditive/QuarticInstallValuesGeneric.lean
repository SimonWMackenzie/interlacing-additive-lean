import CurrentAdditive.QuarticInstallFront

namespace Paper2.CurrentAdditive.QuarticNumericFront.Install27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open EthInapproximability.CurrentPaper

theorem values_generic (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (FT : TMFront.TK → List Bool) (FM : TMFront.MK → List Bool)
    (n p s q₁ q₂ w Q mX mY : ℕ)
    (hn : FLnew LProducer.nC = List.replicate n true)
    (hp : FLnew LProducer.pC = List.replicate p true)
    (hs : FLnew LProducer.sC = List.replicate s true)
    (hq1 : FLnew LProducer.q1C = List.replicate q₁ true)
    (hq2 : FLnew LProducer.q2C = List.replicate q₂ true)
    (hw : Packet27.graphExit g hg FLold FQold FLnew FQnew
      (Graph27.new (LQ27.wc (.inr (.inl 9)))) = List.replicate w true)
    (hQ : FQnew (.inl 24) = List.replicate Q true)
    (hRows : FM 13 = List.replicate mX true)
    (hCols : FM 10 = List.replicate mY true)
    (i : Fin 11) :
    TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM
      (copies i 0) =
      ![List.replicate q₂ true, List.replicate q₁ true,
        List.replicate s true, List.replicate n true,
        List.replicate w true, List.replicate Q true,
        List.replicate p true, List.replicate k true,
        List.replicate mX true, List.replicate mY true, word] i := by
  fin_cases i
  · exact (TM27.lcell_in_graph_exit g hg FLold FQold FLnew FQnew LProducer.q2C).trans hq2
  · exact (TM27.lcell_in_graph_exit g hg FLold FQold FLnew FQnew LProducer.q1C).trans hq1
  · exact (TM27.lcell_in_graph_exit g hg FLold FQold FLnew FQnew LProducer.sC).trans hs
  · exact (TM27.lcell_in_graph_exit g hg FLold FQold FLnew FQnew LProducer.nC).trans hn
  · exact hw
  · exact (TM27.qcell_in_graph_exit g hg FLold FQold FLnew FQnew (.inl 24)).trans hQ
  · exact (TM27.lcell_in_graph_exit g hg FLold FQold FLnew FQnew LProducer.pC).trans hp
  · rfl
  · exact hRows
  · exact hCols
  · rfl

end
end Paper2.CurrentAdditive.QuarticNumericFront.Install27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Install27.values_generic
