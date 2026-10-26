import CurrentAdditive.QuarticNumericTail
import CurrentAdditive.QuarticStartCanonConnection

namespace Paper2.CurrentAdditive.QuarticNumericFront.TailSource27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open SourceProfileParameters SourceRecursiveNoSampling
open CurrentAdditive.RandomizedSchedule

abbrev Stack := Packet27.Stack

def program := BitMachineRawSequence.program Tail27.progBC
  (CopyAll.prog Install27.copies) (.inl ⟨0, by omega⟩)
  Tail27.ctlBC (none : Option Bool)
def initialControl := (Tail27.ctlBC, (none : Option Bool))

def cost (g : EncodedGraph.Graph) (k Δ : ℕ) (γ : ℚ)
    (word : List Bool) : ℕ :=
  (7 * (2 * (k + LookupSeed.width (Nat.clog 2 g.vertices) +
    width (Nat.clog 2 g.vertices) + outerWidth (Nat.clog 2 g.vertices) +
    width27 (Nat.clog 2 g.vertices) +
    Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ + Nat.clog 2 g.vertices) + 3) + 1) +
  TMFront.tmBd k (vector27 g.vertices g.edges.length
    (Nat.clog 2 g.vertices) Δ γ) (Nat.clog 2 g.vertices) + 1 +
  (11 * (2 * (outerWidth (Nat.clog 2 g.vertices) +
    (width (Nat.clog 2 g.vertices) - 2) + width (Nat.clog 2 g.vertices) +
    g.vertices + width27 (Nat.clog 2 g.vertices) +
    Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ +
    LookupSeed.width (Nat.clog 2 g.vertices) + k +
    sourceRows (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k +
    sourceCols (Nat.clog 2 g.vertices)
      (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
      (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) k + word.length) + 3) + 1) + 1

theorem run (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : ℕ) (word : List Bool) (Δ : ℕ) (γ : ℚ)
    (FLold : LProducer.LK → List Bool) (FQold : QProducer.QK → List Bool)
    (FLnew : LProducer.LK → List Bool) (FQnew : QProducer.QK → List Bool)
    (hFacts : CountFront.LFacts g.vertices FLnew)
    (hQ : FQnew (.inl 24) = List.replicate
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ) true) :
    ∃ t ≤ cost g k Δ γ word,
      ∃ vc, ∃ FT : TMFront.TK → List Bool,
      ∃ FM : TMFront.MK → List Bool,
      ((advance program)^[t])
        (⟨some (leftLabel (leftLabel (.inl ⟨0, by omega⟩))), initialControl,
          Packet27.exitBank g hg k word FLold FQold FLnew FQnew⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (Tail27.ctlBC, vc),
          Install27.afterInstall g hg k word FLold FQold FLnew FQnew FT FM
            g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
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
                (Nat.clog 2 g.vertices) γ Δ) k)⟩ := by
  have hvB := TM27.source_values g hg k word Δ γ
    FLold FQold FLnew FQnew hFacts hQ
  obtain ⟨tBC, htBC, vcBC, FT, FM, hBC, -, hMF⟩ :=
    Tail27.runBC g hg k word
      (LookupSeed.width (Nat.clog 2 g.vertices))
      (width (Nat.clog 2 g.vertices))
      (outerWidth (Nat.clog 2 g.vertices))
      (width27 (Nat.clog 2 g.vertices))
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ)
      (Nat.clog 2 g.vertices)
      FLold FQold FLnew FQnew hvB
  have hDims := TM27.source_dims_of_MFacts
    g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ k γ FM hMF
  have hvC := Install27.source_values g hg k word Δ γ
    FLold FQold FLnew FQnew FT FM hFacts hQ hDims.2 hDims.1
  obtain ⟨tC, htC, vcC, hC⟩ := Install27.runCopies g hg k word
    FLold FQold FLnew FQnew FT FM
    g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
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
        (Nat.clog 2 g.vertices) γ Δ) k) hvC
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    Tail27.progBC (CopyAll.prog Install27.copies)
    (leftLabel (.inl ⟨0, by omega⟩)) (.inl ⟨0, by omega⟩)
    Tail27.ctlBC (Tail27.ctlBC.1, vcBC)
    (none : Option Bool) vcC
    (Packet27.exitBank g hg k word FLold FQold FLnew FQnew)
    (TM27.afterTM g hg k word FLold FQold FLnew FQnew FT FM)
    (Install27.afterInstall g hg k word FLold FQold FLnew FQnew FT FM
      g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
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
          (Nat.clog 2 g.vertices) γ Δ) k))
    tBC tC hBC hC
  refine ⟨t, ?_, vcC, FT, FM, ?_⟩
  · unfold cost
    simp only [vector27] at htBC ⊢
    omega
  · exact hrun

end
end Paper2.CurrentAdditive.QuarticNumericFront.TailSource27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.TailSource27.run
