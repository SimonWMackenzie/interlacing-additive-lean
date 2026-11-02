import CurrentAdditive.QuarticNumericTailSource

namespace Paper2.CurrentAdditive.QuarticNumericFront.Raw27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open CurrentAdditive.RandomizedSchedule

abbrev Stack := Packet27.Stack

def program (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (Packet27.program Δ γ)
    TailSource27.program (leftLabel (leftLabel (.inl ⟨0, by omega⟩)))
    Packet27.initialControl TailSource27.initialControl

def startLabel (Δ : ℕ) (γ : ℚ) :=
  FullFront.labelOfP (program Δ γ)
    (leftLabel (Packet27.startLabel Δ γ))

def initialControl := (Packet27.initialControl, TailSource27.initialControl)

def clock (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (word : List Bool) : ℕ :=
  Packet27.clock g Δ γ + TailSource27.cost g k Δ γ word + 1

theorem run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (word : List Bool) :
    ∃ t ≤ clock g Δ γ k word,
      ∃ FLold : LProducer.LK → List Bool,
      ∃ FQold : QProducer.QK → List Bool,
      ∃ FLnew : LProducer.LK → List Bool,
      ∃ FQnew : QProducer.QK → List Bool,
      ∃ FT : TMFront.TK → List Bool,
      ∃ FM : TMFront.MK → List Bool, ∃ vc,
      ((advance (program Δ γ))^[t])
        (⟨some (startLabel Δ γ), initialControl,
          Packet27.initial (FullFront.X0 g k word)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (Packet27.initialControl, (Tail27.ctlBC, vc)),
          Install27.afterInstall g hg k word
            FLold FQold FLnew FQnew FT FM
            g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
            (SourceProfileParameters.width (Nat.clog 2 g.vertices))
            (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2)
            (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
            (width27 (Nat.clog 2 g.vertices))
            (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
              (Nat.clog 2 g.vertices) γ Δ)
            (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 g.vertices)
              (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
              (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
                (Nat.clog 2 g.vertices) γ Δ) k)
            (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 g.vertices)
              (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
              (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
                (Nat.clog 2 g.vertices) γ Δ) k)⟩ := by
  obtain ⟨tP, htP, FLold, FQold, FLnew, FQnew, vcP,
    hP, hFacts, -, hQ⟩ :=
    Packet27.run g hg Δ γ hγ hΔ hn hm k word
  obtain ⟨tT, htT, vcT, FT, FM, hT⟩ :=
    TailSource27.run g hg k word Δ γ FLold FQold FLnew FQnew hFacts hQ
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (Packet27.program Δ γ) TailSource27.program
    (Packet27.startLabel Δ γ)
    (leftLabel (leftLabel (.inl ⟨0, by omega⟩)))
    Packet27.initialControl vcP TailSource27.initialControl
    (Tail27.ctlBC, vcT)
    (Packet27.initial (FullFront.X0 g k word))
    (Packet27.exitBank g hg k word FLold FQold FLnew FQnew)
    (Install27.afterInstall g hg k word FLold FQold FLnew FQnew FT FM
      g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
      (SourceProfileParameters.width (Nat.clog 2 g.vertices))
      (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2)
      (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
      (width27 (Nat.clog 2 g.vertices))
      (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
        (Nat.clog 2 g.vertices) γ Δ)
      (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 g.vertices)
        (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) k)
      (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 g.vertices)
        (4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 g.vertices))
        (q27 (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) γ Δ) k))
    tP tT hP hT
  refine ⟨t, ?_, FLold, FQold, FLnew, FQnew, FT, FM, vcT, ?_⟩
  · unfold clock
    omega
  · exact hr

end
end Paper2.CurrentAdditive.QuarticNumericFront.Raw27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.Raw27.run
