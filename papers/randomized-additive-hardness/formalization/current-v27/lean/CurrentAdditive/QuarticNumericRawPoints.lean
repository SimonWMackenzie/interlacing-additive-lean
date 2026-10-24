import CurrentAdditive.QuarticNumericRaw
import CurrentAdditive.QuarticStartCanonConnection

namespace Paper2.CurrentAdditive.QuarticNumericFront.RawPoints27

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open BitMachineRawSequence (leftLabel)
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive.QuarticLayout
open CurrentAdditive.RandomizedSchedule

abbrev Stack := Packet27.Stack

def nCell : Stack := Packet27.graph
  (Graph27.new (LQ27.wc (.inl LProducer.nC)))
def mCell : Stack := Packet27.graph
  (Graph27.new (LQ27.qc (.inl 1)))

theorem run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ)
    (tape : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    let word := (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits tape
    ∃ T ≤ Raw27.clock g Δ γ k word, ∃ vc, ∃ B : Stack → List Bool,
      ((advance (Raw27.program Δ γ))^[T])
        (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl,
          Packet27.initial (FullFront.X0 g k word)⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (Packet27.initialControl, (Tail27.ctlBC, vc)), B⟩ ∧
      (∀ x, B (Packet27.so x) = startCanon27 Δ γ g hg hn k tape x) ∧
      B nCell = List.replicate g.vertices true ∧
      B mCell = List.replicate g.edges.length true ∧
      B Packet27.scratch = [] ∧
      (∀ i, B (Packet27.packet i) = inputBank27 Δ γ g hg hn k tape i) := by
  intro word
  obtain ⟨tP, htP, FLold, FQold, FLnew, FQnew, vcP,
    hP, hFacts, hmNew, hQ⟩ :=
    Packet27.run g hg Δ γ hγ hΔ hn hm k word
  obtain ⟨tT, htT, vcT, FT, FM, hT⟩ :=
    TailSource27.run g hg k word Δ γ FLold FQold FLnew FQnew hFacts hQ
  let B := Install27.afterInstall g hg k word FLold FQold FLnew FQnew FT FM
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
        (Nat.clog 2 g.vertices) γ Δ) k)
  obtain ⟨T, hT', hr⟩ := BitMachineRawSequence.runs
    (Packet27.program Δ γ) TailSource27.program
    (Packet27.startLabel Δ γ)
    (leftLabel (leftLabel (.inl ⟨0, by omega⟩)))
    Packet27.initialControl vcP TailSource27.initialControl
    (Tail27.ctlBC, vcT)
    (Packet27.initial (FullFront.X0 g k word))
    (Packet27.exitBank g hg k word FLold FQold FLnew FQnew)
    B tP tT hP hT
  refine ⟨T, ?_, vcT, B, hr, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Raw27.clock
    omega
  · intro x
    exact Install27.afterInstall_canon27 g hg hn k Δ γ tape
      FLold FQold FLnew FQnew FT FM x
  · obtain ⟨hnNew, -⟩ := hFacts
    exact (TM27.lcell_in_graph_exit g hg FLold FQold FLnew FQnew LProducer.nC).trans hnNew
  · exact (TM27.qcell_in_graph_exit g hg FLold FQold FLnew FQnew (.inl 1)).trans hmNew
  · rfl
  · intro i
    rfl

end
end Paper2.CurrentAdditive.QuarticNumericFront.RawPoints27

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.RawPoints27.run
