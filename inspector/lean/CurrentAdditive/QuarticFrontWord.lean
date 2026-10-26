import CurrentAdditive.QuarticCutterLift

/-! The same fixed v27 numeric front on an arbitrary raw prefix.  The public
counts are calculated from the graph, while the raw prefix is retained in the
SuccessOrient master bank for the subsequent physical cutter. -/

namespace Paper2.CurrentAdditive.QuarticFrontWord

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticNumericFront
open Paper2.CurrentAdditive.QuarticConstructor
open CurrentAdditive.RandomizedSchedule

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

def startWordBank (g : EncodedGraph.Graph) (Δ : ℕ) (γ : ℚ)
    (k : ℕ) (raw : List Bool) : SuccessOrient.Stack → List Bool :=
  SuccessOrient.startBank g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2)
    (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
    (width27 (Nat.clog 2 g.vertices))
    (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ) k
    (rows27 g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ k)
    (cols27 g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ k) raw

theorem raw_lift_word (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (raw : List Bool) :
    let P := FullFront.X0 g k raw
    ∃ T ≤ Raw27.clock g Δ γ k raw, ∃ vc, ∃ B : FS → List Bool,
      ((advance (rawProg Δ γ))^[T])
        (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl, loaded P⟩ :
          TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, (Packet27.initialControl, (Tail27.ctlBC, vc)), afterRaw P B⟩ ∧
      (∀ x, B (Packet27.so x) = startWordBank g Δ γ k raw x) ∧
      B Packet27.scratch = [] := by
  intro P
  obtain ⟨T, hT, FLold, FQold, FLnew, FQnew, FT, FM, vc, hr⟩ :=
    Raw27.run g hg Δ γ hγ hΔ hn hm k raw
  let B := Install27.afterInstall g hg k raw FLold FQold FLnew FQnew FT FM
    g.vertices (LookupSeed.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.width (Nat.clog 2 g.vertices))
    (SourceProfileParameters.width (Nat.clog 2 g.vertices) - 2)
    (SourceProfileParameters.outerWidth (Nat.clog 2 g.vertices))
    (width27 (Nat.clog 2 g.vertices))
    (Q27 (V := Fin g.vertices) (E := Fin g.edges.length)
      (Nat.clog 2 g.vertices) γ Δ)
    (rows27 g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ k)
    (cols27 g.vertices g.edges.length (Nat.clog 2 g.vertices) Δ γ k)
  have hLift := BitMachineStackRun.run (Lift.ιFS FS) (loaded P)
    (Raw27.program Δ γ)
    (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl,
      Packet27.initial (FullFront.X0 g k raw)⟩ :
      TM2.Cfg (fun _ : FS => Bool) _ _) T
  change ((advance (Raw27.program Δ γ))^[T])
    (⟨some (Raw27.startLabel Δ γ), Raw27.initialControl,
      Packet27.initial P⟩ : TM2.Cfg (fun _ : FS => Bool) _ _) =
    ⟨none, (Packet27.initialControl, (Tail27.ctlBC, vc)), B⟩ at hr
  rw [hr] at hLift
  have hstart : bank (Lift.ιFS FS) (loaded P) (Packet27.initial P) =
      loaded P := by
    apply bank_eq_self
    intro x
    exact (loaded_raw P x).symm
  refine ⟨T, hT, vc, B, ?_, ?_, ?_⟩
  · simpa only [rawProg, stackCfg, hstart, after_raw_bank] using hLift
  · intro x
    rfl
  · rfl

theorem physical_word_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (raw : List Bool) :
    let P := FullFront.X0 g k raw
    ∃ T, ∃ v, ∃ B : FS → List Bool,
      T ≤ clock g Δ γ k P B ∧
      ((advance (QuarticFrontLift.program Δ γ))^[T])
        (⟨some (startLabel Δ γ), initialControl,
          Wrap.widen (Lift.a FS) P⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none, v, afterMaster P B (startWordBank g Δ γ k raw)⟩ ∧
      B Packet27.scratch = [] := by
  intro P
  obtain ⟨tP, htP, vP, hrP⟩ := packet_copy_run P
  rw [packet_loaded P] at hrP
  obtain ⟨tR, htR, vR, B, hrR, hmaster, hsB⟩ :=
    raw_lift_word g hg Δ γ hγ hΔ hn hm k raw
  obtain ⟨tS, htS, vS, hrS⟩ := so_copy_run P B hsB
  rw [so_done_layout P B _ hmaster] at hrS
  obtain ⟨tPR, htPR, hrPR⟩ := BitMachineRawSequence.runs
    (CopyAll.prog packetCopies) (rawProg Δ γ)
    (.inl ⟨0, by omega⟩) (Raw27.startLabel Δ γ)
    (none : Option Bool) vP Raw27.initialControl
    (Packet27.initialControl, (Tail27.ctlBC, vR))
    (Wrap.widen (Lift.a FS) P) (loaded P) (afterRaw P B)
    tP tR hrP hrR
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (firstProg Δ γ) (CopyAll.prog soCopies)
    (BitMachineRawSequence.leftLabel (.inl ⟨0, by omega⟩ : CopyAll.Lab 3))
    (.inl ⟨0, by omega⟩)
    firstCtl ((none : Option Bool), (Packet27.initialControl, (Tail27.ctlBC, vR)))
    (none : Option Bool) vS
    (Wrap.widen (Lift.a FS) P) (afterRaw P B)
    (afterMaster P B (startWordBank g Δ γ k raw))
    tPR tS hrPR hrS
  refine ⟨T, (firstCtl, vS), B, ?_, ?_, hsB⟩
  · change tR ≤ Raw27.clock g Δ γ k (P 2) at htR
    unfold clock copyPacketClock copyMasterClock at *
    omega
  · simpa only [QuarticFrontLift.program, startLabel,
      FullFront.labelOfP, initialControl] using hr

#print axioms raw_lift_word
#print axioms physical_word_run

end
end Paper2.CurrentAdditive.QuarticFrontWord
