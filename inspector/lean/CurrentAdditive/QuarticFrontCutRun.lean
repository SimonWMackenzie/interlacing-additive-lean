import CurrentAdditive.QuarticFrontWord

/-! The arbitrary-word numeric front followed by the literal v27 prepared
prefix cutter, as one fixed finite-stack program. -/

namespace Paper2.CurrentAdditive.QuarticFrontCutRun

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticFrontWord
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticNumericFront
open CurrentAdditive.RandomizedSchedule

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

noncomputable def program (Δ : ℕ) (γ : ℚ) :=
  BitMachineRawSequence.program (QuarticFrontLift.program Δ γ)
    QuarticCutterLift.program
    (.inl (.inl (.inl SamplerParameterJoin.startLabel)))
    QuarticFrontLift.initialControl
    (((SamplerParameterJoin.startControl, (false, false)), (none, ())), ((), none))

theorem physical_front_cut_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (raw : List Bool) :
    let P := FullFront.X0 g k raw
    ∃ T, ∃ B : FS → List Bool,
      ∃ H : SamplerParameterBank.Stack → List Bool,
      T ≤ QuarticFrontLift.clock g Δ γ k P B +
        QuarticRawPrefixCutter.clock g.vertices g.edges.length
          (Nat.clog 2 g.vertices) Δ γ k raw + 1 ∧
      ((advance (program Δ γ))^[T])
        (⟨some (.inl (startLabel Δ γ)),
          (initialControl,
            (((SamplerParameterJoin.startControl, (false, false)),
              (none, ())), ((), none))),
          Wrap.widen (Lift.a FS) P⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none,
          ((firstCtl, (none : Option Bool)),
            (((SamplerParameterJoin.finalControl, (false, false)),
              (none, ())), ((), none))),
          bank (Lift.ιOS FS)
            (afterMaster P B (startWordBank g Δ γ k raw))
            (bank SuccessOrient.preSlots
              (startWordBank g Δ γ k raw) H)⟩ ∧
      H (SamplerParameterJoin.bitCountSlot 0) =
        raw.take (QuarticCutCount.count27 g.vertices g.edges.length
          (Nat.clog 2 g.vertices) Δ γ k) ∧
      B Packet27.scratch = [] := by
  intro P
  obtain ⟨tF, vF, B, htF, hrF, hsB⟩ :=
    physical_word_run g hg Δ γ hγ hΔ hn hm k raw
  have hS : ∀ x : SuccessOrient.Stack,
      afterMaster P B (startWordBank g Δ γ k raw) (Lift.ιOS FS x) =
        startWordBank g Δ γ k raw x := by
    intro x
    change Lift.layoutBank FS P
      (Lift.region FS (startWordBank g Δ γ k raw) ![[], [], []] B)
        (Lift.pos FS (.inl (.inr (.inl x)))) = _
    rw [Lift.layoutBank_inl]
    rfl
  obtain ⟨tC, htC, H, hrC, hcut⟩ :=
    QuarticCutterLift.run g.vertices g.edges.length
      (Nat.clog 2 g.vertices) Δ γ k raw
      (afterMaster P B (startWordBank g Δ γ k raw)) hS
  obtain ⟨T, hT, hr⟩ := BitMachineRawSequence.runs
    (QuarticFrontLift.program Δ γ) QuarticCutterLift.program
    (startLabel Δ γ)
    (.inl (.inl (.inl SamplerParameterJoin.startLabel)))
    initialControl vF
    (((SamplerParameterJoin.startControl, (false, false)),
      (none, ())), ((), none))
    (((SamplerParameterJoin.finalControl, (false, false)),
      (none, ())), ((), none))
    (Wrap.widen (Lift.a FS) P)
    (afterMaster P B (startWordBank g Δ γ k raw))
    (bank (Lift.ιOS FS)
      (afterMaster P B (startWordBank g Δ γ k raw))
      (bank SuccessOrient.preSlots (startWordBank g Δ γ k raw) H))
    tF tC hrF hrC
  refine ⟨T, B, H, ?_, ?_, hcut, hsB⟩
  · change tF ≤ QuarticFrontLift.clock g Δ γ k P B at htF
    omega
  · simpa only [program] using hr

#print axioms physical_front_cut_run

end
end Paper2.CurrentAdditive.QuarticFrontCutRun
