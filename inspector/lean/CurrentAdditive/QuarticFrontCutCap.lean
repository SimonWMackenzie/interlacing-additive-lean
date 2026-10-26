import CurrentAdditive.QuarticOuterCapRun
import CurrentAdditive.QuarticFrontWordCap

/-! The arbitrary-word front bound followed by the physical prefix cutter. -/

namespace Paper2.CurrentAdditive.QuarticFrontCutCap

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly
open Paper2.CurrentAdditive.QuarticFrontLift
open Paper2.CurrentAdditive.QuarticFrontWord
open Paper2.CurrentAdditive.QuarticFrontCapTransfer
open Paper2.CurrentAdditive.QuarticNumericFront

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem physical_front_cut_with_cap (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (hn : 0 < g.vertices) (hm : 0 < g.edges.length)
    (k : ℕ) (raw : List Bool) (Z : ℕ) (hZ : 1 ≤ Z)
    (hP : (BitMachineBankCodec.encode (FullFront.X0 g k raw)).length ≤ Z)
    (hRaw : Raw27.clock g Δ γ k raw ≤ Z) :
    let P := FullFront.X0 g k raw
    ∃ T, ∃ B : FS → List Bool,
      ∃ H : SamplerParameterBank.Stack → List Bool,
      T ≤ timeCoefficient Δ γ * Z +
        QuarticRawPrefixCutter.clock g.vertices g.edges.length
          (Nat.clog 2 g.vertices) Δ γ k raw + 1 ∧
      ((advance (QuarticFrontCutRun.program Δ γ))^[T])
        (⟨some (.inl (startLabel Δ γ)),
          (initialControl,
            (((SamplerParameterJoin.startControl, (false, false)),
              (none, ())), ((), none))),
          Wrap.widen (Lift.a FS) P⟩ : TM2.Cfg (fun _ : K => Bool) _ _) =
        ⟨none,
          ((firstCtl, (none : Option Bool)),
            (((SamplerParameterJoin.finalControl, (false, false)),
              (none, ())), ((), none))),
          QuarticCutOutputCopies.postBank g Δ γ k raw B H⟩ ∧
      H (SamplerParameterJoin.bitCountSlot 0) =
        raw.take (QuarticCutCount.count27 g.vertices g.edges.length
          (Nat.clog 2 g.vertices) Δ γ k) ∧
      B Packet27.scratch = [] := by
  intro P
  obtain ⟨tF, vF, B, htF, hrF, hsB⟩ :=
    QuarticFrontWordCap.physical_word_with_cap g hg Δ γ hγ hΔ hn hm k raw Z hZ hP hRaw
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
    (QuarticCutOutputCopies.postBank g Δ γ k raw B H)
    tF tC hrF (by simpa only [QuarticCutOutputCopies.postBank] using hrC)
  refine ⟨T, B, H, ?_, ?_, hcut, hsB⟩
  · omega
  · simpa only [QuarticFrontCutRun.program] using hr

#print axioms physical_front_cut_with_cap

end
end Paper2.CurrentAdditive.QuarticFrontCutCap
