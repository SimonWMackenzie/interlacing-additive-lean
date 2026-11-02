import CurrentAdditive.QuarticLayout
import Paper2.FullSched
import Paper2.FrontRun

/-! The v27 selected tape is exactly the third cell expected by the existing
physical front.  This file records the run that can genuinely be reused, with
its actual (older) numeric output kept explicit. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.CurrentAdditive.QuarticConstructor
open Paper2.CurrentAdditive.QuarticDispatchSpec
open Paper2.CurrentAdditive
open CurrentAdditive.RandomizedSchedule
open Paper2.A3Assembly

theorem selected_packet_eq_X0 (Δ : ℕ) (γ : ℚ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    inputBank27 Δ γ g hg hn k t =
      FullFront.X0 g k
        ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t) := rfl

/-- A fixed existing program really runs on the literal v27 selected packet.
Its output is named `FullFront.exitBank` so that the old numeric values are
not silently identified with the quartic ones. -/
theorem legacy_full_run_on_selected27 (Δ : ℕ) (γ : ℚ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices) (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    ∃ T ≤ FullFront.fullBd γ.num.toNat γ.den Δ g k
        ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t),
      ∃ vc, ∃ FL : CountFront.LK → List Bool,
      ∃ FQ : CountFront.QK → List Bool,
      ∃ FT : TMFront.TK → List Bool,
      ∃ FM : TMFront.MK → List Bool,
        ((advance (FullFront.full γ.num.toNat γ.den Δ))^[T])
          (⟨some (FullFront.fullStart γ.num.toNat γ.den Δ),
            FullFront.fullCtl, FullFront.F0 (inputBank27 Δ γ g hg hn k t)⟩ :
            TM2.Cfg (fun _ : FullFront.JF => Bool) _ _) =
          ⟨none, vc, FullFront.exitBank γ.num.toNat γ.den Δ g hg k
            ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)
            FL FQ FT FM⟩ := by
  obtain ⟨T, hT, vc, FL, FQ, FT, FM, hr, _, _, _, _⟩ :=
    FullFront.full_run γ.num.toNat γ.den Δ g hg k
      ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t)
  exact ⟨T, hT, vc, FL, FQ, FT, FM,
    selected_packet_eq_X0 Δ γ g hg hn k t ▸ hr⟩

/-- The already checked front also embeds into the reusable v27 physical
layout.  The output is still the legacy numeric region `stSched`. -/
theorem legacy_layout_run_on_selected27 (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (k : ℕ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    ∃ T ≤ FullFront.fullBd γ.num.toNat γ.den Δ g k
        ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t) +
        (g.vertices + g.edges.length + 2) + 1,
      ∃ u, ∃ bit : Bool, ∃ Z : FrontLift.FS → List Bool,
        ((advance (FrontLift.front Δ γ))^[T])
          (⟨some (FrontLift.sF Δ γ), FrontLift.vF Δ γ,
            Wrap.widen (Lift.a FrontLift.FS) (inputBank27 Δ γ g hg hn k t)⟩ :
            TM2.Cfg (fun _ : Fin (Lift.a FrontLift.FS + 3) => Bool) _ _) =
          ⟨none, u, Lift.layoutBank FrontLift.FS (inputBank27 Δ γ g hg hn k t)
            (Lift.region FrontLift.FS
              (FrontLift.stSched Δ γ g k
                ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t))
              ![[bit], [], []] Z)⟩ ∧
        (bit = true ↔ CompletePublicScheduleScratch.Checks
          (V := Fin g.vertices) (E := Fin g.edges.length)
          (Nat.clog 2 g.vertices) Δ γ) := by
  simpa only [← selected_packet_eq_X0 Δ γ g hg hn k t] using
    (FrontLift.front_run Δ γ hγ hΔ g hg hn hinc hdeg k
      ((select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t))

/-- An exact small numerical witness that the checked legacy front cannot be
used as a quartic front merely by changing names. -/
theorem legacy_width_ne_quartic_at_four (g : EncodedGraph.Graph)
    (hfour : g.vertices = 4) :
    FullFront.wV g ≠ width27 (Nat.clog 2 g.vertices) := by
  simp only [FullFront.wV, FullFront.eg, FullFront.Lg,
    width27, RestorationWidthScheduleScratch.ell, hfour]
  decide

end Paper2.CurrentAdditive.QuarticNumericFront

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.selected_packet_eq_X0
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.legacy_full_run_on_selected27
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.legacy_layout_run_on_selected27
#print axioms Paper2.CurrentAdditive.QuarticNumericFront.legacy_width_ne_quartic_at_four
