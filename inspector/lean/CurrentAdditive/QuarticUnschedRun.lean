import CurrentAdditive.QuarticUnschedFinite

/-! Physical fixed fallback run under failed literal v27 public checks. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace Paper2.CurrentAdditive.QuarticUnschedRun

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2 Paper2.A3Assembly.Unsched
open Paper2.CurrentAdditive.QuarticUnschedFinite
open Paper2.CurrentAdditive.QuarticConstructor

/-- Clock of the existing five-stage fallback printer with the new finite
exception threshold in its table-search stage. -/
noncomputable def clockU27 (g : EncodedGraph.Graph) (hg : g.Valid)
    (Δ : ℕ) (γ : ℚ) (k : ℕ) : ℕ :=
  103 * ((EncodedGraph.encode g).length + 1) ^ 3 +
    (3 * (2 * LB g hg k + 3) + 1) +
    FallbackFiniteClock.coefficient (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) Δ *
      2 ^ (3 * k) +
    (3 * (2 * LD g hg k + 3) + 1) + headerClock k + 4

/-- Only the finite-search stage changes proof: source failure gives the new
constant bound; the physical `fProg` is unchanged. -/
theorem stageC27 (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (Δ : ℕ) (γ : ℚ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (k : ℕ)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (hc : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ) :
    ∃ t ≤ FallbackFiniteClock.coefficient
        (CurrentAdditive.QuarticSchedule.threshold27 Δ γ) Δ * 2 ^ (3 * k),
      ∃ (ctl : FallbackBranchT.ACtl) (q : List Bool),
        ((advance fProg)^[t])
          (⟨some (Sum.inl FallbackBranch.Adm.alloc), ctlF, bankB g hg k⟩ :
            TM2.Cfg (fun _ : JU => Bool) _ _) = ⟨none, ctl, bankC g hg k q⟩ := by
  haveI : Nonempty (Fin g.vertices) := ⟨⟨0, hn⟩⟩
  obtain ⟨t, ht, ctl, q, hr⟩ := failed_schedule_run27
    (CanonicalEdgeTape.graphEdge g hg) Δ γ hγ hΔ hinc hdeg hc k
  refine ⟨t, ht, ctl, q, ?_⟩
  unfold FallbackFiniteClock.RunsToTable at hr
  have h := BitMachineStackRun.run ιF (bankB g hg k) FallbackBranchT.program
    (FallbackBranchT.start (CanonicalEdgeTape.graphEdge g hg) k) t
  have hr' : ((advance FallbackBranchT.program)^[t])
      (FallbackBranchT.start (CanonicalEdgeTape.graphEdge g hg) k) =
      ⟨none, ctl, fbFinal (CanonicalEdgeTape.graphEdge g hg) k q⟩ := hr
  rw [hr'] at h
  change ((advance fProg)^[t])
      ⟨some (Sum.inl FallbackBranch.Adm.alloc), ctlF,
        bank ιF (bankB g hg k)
          (FallbackBranchT.start (CanonicalEdgeTape.graphEdge g hg) k).stk⟩ =
      ⟨none, ctl,
        bank ιF (bankB g hg k)
          (fbFinal (CanonicalEdgeTape.graphEdge g hg) k q)⟩ at h
  unfold bankB at h
  rw [bank_F, bank_F] at h
  exact h

/-- The original fixed fallback program prints the v27 selector's exact
fallback matrix when the literal v27 check fails. -/
theorem unscheduled_run27 (g : EncodedGraph.Graph) (hg : g.Valid)
    (hn : 0 < g.vertices) (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (k : ℕ)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (hc : ¬ CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (Nat.clog 2 g.vertices) Δ γ)
    (t : (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).Tape) :
    ∃ T ≤ clockU27 g hg Δ γ k, ∃ ctl, ∃ (q : List Bool)
      (F : Paper2.A3Assembly.Unsched.HB → List Bool),
      ((advance progU)^[T])
        (⟨some startU, ctlU, entry g k⟩ : TM2.Cfg (fun _ : JU => Bool) _ _) =
        ⟨none, ctl, exitU g hg k q F⟩ ∧
      F HeaderA.outH = outputBits27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k t ∧
      (select27 hn (CanonicalEdgeTape.graphEdge g hg) Δ γ k).tapeBits t = [] := by
  obtain ⟨tA, htA, hA⟩ := stageA g hg k
  obtain ⟨tB, htB, vB, hB⟩ := stageB g hg k
  obtain ⟨tC, htC, ctlC, q, hC⟩ := stageC27 g hg hn Δ γ hγ hΔ k hinc hdeg hc
  obtain ⟨tD, htD, vD, hD⟩ := stageD g hg k q
  obtain ⟨tE, htE, vE, F, hE, hF⟩ := stageE g hg k q
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs gProg (CopyAll.prog cpB)
    _ _ _ _ _ _ _ _ _ tA tB hA hB
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs p1 fProg
    _ _ _ _ _ _ _ _ _ u1 tC r1 hC
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs p2 (CopyAll.prog cpD)
    _ _ _ _ _ _ _ _ _ u2 tD r2 hD
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs p3 hProg
    _ _ _ _ _ _ _ _ _ u3 tE r3 hE
  obtain ⟨hbits, htape⟩ := outputBits_unscheduled27 hn
    (CanonicalEdgeTape.graphEdge g hg) Δ γ k hc t
  refine ⟨u4, ?_, _, q, F, r4, ?_, htape⟩
  · unfold clockU27
    omega
  · rw [hF, hbits]
    rfl

#print axioms stageC27
#print axioms unscheduled_run27

end Paper2.CurrentAdditive.QuarticUnschedRun
