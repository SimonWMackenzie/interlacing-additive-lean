import CurrentAdditive.QuarticSourceSize
import Paper2.CheckBit

/-! A fixed physical decision controller for the literal v27 public checks.
It uses the admitted saturating two-counter program, with a new finite table
whose entries are exactly `QuarticSchedule.Checks27`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticCheckBit

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2
open Paper2.CheckBit

def NA27 (Δ : ℕ) (γ : ℚ) : ℕ := CurrentAdditive.QuarticSchedule.threshold27 Δ γ
def NB27 (Δ : ℕ) (γ : ℚ) : ℕ := Δ * NA27 Δ γ

/-- This is a finite table fixed when the machine is fixed. Above the cutoff,
the checked all-large theorem makes every entry true. -/
noncomputable def tab27 (Δ : ℕ) (γ : ℚ) (ca cb : ℕ) : Bool := by
  classical
  exact decide (NA27 Δ γ ≤ ca) ||
    decide (CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin ca) (Edges := Fin cb) (Nat.clog 2 ca) Δ γ)

variable {K : Type*} [DecidableEq K]

noncomputable def checkProg27 (A B O : K) (Δ : ℕ) (γ : ℚ) :=
  CheckBit.program A B O (NA27 Δ γ) (NB27 Δ γ) (tab27 Δ γ)

theorem tab_correct27 (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ) :
    (tab27 Δ γ (min g.vertices (NA27 Δ γ))
        (min g.edges.length (NB27 Δ γ)) = true ↔
      CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin g.vertices) (Edges := Fin g.edges.length)
        (Nat.clog 2 g.vertices) Δ γ) := by
  haveI : Nonempty (Fin g.vertices) := ⟨⟨0, hn⟩⟩
  by_cases hbig : NA27 Δ γ ≤ g.vertices
  · have hmin : min g.vertices (NA27 Δ γ) = NA27 Δ γ := min_eq_right hbig
    have hC := CurrentAdditive.QuarticSchedule.all_large_checks27_at_graph
      (V := Fin g.vertices) (Edges := Fin g.edges.length)
      (CanonicalEdgeTape.graphEdge g hg) Δ γ hγ hΔ hinc hdeg
      (by simpa only [Fintype.card_fin, NA27] using hbig)
    simp only [Fintype.card_fin] at hC
    simp only [tab27, hmin, le_refl, decide_true, Bool.true_or, true_iff]
    exact hC
  · have hsmall : g.vertices < NA27 Δ γ := Nat.lt_of_not_le hbig
    have hmin : min g.vertices (NA27 Δ γ) = g.vertices := min_eq_left (le_of_lt hsmall)
    have h2 := SourceDensityScheduleScratch.twice_edges_le_degree_vertices
      (V := Fin g.vertices) (E := Fin g.edges.length)
      (CanonicalEdgeTape.graphEdge g hg) Δ hdeg
    simp only [Fintype.card_fin] at h2
    have hm : g.edges.length ≤ NB27 Δ γ := by
      have : Δ * g.vertices ≤ Δ * NA27 Δ γ :=
        Nat.mul_le_mul_left _ (le_of_lt hsmall)
      simp only [NB27]
      omega
    have hminm : min g.edges.length (NB27 Δ γ) = g.edges.length := min_eq_left hm
    rw [hmin, hminm]
    simp only [tab27, Bool.or_eq_true, decide_eq_true_iff]
    exact ⟨fun h => h.resolve_left hbig, fun h => Or.inr h⟩

/-- Exact v27 decision bit on a generic bank holding unary n and m. -/
theorem check_run27 (A B O : K) (hAB : A ≠ B) (hAO : A ≠ O) (hBO : B ≠ O)
    (Δ : ℕ) (γ : ℚ) (hγ : 0 < γ) (hΔ : 0 < Δ)
    (g : EncodedGraph.Graph) (hg : g.Valid) (hn : 0 < g.vertices)
    (hinc : ∀ v, ∃ e b, CanonicalEdgeTape.graphEdge g hg e b = v)
    (hdeg : ∀ v, SourceItems.degree (CanonicalEdgeTape.graphEdge g hg) v ≤ Δ)
    (S : K → List Bool) (hA : S A = List.replicate g.vertices true)
    (hB : S B = List.replicate g.edges.length true) :
    ∃ w, ∃ bit : Bool,
      ((advance (checkProg27 A B O Δ γ))^[g.vertices + g.edges.length + 2])
        (⟨some .rdA, CheckBit.ctl0 (NA27 Δ γ) (NB27 Δ γ), S⟩ :
          TM2.Cfg (fun _ : K => Bool) CheckBit.DL
            (CheckBit.DV (NA27 Δ γ) (NB27 Δ γ))) =
        ⟨none, w, Function.update (Function.update (Function.update S A []) B []) O
          (bit :: S O)⟩ ∧
      (bit = true ↔ CurrentAdditive.QuarticSchedule.Checks27
        (V := Fin g.vertices) (Edges := Fin g.edges.length)
        (Nat.clog 2 g.vertices) Δ γ) := by
  obtain ⟨w, hw⟩ := CheckBit.decide_run A B O hAB hAO hBO
    (NA27 Δ γ) (NB27 Δ γ) (tab27 Δ γ) S _ _ hA hB
  exact ⟨w, _, hw, tab_correct27 Δ γ hγ hΔ g hg hn hinc hdeg⟩

#print axioms tab_correct27
#print axioms check_run27

end Paper2.CurrentAdditive.QuarticCheckBit
