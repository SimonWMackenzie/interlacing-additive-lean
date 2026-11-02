import Paper2.DefectInduction
import Paper2.RationalRowEstimates

/-!
# Defect induction on the original rationally weighted matrix

Frozen v12 Appendix A, `cl:defect-induction` together with
`cl:rational-laws`. A nonempty, arbitrarily correlated retained column
set is lifted by taking all its labelled copies. Exact product-law
transport gives the same logarithmic defect; arbitrary partial-copy
restrictions are already covered by the base lower-bound/profile transport.
The uniform theorem is then applied and its conclusion returns to the
same original retained matrix by exact communication-cost equality.
-/

namespace Paper2.DefectInduction

open Workspace.Types.CommComplexity
open RationalSeparation

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- All original retained tuples have surviving labelled lifts, including
when the retained set has correlations between every coordinate. -/
theorem lifted_columns_nonempty (ν : PositiveRationalLaw Y) (p : ℕ)
    (K : Finset (Fin p → Y)) (hK : K.Nonempty) :
    (liftSet (ν.forgetTuple p) K).Nonempty := by
  obtain ⟨c, hc⟩ := hK
  obtain ⟨d, hd⟩ := ν.forgetTuple_surjective p c
  exact ⟨d, (mem_liftSet _ _ _).mpr (hd ▸ hc)⟩

/-- The copied cardinality density is exactly the original joint
probability, not a lower bound on an unrelated projection. -/
theorem lifted_columnDensity (ν : PositiveRationalLaw Y) (p : ℕ)
    (K : Finset (Fin p → Y)) :
    ProjectionDefect.columnDensity p (liftSet (ν.forgetTuple p) K) =
      (ν.toFiniteLaw.iid p).prob (· ∈ K) := by
  rw [ProjectionDefect.columnDensity_eq_prob]
  simpa only [mem_liftSet] using tuples_prob_preimage ν p (· ∈ K)

/-- T43 with positive rational input laws and actual retained inputs.
`C` is only a lower bound. The one-copy input is stated as the exact
universal retained-rectangle lower bound rather than as an opaque family
certificate, and every other hypothesis is the paper's displayed one. -/
theorem rational_defect_induction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (C p a e : ℕ) (θ δ : ℝ)
    (hC : 3 ≤ C) (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 4)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 64)
    (he : e ≤ 1) (ha : 2 * e ≤ a)
    (hp : 2 ^ a < 2 * p) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hnear : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw
      θ (1 - δ) (C : ℤ))
    (hprofile : RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((C : ℤ) - 1))
    (R : Finset (Fin p × X)) (K : Finset (Fin p → Y)) (hK : K.Nonempty)
    (hR : ∀ i, (2 : ℝ) ^ a * θ ≤ μ.toFiniteLaw.prob (fun x => (i, x) ∈ R))
    (hdef : ProjectionDefect.defect ((ν.toFiniteLaw.iid p).prob (· ∈ K)) ≤
      ((p : ℝ) - (2 : ℝ) ^ ((a : ℤ) - 1)) * δ +
        (e : ℝ) * (1 + 1 / (p : ℝ))) :
    C + a - e ≤ D (NPCC.subgame (fullInterlace F p) R K) := by
  let M := matrix μ ν F 1
  have hnear' : RestrictionLowerBound M
      (FiniteLaw.uniform (Rows μ 1)) (FiniteLaw.uniform ν.Copies)
      θ (1 - δ) (C : ℤ) :=
    (RationalRowEstimates.matrix_lowerBound_iff μ ν F 1 θ (1 - δ) (C : ℤ)).mpr hnear
  have hfamily : C ≤ ClassicalRows.restrictionCost M 1 θ (1 - δ) := by
    have hh := ClassicalSeparation.oneCopy_family_lowerBound M θ (1 - δ) (C : ℤ)
      (by linarith) (by linarith) hnear'
    exact_mod_cast hh
  have hrows := RationalRowEstimates.lifted_selected_rows μ 1 p Finset.univ R
    ((2 : ℝ) ^ a * θ) (fun i _ => hR i)
  have hrows' : NPCC.IsEquipartitionedGE (liftSet (blockForget μ 1 p) R) Finset.univ
      ⌈(Fintype.card (Rows μ 1) : ℝ) * (2 : ℝ) ^ a * θ⌉₊ := by
    simpa only [mul_assoc] using hrows
  have hout := defect_induction M C p a e θ δ hC hθ hθ1 hδ hδ1 he ha hp hscale
    hfamily ((matrix_profile_iff μ ν F 1 θ ((C : ℤ) - 1)).mpr hprofile)
    (liftSet (blockForget μ 1 p) R) (liftSet (ν.forgetTuple p) K)
    (lifted_columns_nonempty ν p K hK) hrows'
    (by simpa only [lifted_columnDensity] using hdef)
  exact (RationalRowEstimates.lifted_D_eq μ ν F 1 p R K) ▸ hout

end Paper2.DefectInduction
