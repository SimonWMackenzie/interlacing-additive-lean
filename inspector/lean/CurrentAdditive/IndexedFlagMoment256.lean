import CurrentAdditive.IndexedIncomingDensity
import CurrentAdditive.IncomingEvenMoment256
import CurrentAdditive.MomentTransfer
import CurrentAdditive.BlockJointBridge

/-! A 256th-moment bound for Boolean flags on distinct coordinates of an
actual indexed bounded-wise code source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2
open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]
  {D w m : ℕ} {μ : PositiveRationalLaw A}
  (source : CodeSource D w A μ)

/-- The actual labelled source has the same 256th centered flag moment as
independent source outcomes, provided the selected positions are distinct. -/
theorem indexed_flag_moment_256 (hD : 8*256 ≤ D)
    (e : Fin m → Fin w) (he : Function.Injective e) (P : A → Bool) :
    expectation source.law.toFiniteLaw (fun seed =>
      |∑ i : Fin m,
        ((if P (source.decode seed (e i)) then (1 : ℝ) else 0) -
          source.law.toFiniteLaw.prob
            (fun seed' => P (source.decode seed' (e i)) = true))| ^ 256) ≤
      2 * ((64 : ℝ) * m) ^ 128 := by
  classical
  let ν := source.law.toFiniteLaw
  let F : Fin m → source.Label → Bool := fun i seed =>
    P (source.decode seed (e i))
  let blocks : Fin m → Finset (Fin w) := fun i => {e i}
  let H : ∀ i : Fin m, (blocks i → A) → Bool := fun i z =>
    P (z ⟨e i, Finset.mem_singleton_self _⟩)
  have hsize : ∀ i : Fin m, (blocks i).card ≤ 8 := by
    intro i
    simp [blocks]
  have hdisj : Pairwise (fun i j : Fin m => Disjoint (blocks i) (blocks j)) := by
    intro i j hij
    simp only [blocks, Finset.disjoint_singleton]
    exact fun h => hij (he h)
  have hwise : IsDWise (8*256) ν source.decode μ.toFiniteLaw := by
    intro S hS E
    exact source.exactLaw S (hS.trans (by omega)) E
  have hjoint : IndicatorJointAgreement ν F 256 := by
    intro S hS E
    have h := disjoint_blocks_indicator_joint_agreement ν μ.toFiniteLaw
      source.decode hwise blocks hsize hdisj H S hS E
    simpa only [F, H, blocks, Finset.mem_singleton] using h
  have htransfer := centered_indicator_even_moment_eq_proxy ν F 256
    (by norm_num : Even 256) hjoint
  have hproxy := EvenMoment.iid_centered_indicator_moment_256 ν m F
  have hmain : expectation ν (fun ω => |∑ i : Fin m,
      ((if F i ω then (1 : ℝ) else 0) -
        ν.prob (fun ω' => F i ω'))| ^ 256) ≤
      2 * ((64 : ℝ) * m) ^ 128 := by
    rw [htransfer]
    simpa [EvenMoment.ex, expectation] using hproxy
  simpa only [F, ν] using hmain

#print axioms indexed_flag_moment_256

end CurrentAdditive.DeterministicIndexedMatrix
