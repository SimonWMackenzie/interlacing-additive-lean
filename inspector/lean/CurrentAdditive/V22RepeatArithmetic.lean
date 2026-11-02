import CurrentAdditive.EdgeMatrixProductionConjugacy
import CurrentAdditive.V38Schedule

namespace V22RepeatArithmetic
open CurrentAdditive

def q0 (s m : ℕ) : ℕ := 2 ^ Nat.clog 2 (4*s*m)
def repetitions (q₂ s m : ℕ) : ℕ := q₂ / q0 s m

theorem q0_source (s m : ℕ) :
    q0 s m = EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) := by
  rw [EdgeSource.sourceQ0_literal]
  simp only [Fintype.card_fin,q0,Paper2.SourcePadding.powTwoCeil]

theorem q0_pos (s m : ℕ) : 0 < q0 s m := by unfold q0; positivity

theorem pow2_dvd_of_le {a b : ℕ} (h : 2^a ≤ 2^b) : 2^a ∣ 2^b :=
  pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h)

theorem fullQ₂_power (L : ℕ) :
    V38Schedule.fullQ₂ L = 2^(L+2*(16+V38Schedule.ell L)) := by
  simp only [V38Schedule.fullQ₂,V38Schedule.fullS,←pow_mul,←pow_add]
  congr 1
  omega

theorem full_width (L m : ℕ)
    (h : q0 (V38Schedule.fullS L) m ≤ V38Schedule.fullQ₂ L) :
    V38Schedule.fullQ₂ L = LiteralEdgeEncoder.Width (V38Schedule.fullS L) m
      (repetitions (V38Schedule.fullQ₂ L) (V38Schedule.fullS L) m) := by
  have hd : q0 (V38Schedule.fullS L) m ∣ V38Schedule.fullQ₂ L := by
    rw [fullQ₂_power] at h ⊢
    exact pow2_dvd_of_le h
  change V38Schedule.fullQ₂ L =
    EdgeSource.sourceQ0 (Fin (4*V38Schedule.fullS L)) (Fin m) *
      (V38Schedule.fullQ₂ L / q0 (V38Schedule.fullS L) m)
  rw [←q0_source]
  exact (Nat.mul_div_cancel' hd).symm

theorem full_width_of_tests (c δv ζ : ℚ) (L m : ℕ)
    (h : V38Schedule.FullTests c L m δv ζ) :
    V38Schedule.fullQ₂ L = LiteralEdgeEncoder.Width (V38Schedule.fullS L) m
      (repetitions (V38Schedule.fullQ₂ L) (V38Schedule.fullS L) m) := by
  apply full_width
  exact h.1.2.2.1

theorem full_repeat_pos (L m : ℕ)
    (h : q0 (V38Schedule.fullS L) m ≤ V38Schedule.fullQ₂ L) :
    0 < repetitions (V38Schedule.fullQ₂ L) (V38Schedule.fullS L) m :=
  Nat.div_pos h (q0_pos _ _)

#print axioms full_width_of_tests
end V22RepeatArithmetic
