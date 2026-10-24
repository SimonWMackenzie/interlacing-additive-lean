import CurrentAdditive.NextClockAtoms

/-! Polynomial bounds for physical constructor stage clocks. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open EthInapproximability.CurrentPaper
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoClockPoly

set_option maxHeartbeats 2000000

theorem poly_powerBound {t : ℕ} {f : YaoSource t → ℕ}
    (hf : PolyIn f) (s : ℕ) :
    PolyIn (fun x => MatrixWeightedPower.powerBound (f x) s) := by
  apply poly_mono (g := fun x =>
    (s+1) * (3*((f x)^s+1)*(f x)+5*((f x)^s+1)+7))
  · intro x
    exact MatrixWeightedPower.powerBound_polynomial (f x) s
  · repeat' poly_step

theorem poly_degreeClock (t : ℕ) :
    PolyIn (fun x : YaoSource t =>
      YaoDegreeClock.polynomial t (paddedEdgeCount x.2.1)) := by
  simp only [YaoDegreeClock.polynomial, YaoDegreeClock.setupCap,
    YaoDegreeClock.aCap, YaoDegreeClock.qCap, YaoDegreeClock.testCap]
  repeat' poly_step

theorem poly_sourceSelectorClock (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (sourceSelectorClock (t := t)) := by
  have hsource := sourceClock_poly t (by omega : 1 ≤ t)
  have hdegree := poly_degreeClock t
  have hdegree' : PolyIn (fun x : YaoSource t =>
      YaoDegreeClock.polynomial t (2 ^ paddedEdgeBits x.2.1)) := by
    simpa only [paddedEdgeCount] using hdegree
  have hpower := poly_powerBound (poly_H (t := t)) (2^(t-1))
  unfold sourceSelectorClock MatrixAddressMachine.exactTime
  repeat' poly_step

theorem poly_squarePowerClock (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fun x : YaoSource t =>
      MatrixWeightedPower.powerBound 4
        (publicFieldDegree (paddedEdgeBits x.2.1) t)) := by
  apply poly_mono (g := fun x : YaoSource t =>
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    (d+1)*(3*((2^d)^2+1)*4+5*((2^d)^2+1)+7))
  · intro x
    have h := MatrixWeightedPower.powerBound_polynomial 4
      (publicFieldDegree (paddedEdgeBits x.2.1) t)
    have he (d : ℕ) : (4 : ℕ)^d = (2^d)^2 := by
      calc
        (4 : ℕ)^d = (2^2)^d := by norm_num
        _ = (2^d)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 d]
    simpa only [he] using h
  · have hd := poly_public_degree t ht
    have hq := poly_public_order t ht
    have hd1 := poly_add hd (poly_const 1)
    have hq2 := poly_pow hq 2
    have hq21 := poly_add hq2 (poly_const 1)
    have hleft := poly_mul (poly_mul (poly_const 3) hq21)
      (poly_const 4)
    have hright := poly_mul (poly_const 5) hq21
    exact poly_mul hd1
      (poly_add (poly_add hleft hright) (poly_const 7))

def sourceFieldBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  sourceFieldClock x (fieldBudget x)

theorem poly_sourceFieldBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (sourceFieldBudget (t := t)) := by
  have hs := poly_sourceSelectorClock t ht
  have hd := poly_public_degree t ht
  have hn := poly_public_width t
  have hu := poly_fieldBudget t ht
  have hp := poly_squarePowerClock t ht
  unfold sourceFieldBudget sourceFieldClock
  repeat' poly_step

#print axioms poly_powerBound
#print axioms poly_degreeClock
#print axioms poly_sourceSelectorClock
#print axioms poly_squarePowerClock
#print axioms poly_sourceFieldBudget

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
