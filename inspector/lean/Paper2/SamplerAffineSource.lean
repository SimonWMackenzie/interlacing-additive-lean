import Paper2.SamplerAffineLoop
import Paper2.RecursiveSamplingExecution

set_option maxHeartbeats 1000000

namespace Paper2.SamplerAffineSource

def coeffA (s q₁ q₂ w Q : Nat) : Nat := Q * (s+2)
def coeffB (s q₁ q₂ w Q : Nat) : Nat :=
  Q * (s+1+s*(q₁+s+1))
def coeffC (s q₁ q₂ w Q : Nat) : Nat := 1+3*w+w*q₂
def coeffD (s q₁ q₂ w Q : Nat) : Nat := w*q₂

theorem row_step (s q₁ q₂ w Q r c : Nat) :
    coeffA s q₁ q₂ w Q + coeffB s q₁ q₂ w Q * c =
      Q * (2+s+((s+1)+s*(q₁+s+1))*c) := by
  unfold coeffA coeffB
  ring

theorem col_step (s q₁ q₂ w Q r c : Nat) :
    coeffC s q₁ q₂ w Q + coeffD s q₁ q₂ w Q * r =
      1+w*(3+q₂*(1+r)) := by
  unfold coeffC coeffD
  ring

theorem values_succ (A B C D k r c : Nat) :
    SamplerAffineLoop.values A B C D (k+1) r c =
      (A + B * (SamplerAffineLoop.values A B C D k r c).2,
       C + D * (SamplerAffineLoop.values A B C D k r c).1) := by
  induction k generalizing r c with
  | zero => rfl
  | succ k ih =>
      change SamplerAffineLoop.values A B C D (k+1)
          (A+B*c) (C+D*r) =
        (A+B*(SamplerAffineLoop.values A B C D (k+1) r c).2,
          C+D*(SamplerAffineLoop.values A B C D (k+1) r c).1)
      simpa only [SamplerAffineLoop.values] using
        ih (A+B*c) (C+D*r)

theorem values_eq_drawBounds (s q₁ q₂ w Q r₀ c₀ k : Nat) :
    SamplerAffineLoop.values
      (coeffA s q₁ q₂ w Q) (coeffB s q₁ q₂ w Q)
      (coeffC s q₁ q₂ w Q) (coeffD s q₁ q₂ w Q)
      k r₀ c₀ = RecursiveSampling.drawBounds s q₁ q₂ w Q r₀ c₀ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [values_succ, ih]
      simp only [RecursiveSampling.drawBounds]
      apply Prod.ext
      · exact row_step s q₁ q₂ w Q
          (RecursiveSampling.drawBounds s q₁ q₂ w Q r₀ c₀ k).1
          (RecursiveSampling.drawBounds s q₁ q₂ w Q r₀ c₀ k).2
      · exact col_step s q₁ q₂ w Q
          (RecursiveSampling.drawBounds s q₁ q₂ w Q r₀ c₀ k).1
          (RecursiveSampling.drawBounds s q₁ q₂ w Q r₀ c₀ k).2

theorem exact_N (s q₁ q₂ w Q p k mX mY : Nat) :
    1 + mY * (SamplerAffineLoop.values
      (coeffA s q₁ q₂ w Q) (coeffB s q₁ q₂ w Q)
      (coeffC s q₁ q₂ w Q) (coeffD s q₁ q₂ w Q)
      k p 1).2 +
      mX * (SamplerAffineLoop.values
      (coeffA s q₁ q₂ w Q) (coeffB s q₁ q₂ w Q)
      (coeffC s q₁ q₂ w Q) (coeffD s q₁ q₂ w Q)
      k p 1).1 =
      RecursiveSamplingExecution.drawCap s q₁ q₂ w Q p k mX mY := by
  rw [values_eq_drawBounds]
  rfl

#print axioms values_eq_drawBounds
#print axioms exact_N

end Paper2.SamplerAffineSource
