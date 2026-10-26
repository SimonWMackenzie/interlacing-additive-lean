import CurrentAdditive.NextFullRendererValid

/-! Public-size atoms for the source-started canonical renderer clock. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoSourceCodec Paper2.YaoLookup Paper2.YaoClockPoly

theorem poly_public_degree (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fun x : YaoSource t =>
      publicFieldDegree (paddedEdgeBits x.2.1) t) := by
  apply poly_mono (g := fun x : YaoSource t =>
    paddedEdgeBits x.2.1 * degreeSlope t + degreeOffset t)
  · intro x
    have hd := public_degree_cost_bound (paddedEdgeBits x.2.1) t ht
    dsimp only [degreeSlope, degreeOffset]
    omega
  · exact poly_add (poly_mul poly_b (poly_const _)) (poly_const _)

theorem poly_public_order (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fun x : YaoSource t =>
      2 ^ publicFieldDegree (paddedEdgeBits x.2.1) t) := by
  apply poly_mono (g := fun x : YaoSource t =>
    2 ^ degreeOffset t *
      (2 ^ paddedEdgeBits x.2.1) ^ degreeSlope t)
  · intro x
    have hd := public_degree_cost_bound (paddedEdgeBits x.2.1) t ht
    have hd' : publicFieldDegree (paddedEdgeBits x.2.1) t ≤
        paddedEdgeBits x.2.1 * degreeSlope t + degreeOffset t := by
      dsimp only [degreeSlope, degreeOffset]
      omega
    calc
      2 ^ publicFieldDegree (paddedEdgeBits x.2.1) t ≤
          2 ^ (paddedEdgeBits x.2.1 * degreeSlope t +
            degreeOffset t) := Nat.pow_le_pow_right (by omega) hd'
      _ = 2 ^ degreeOffset t *
          (2 ^ paddedEdgeBits x.2.1) ^ degreeSlope t := by
          rw [pow_add, pow_mul]
          ring
  · exact poly_mul (poly_const _) (poly_pow poly_H' _)

theorem poly_public_width (t : ℕ) :
    PolyIn (fun x : YaoSource t =>
      paddedEdgeCount x.2.1 * (arity t + 1)) :=
  poly_mul poly_H (poly_const _)

theorem poly_public_cap (t : ℕ) :
    PolyIn (fun x : YaoSource t =>
      (paddedEdgeCount x.2.1) ^ (2 ^ (t - 1))) :=
  poly_pow poly_H _

theorem poly_public_rows (t : ℕ) :
    PolyIn (fun x : YaoSource t =>
      rowCount x.1 (paddedEdgeBits x.2.1) t) := by
  unfold rowCount
  exact poly_mul poly_v (poly_pow poly_H' _)

theorem poly_public_columns (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fun x : YaoSource t =>
      columnCount (paddedEdgeBits x.2.1) t
        (publicFieldDegree (paddedEdgeBits x.2.1) t)) := by
  unfold columnCount
  exact poly_mul (poly_mul (poly_const _) poly_H')
    (poly_pow (poly_public_order t ht) 2)

def fieldBudget {t : ℕ} (x : YaoSource t) : ℕ :=
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let q := 2 ^ d
  let n := paddedEdgeCount x.2.1 * (arity t + 1)
  (3*d + 2*n + 7) + 55*q*q*(d+1)^2 + 2 +
    25*q^2*n*(d+1)^2

theorem field_steps_le_budget {t : ℕ} (x : YaoSource t)
    (c u : ℕ)
    (hu : u ≤ CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine.prepTime
        (publicFieldDegree (paddedEdgeBits x.2.1) t)
        (paddedEdgeCount x.2.1*(arity t+1)) +
      55*2^publicFieldDegree (paddedEdgeBits x.2.1) t *
        2^(publicFieldDegree (paddedEdgeBits x.2.1) t/2) *
        (publicFieldDegree (paddedEdgeBits x.2.1) t+1)^2 + 2 +
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound
        (publicFieldDegree (paddedEdgeBits x.2.1) t) c
        (paddedEdgeCount x.2.1*(arity t+1))) :
    u ≤ fieldBudget x := by
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  let q := 2 ^ d
  let n := paddedEdgeCount x.2.1*(arity t+1)
  have hd : 0 < d := public_degree_pos _ _
  have hn : 0 < n := by
    dsimp [n]
    have hH : 0 < paddedEdgeCount x.2.1 := by
      unfold paddedEdgeCount
      positivity
    have hK : 0 < arity t + 1 := by omega
    positivity
  have hhalf : 2 ^ (d/2) ≤ q := by
    dsimp [q]
    exact Nat.pow_le_pow_right (by omega) (Nat.div_le_self d 2)
  have htime := CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound_le
    d c n hd hn
  change CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n ≤
    25*q^2*n*(d+1)^2 at htime
  have hprep :
      CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine.prepTime d n ≤
        3*d+2*n+7 := by
    dsimp [CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine.prepTime]
    omega
  change u ≤ CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine.prepTime
      d n + 55*q*2^(d/2)*(d+1)^2+2+
      CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n at hu
  dsimp only [fieldBudget]
  change u ≤ (3*d+2*n+7)+55*q*q*(d+1)^2+2+
    25*q^2*n*(d+1)^2
  have hsearch : 55*q*2^(d/2)*(d+1)^2 ≤
      55*q*q*(d+1)^2 := by gcongr
  omega

theorem poly_fieldBudget (t : ℕ) (ht : 4 ≤ t) :
    PolyIn (fieldBudget (t := t)) := by
  have hd := poly_public_degree t ht
  have hq := poly_public_order t ht
  have hn := poly_public_width t
  unfold fieldBudget
  repeat' poly_step

#print axioms poly_public_degree
#print axioms poly_public_order
#print axioms poly_public_width
#print axioms poly_public_cap
#print axioms poly_public_rows
#print axioms poly_public_columns
#print axioms field_steps_le_budget
#print axioms poly_fieldBudget

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
