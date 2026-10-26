import CurrentAdditive.EntryStep

namespace CurrentAdditive.EliminationEntryBounds

open CurrentAdditive.RationalBitBounds

def ComponentsWithin (H : ℕ) (q : ℚ) : Prop :=
  q.num.natAbs ≤ H ∧ q.den ≤ H

theorem components_mono {H K : ℕ} {q : ℚ}
    (h : ComponentsWithin H q) (hHK : H ≤ K) :
    ComponentsWithin K q := ⟨h.1.trans hHK, h.2.trans hHK⟩

theorem components_mul {H₁ H₂ : ℕ} {q r : ℚ}
    (hq : ComponentsWithin H₁ q) (hr : ComponentsWithin H₂ r) :
    ComponentsWithin (H₁ * H₂) (q * r) := by
  have hd : (q.den : ℤ) * (r.den : ℤ) ≠ 0 := by positivity
  have hrepr : q * r = ((q.num * r.num : ℤ) : ℚ) /
      (((q.den * r.den : ℕ) : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den r]
    norm_cast
    simp only [Rat.divInt_eq_div]
    field_simp [q.den_ne_zero, r.den_ne_zero]
    push_cast
    ring
  have hh := rat_components_le_of_divInt (q * r)
    (q.num * r.num) ((q.den * r.den : ℕ) : ℤ) hd hrepr
  dsimp [ComponentsWithin] at hq hr ⊢
  constructor
  · calc
      (q * r).num.natAbs ≤ (q.num * r.num).natAbs := hh.1
      _ = q.num.natAbs * r.num.natAbs := Int.natAbs_mul ..
      _ ≤ H₁ * H₂ := Nat.mul_le_mul hq.1 hr.1
  · calc
      (q * r).den ≤ ((q.den * r.den : ℕ) : ℤ).natAbs := hh.2
      _ = q.den * r.den := by simp [Int.natAbs_mul]
      _ ≤ H₁ * H₂ := Nat.mul_le_mul hq.2 hr.2

theorem components_div {H₁ H₂ : ℕ} {q r : ℚ}
    (hq : ComponentsWithin H₁ q) (hr : ComponentsWithin H₂ r)
    (hr0 : r ≠ 0) :
    ComponentsWithin (H₁ * H₂) (q / r) := by
  have hrn : r.num ≠ 0 := Rat.num_ne_zero.mpr hr0
  have hd : (q.den : ℤ) * r.num ≠ 0 := mul_ne_zero (by positivity) hrn
  have hrepr : q / r = ((q.num * r.den : ℤ) : ℚ) /
      ((q.den * r.num : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den r]
    norm_cast
    simp only [Rat.divInt_eq_div]
    field_simp [hrn, q.den_ne_zero, r.den_ne_zero]
    push_cast
    ring
  have hh := rat_components_le_of_divInt (q / r)
    (q.num * r.den) (q.den * r.num) hd hrepr
  dsimp [ComponentsWithin] at hq hr ⊢
  constructor
  · calc
      (q / r).num.natAbs ≤ (q.num * r.den).natAbs := hh.1
      _ = q.num.natAbs * r.den := by simp [Int.natAbs_mul]
      _ ≤ H₁ * H₂ := Nat.mul_le_mul hq.1 hr.2
  · calc
      (q / r).den ≤ (q.den * r.num).natAbs := hh.2
      _ = q.den * r.num.natAbs := by simp [Int.natAbs_mul]
      _ ≤ H₁ * H₂ := Nat.mul_le_mul hq.2 hr.1

theorem components_sub {H₁ H₂ : ℕ} {q r : ℚ}
    (hq : ComponentsWithin H₁ q) (hr : ComponentsWithin H₂ r) :
    ComponentsWithin (2 * (H₁ * H₂)) (q - r) := by
  have hd : (q.den : ℤ) * (r.den : ℤ) ≠ 0 := by positivity
  have hrepr : q - r =
      ((q.num * r.den - r.num * q.den : ℤ) : ℚ) /
      (((q.den * r.den : ℕ) : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den q, ← Rat.num_div_den r]
    norm_cast
    simp only [Rat.divInt_eq_div]
    field_simp [q.den_ne_zero, r.den_ne_zero]
    push_cast
    ring
  have hh := rat_components_le_of_divInt (q - r)
    (q.num * r.den - r.num * q.den)
    ((q.den * r.den : ℕ) : ℤ) hd hrepr
  dsimp [ComponentsWithin] at hq hr ⊢
  constructor
  · calc
      (q - r).num.natAbs ≤
          (q.num * r.den - r.num * q.den).natAbs := hh.1
      _ ≤ (q.num * r.den).natAbs + (r.num * q.den).natAbs :=
        Int.natAbs_sub_le _ _
      _ = q.num.natAbs * r.den + r.num.natAbs * q.den := by
        simp [Int.natAbs_mul]
      _ ≤ H₁ * H₂ + H₂ * H₁ :=
        Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2)
          (Nat.mul_le_mul hr.1 hq.2)
      _ = 2 * (H₁ * H₂) := by ring
  · calc
      (q - r).den ≤ ((q.den * r.den : ℕ) : ℤ).natAbs := hh.2
      _ = q.den * r.den := by simp [Int.natAbs_mul]
      _ ≤ H₁ * H₂ := Nat.mul_le_mul hq.2 hr.2
      _ ≤ 2 * (H₁ * H₂) := by omega

theorem components_of_bits (q : ℚ) (S : ℕ)
    (hn : Nat.size q.num.natAbs ≤ S)
    (hd : Nat.size q.den ≤ S) :
    ComponentsWithin (2 ^ S) q := by
  constructor
  · exact (le_of_lt (Nat.lt_size_self q.num.natAbs)).trans
      (Nat.pow_le_pow_right (by omega) hn)
  · exact (le_of_lt (Nat.lt_size_self q.den)).trans
      (Nat.pow_le_pow_right (by omega) hd)

theorem clearTyped_temporary_components {m k : ℕ}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k) (S : ℕ)
    (hB : ∀ i j, ComponentsWithin (2 ^ S) (B i j))
    (hp : B r c ≠ 0) (i : Fin m) (j : Fin k) :
    ComponentsWithin (2 ^ (2 * S)) (B r j / B r c) ∧
    ComponentsWithin (2 ^ (2 * S)) (B i c / B r c) ∧
    ComponentsWithin (2 ^ (3 * S))
      ((B i c / B r c) * B r j) ∧
    ComponentsWithin (2 ^ (4 * S + 1))
      (B i j - (B i c / B r c) * B r j) ∧
    ComponentsWithin (2 ^ (4 * S + 1))
      (CurrentAdditive.SequentialTotality.clearTyped B r c i j) := by
  let H := 2 ^ S
  have hnorm := components_div (hB r j) (hB r c) hp
  have hratio := components_div (hB i c) (hB r c) hp
  have hprod := components_mul hratio (hB r j)
  have hsub := components_sub (hB i j) hprod
  have h2 : H * H = 2 ^ (2 * S) := by simp [H, ← pow_add, two_mul]
  have h3 : (H * H) * H = 2 ^ (3 * S) := by
    simp [H, ← pow_add]
    congr 1
    omega
  have h4 : 2 * (H * ((H * H) * H)) = 2 ^ (4 * S + 1) := by
    calc
      2 * (H * ((H * H) * H)) = H ^ 4 * 2 := by ring
      _ = 2 ^ (4 * S + 1) := by
        dsimp [H]
        rw [← pow_mul]
        change 2 ^ (S * 4) * 2 ^ 1 = 2 ^ (4 * S + 1)
        rw [← pow_add]
        congr 1
        omega
  have hnorm' : ComponentsWithin (2 ^ (2 * S)) (B r j / B r c) := by
    simpa [H, ← pow_add, two_mul] using hnorm
  have hratio' : ComponentsWithin (2 ^ (2 * S)) (B i c / B r c) := by
    simpa [H, ← pow_add, two_mul] using hratio
  have hprod' : ComponentsWithin (2 ^ (3 * S))
      ((B i c / B r c) * B r j) := by
    simpa [H, ← pow_add, show S + S + S = 3 * S by omega] using hprod
  have hsub' : ComponentsWithin (2 ^ (4 * S + 1))
      (B i j - (B i c / B r c) * B r j) := by
    change ComponentsWithin (2 * (H * ((H * H) * H))) _ at hsub
    rw [h4] at hsub
    exact hsub
  refine ⟨hnorm', hratio', hprod', hsub', ?_⟩
  by_cases hi : i = r
  · simpa [CurrentAdditive.SequentialTotality.clearTyped, hi] using
      (components_mono hnorm'
        (Nat.pow_le_pow_right (by omega) (by omega : 2 * S ≤ 4 * S + 1)))
  · simpa [CurrentAdditive.SequentialTotality.clearTyped, hi] using hsub'

theorem components_fits_bits (q : ℚ) (E : ℕ)
    (h : ComponentsWithin (2 ^ E) q) :
    Nat.size q.num.natAbs ≤ E + 1 ∧ Nat.size q.den ≤ E + 1 :=
  ⟨size_le_of_pow_bound h.1, size_le_of_pow_bound h.2⟩

/-- Every division, multiplication, and subtraction actually evaluated by a
successful pivot is polynomial-size. The state is the exact cursor of the
materialized loop after scanning `t` columns. -/
theorem actualPivot_temporary_bits {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : ℕ) (ht : t ≤ k)
    (hr : (cursorAfter (fun i j => (A i j : ℚ)) t).r < m)
    (hc : (cursorAfter (fun i j => (A i j : ℚ)) t).c < k)
    (p : Fin m)
    (hp : CurrentAdditive.SequentialTotality.pivotTyped
      (cursorAfter (fun i j => (A i j : ℚ)) t).B
      (cursorAfter (fun i j => (A i j : ℚ)) t).r
      ⟨(cursorAfter (fun i j => (A i j : ℚ)) t).c, hc⟩ = some p)
    (i : Fin m) (j : Fin k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    let state := cursorAfter Aq t
    let rf : Fin m := ⟨state.r, hr⟩
    let cf : Fin k := ⟨state.c, hc⟩
    let B := CurrentAdditive.SequentialTotality.swapTyped state.B rf p
    let S := (m + 3) * (m + 1) ^ 2 + 1
    let E := 4 * S + 1
    (Nat.size (B rf j / B rf cf).num.natAbs ≤ E + 1 ∧
      Nat.size (B rf j / B rf cf).den ≤ E + 1) ∧
    (Nat.size (B i cf / B rf cf).num.natAbs ≤ E + 1 ∧
      Nat.size (B i cf / B rf cf).den ≤ E + 1) ∧
    (Nat.size ((B i cf / B rf cf) * B rf j).num.natAbs ≤ E + 1 ∧
      Nat.size ((B i cf / B rf cf) * B rf j).den ≤ E + 1) ∧
    (Nat.size (B i j - (B i cf / B rf cf) * B rf j).num.natAbs ≤ E + 1 ∧
      Nat.size (B i j - (B i cf / B rf cf) * B rf j).den ≤ E + 1) ∧
    (Nat.size (CurrentAdditive.SequentialTotality.clearTyped B rf cf i j).num.natAbs
        ≤ E + 1 ∧
      Nat.size (CurrentAdditive.SequentialTotality.clearTyped B rf cf i j).den
        ≤ E + 1) := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  let state := cursorAfter Aq t
  let rf : Fin m := ⟨state.r, hr⟩
  let cf : Fin k := ⟨state.c, hc⟩
  let B := CurrentAdditive.SequentialTotality.swapTyped state.B rf p
  let S := (m + 3) * (m + 1) ^ 2 + 1
  let E := 4 * S + 1
  have hstate : ∀ i j, ComponentsWithin (2 ^ S) (state.B i j) := by
    intro u v
    have hh := every_actual_step_entry_bits A h01 t ht u v
    exact components_of_bits _ S hh.2 hh.1
  have hB : ∀ u v, ComponentsWithin (2 ^ S) (B u v) := by
    intro u v
    exact hstate (Equiv.swap rf p u) v
  have hpivot : B rf cf ≠ 0 := by
    have hh := (CurrentAdditive.SequentialTotality.pivotTyped_spec
      state.B state.r cf p hp).2
    simpa [B, CurrentAdditive.SequentialTotality.swapTyped] using hh
  obtain ⟨hnorm, hratio, hprod, hsub, hclear⟩ :=
    clearTyped_temporary_components B rf cf S hB hpivot i j
  have h21 : 2 * S ≤ E := by dsimp [E]; omega
  have h31 : 3 * S ≤ E := by dsimp [E]; omega
  have hnorm' := components_mono hnorm
    (Nat.pow_le_pow_right (by omega) h21)
  have hratio' := components_mono hratio
    (Nat.pow_le_pow_right (by omega) h21)
  have hprod' := components_mono hprod
    (Nat.pow_le_pow_right (by omega) h31)
  exact ⟨components_fits_bits _ E hnorm',
    components_fits_bits _ E hratio',
    components_fits_bits _ E hprod',
    components_fits_bits _ E hsub,
    components_fits_bits _ E hclear⟩

end CurrentAdditive.EliminationEntryBounds
