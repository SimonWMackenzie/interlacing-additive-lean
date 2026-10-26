import EthInapproximability.CurrentPaper.MatrixEntryRuntimeBounds
import EthInapproximability.CurrentPaper.MatrixTemplateAddressSetup

/-!
# Uniform bounds for physical entry evaluation

These inequalities bound the explicit transition and cleanup quantities of
the physical query controllers. They do not introduce an abstract evaluator
or certify an unimplemented run. The shared scale includes unary parameters
and the alphabet size; subsequent materialization uses the actual table
writer with a uniform entry bound.
-/

namespace EthInapproximability.CurrentPaper.MatrixUniformEntryBounds

abbrev scale := MatrixEntryRuntimeBounds.scale

theorem scale_bounds (a d N₁ N₂ n : ℕ) :
    let S := scale a d N₁ N₂ n
    1 ≤ S ∧ a ≤ S ∧ 2 ^ a ≤ S ∧ d ≤ S ∧ N₁ ≤ S ∧ N₂ ≤ S ∧ n ≤ S := by
  have hp : (0 : ℤ) ≤ ((2 ^ a : ℕ) : ℤ) := Int.natCast_nonneg _
  dsimp [scale, MatrixEntryRuntimeBounds.scale]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem prefix_bound {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) :
    ExactConstruction.prefixLength a ≤ scale a d N₁ N₂ n := by
  have hb := (scale_bounds a d N₁ N₂ n).2.2.1
  have h := Construction.qOne_add_two a (by omega : 1 ≤ a)
  change ExactConstruction.prefixLength a + 2 = 2 ^ a at h
  omega

theorem rows_bound (a d N₁ N₂ n : ℕ) :
    4 * N₂ + n ≤ 5 * scale a d N₁ N₂ n := by
  have hb := scale_bounds a d N₁ N₂ n
  omega

theorem columns_bound (a d N₁ N₂ n : ℕ) :
    8 * (d * N₁) ^ 4 ≤ 8 * scale a d N₁ N₂ n ^ 8 := by
  have hb := scale_bounds a d N₁ N₂ n
  have hd : d ≤ scale a d N₁ N₂ n := hb.2.2.2.1
  have hN : N₁ ≤ scale a d N₁ N₂ n := hb.2.2.2.2.1
  have hm : d * N₁ ≤ scale a d N₁ N₂ n ^ 2 := by nlinarith [Nat.mul_le_mul hd hN]
  calc
    _ ≤ 8 * (scale a d N₁ N₂ n ^ 2) ^ 4 := by gcongr
    _ = _ := by ring

theorem preparation_bound {a d N₁ N₂ n x y : ℕ}
    (hx : x < 4 * N₂ + n) (hy : y < 8 * (d * N₁) ^ 4) :
    14 * x + 66 * y + 16 * N₂ + 12 * (d * N₁) + 12 * N₁ + 12 * d + 72 ≤
      1024 * scale a d N₁ N₂ n ^ 8 := by
  let S := scale a d N₁ N₂ n
  have hb := scale_bounds a d N₁ N₂ n
  have hS : 1 ≤ S := hb.1
  have hd : d ≤ S := hb.2.2.2.1
  have hN₁ : N₁ ≤ S := hb.2.2.2.2.1
  have hN₂ : N₂ ≤ S := hb.2.2.2.2.2.1
  have hr : x ≤ 5 * S := (Nat.le_of_lt hx).trans (rows_bound a d N₁ N₂ n)
  have hc : y ≤ 8 * S ^ 8 := (Nat.le_of_lt hy).trans (columns_bound a d N₁ N₂ n)
  have hm : d * N₁ ≤ S ^ 2 := by nlinarith [Nat.mul_le_mul hd hN₁]
  have h18 : S ≤ S ^ 8 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 8)
  have h28 : S ^ 2 ≤ S ^ 8 := Nat.pow_le_pow_right hS (by decide : 2 ≤ 8)
  have h08 : 1 ≤ S ^ 8 := Nat.one_le_pow _ _ hS
  change _ ≤ 1024 * S ^ 8
  nlinarith

theorem template_address_bound {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (ell : Fin N₁) (z : Fin N₂) (alpha : Fin d) :
    MatrixTemplateAddressSetup.bound ell.val (ExactConstruction.prefixLength a + 3)
      z.val d alpha.val a + 2 * ExactConstruction.prefixLength a + 2 * a + 4 ≤
      32768 * scale a d N₁ N₂ n ^ 4 := by
  let S := scale a d N₁ N₂ n
  have hb := scale_bounds a d N₁ N₂ n
  have hS : 1 ≤ S := hb.1
  have haS : a ≤ S := hb.2.1
  have hd : d ≤ S := hb.2.2.2.1
  have hell : ell.val ≤ S := (Nat.le_of_lt ell.isLt).trans hb.2.2.2.2.1
  have hz : z.val ≤ S := (Nat.le_of_lt z.isLt).trans hb.2.2.2.2.2.1
  have halpha : alpha.val ≤ S := (Nat.le_of_lt alpha.isLt).trans hd
  have hq : ExactConstruction.prefixLength a ≤ S := prefix_bound ha
  have hsum : ell.val + (ExactConstruction.prefixLength a + 3) + z.val + d +
      alpha.val + a + 1 ≤ 10 * S := by omega
  have haddr := MatrixTemplateAddressSetup.bound_polynomial ell.val
    (ExactConstruction.prefixLength a + 3) z.val d alpha.val a
  have h3 : (ell.val + (ExactConstruction.prefixLength a + 3) + z.val + d +
      alpha.val + a + 1) ^ 3 ≤ (10 * S) ^ 3 := by gcongr
  have h34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide : 3 ≤ 4)
  have h14 : S ≤ S ^ 4 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 4)
  have h04 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS
  change _ ≤ 32768 * S ^ 4
  nlinarith

theorem template_work_bound {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (ell : Fin N₁) (z : Fin N₂) (alpha : Fin d) :
    ell.val * (ExactConstruction.prefixLength a + 3) + ExactConstruction.prefixLength a +
      (z.val * d + alpha.val) + ((z.val * d + alpha.val) * a + a) ≤
        16 * scale a d N₁ N₂ n ^ 3 := by
  let S := scale a d N₁ N₂ n
  have hb := scale_bounds a d N₁ N₂ n
  have hS : 1 ≤ S := hb.1
  have haS : a ≤ S := hb.2.1
  have hd : d ≤ S := hb.2.2.2.1
  have hell : ell.val ≤ S := (Nat.le_of_lt ell.isLt).trans hb.2.2.2.2.1
  have hz : z.val ≤ S := (Nat.le_of_lt z.isLt).trans hb.2.2.2.2.2.1
  have halpha : alpha.val ≤ S := (Nat.le_of_lt alpha.isLt).trans hd
  have hq : ExactConstruction.prefixLength a ≤ S := prefix_bound ha
  have hw : ExactConstruction.prefixLength a + 3 ≤ 4 * S := by omega
  have hfirst := Nat.mul_le_mul hell hw
  have hmid : z.val * d + alpha.val ≤ 2 * S ^ 2 := by
    have hh := Nat.mul_le_mul hz hd
    have h12 : S ≤ S ^ 2 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 2)
    nlinarith
  have hlast := Nat.mul_le_mul hmid haS
  have h13 : S ≤ S ^ 3 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 3)
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide : 2 ≤ 3)
  change _ ≤ 16 * S ^ 3
  nlinarith

end EthInapproximability.CurrentPaper.MatrixUniformEntryBounds
