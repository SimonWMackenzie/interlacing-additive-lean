import EthInapproximability.CurrentPaper.FlatTemplateMatrix
import EthInapproximability.CurrentPaper.MatrixSourceColumnMachine

/-!
# Common polynomial bounds for the actual matrix-entry controllers

The quantities bounded here are the literal transition bounds proved by
`FlatTemplateMatrix.template_run` and `MatrixSourceColumnMachine.Gather.source_run`.
No new operation-count oracle is introduced. The scale includes the prepared
unary parameters; constructing these parameters and decoding labels remain
separate implementation obligations.
-/

namespace EthInapproximability.CurrentPaper.MatrixEntryRuntimeBounds

def scale (a d N₁ N₂ n : ℕ) : ℕ := a + 2 ^ a + d + N₁ + N₂ + n + 1

theorem read_bound {S w start size : ℕ} (hS : 1 ≤ S) (hw : w ≤ S)
    (ht : start ≤ 4 * S ^ 3) (hz : size ≤ 4 * S ^ 3) :
    FlatTemplateMatrix.readBound w start size ≤ 40 * S ^ 4 := by
  have h₁ : S ≤ S ^ 4 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 4)
  have h₂ : S ^ 2 ≤ S ^ 4 := Nat.pow_le_pow_right hS (by decide : 2 ≤ 4)
  have h₀ : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS
  calc
    FlatTemplateMatrix.readBound w start size ≤
        S * (3 * (4 * S ^ 3 + S) + 3 * (4 * S ^ 3) + 11) + 2 := by
      unfold FlatTemplateMatrix.readBound
      gcongr
    _ ≤ 40 * S ^ 4 := by nlinarith

theorem template_bound {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : ExactConstruction.FirstFamily a N₁) (C₂ : ExactConstruction.SecondFamily a d N₂)
    (v : Fin n → Fin d → Bool) (p : Fin 4) (z : Fin N₂)
    (c : ExactConstruction.Columns d N₁) :
    let q := ExactConstruction.prefixLength a
    let s₁ := (c.2 p).2.val * (q + 3)
    let s₂ := (z.val * d + (c.2 p).1.val) * a
    let data := MatrixMaterialization.storeBits C₁ C₂ v
    FlatTemplateMatrix.readBound q s₁ data.first.length +
      FlatTemplateMatrix.readBound a s₂ data.second.length + (8 * 2 ^ a + 3 * a + 10) ≤
        128 * scale a d N₁ N₂ n ^ 4 := by
  dsimp only
  have hpow : (0 : ℤ) ≤ ((2 ^ a : ℕ) : ℤ) := Int.natCast_nonneg _
  let S := scale a d N₁ N₂ n
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have haS : a ≤ S := by dsimp [S, scale]; omega
  have hwS : 2 ^ a ≤ S := by dsimp [S, scale]; omega
  have hdS : d ≤ S := by dsimp [S, scale]; omega
  have h₁S : N₁ ≤ S := by dsimp [S, scale]; omega
  have h₂S : N₂ ≤ S := by dsimp [S, scale]; omega
  have hq : ExactConstruction.prefixLength a ≤ S := by
    have h := Construction.qOne_add_two a (by omega : 1 ≤ a)
    change ExactConstruction.prefixLength a + 2 = 2 ^ a at h
    omega
  have hq3 : ExactConstruction.prefixLength a + 3 ≤ 4 * S := by omega
  have hl : (c.2 p).2.val ≤ S := (Nat.le_of_lt (c.2 p).2.isLt).trans h₁S
  have hz : z.val ≤ S := (Nat.le_of_lt z.isLt).trans h₂S
  have hα : (c.2 p).1.val ≤ S := (Nat.le_of_lt (c.2 p).1.isLt).trans hdS
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide : 2 ≤ 3)
  have h12 : S ≤ S ^ 2 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 2)
  have h14 : S ≤ S ^ 4 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 4)
  have h04 : 1 ≤ S ^ 4 := Nat.one_le_pow _ _ hS
  have hstart₁ : (c.2 p).2.val * (ExactConstruction.prefixLength a + 3) ≤ 4 * S ^ 3 := by
    have h := Nat.mul_le_mul hl hq3
    nlinarith
  have hsize₁ : (MatrixMaterialization.storeBits C₁ C₂ v).first.length ≤ 4 * S ^ 3 := by
    rw [(MatrixMaterialization.storeBits_lengths C₁ C₂ v).1]
    have h := Nat.mul_le_mul h₁S hq3
    nlinarith
  have hstart₂ : (z.val * d + (c.2 p).1.val) * a ≤ 4 * S ^ 3 := by
    have hmul : z.val * d + (c.2 p).1.val ≤ 2 * S ^ 2 := by
      have h := Nat.mul_le_mul hz hdS
      nlinarith
    have h := Nat.mul_le_mul hmul haS
    nlinarith
  have hsize₂ : (MatrixMaterialization.storeBits C₁ C₂ v).second.length ≤ 4 * S ^ 3 := by
    rw [(MatrixMaterialization.storeBits_lengths C₁ C₂ v).2.1]
    have h := Nat.mul_le_mul (Nat.mul_le_mul h₂S hdS) haS
    nlinarith
  have hread₁ := read_bound hS hq hstart₁ hsize₁
  have hread₂ := read_bound hS haS hstart₂ hsize₂
  change _ ≤ 128 * S ^ 4
  nlinarith

theorem source_bound {a d N₁ N₂ n : ℕ} (i : Fin n) (α : Fin d) :
    (i.val + 1) * (3 * (α.val + (i.val + 1) * d) + 3 * (n * d) + 2 * d + 12) + i.val + 3 ≤
      32 * scale a d N₁ N₂ n ^ 3 := by
  have hpow : (0 : ℤ) ≤ ((2 ^ a : ℕ) : ℤ) := Int.natCast_nonneg _
  let S := scale a d N₁ N₂ n
  have hS : 1 ≤ S := by dsimp [S, scale]; omega
  have hi : i.val + 1 ≤ S := by have := i.isLt; dsimp [S, scale]; omega
  have hα : α.val ≤ S := by have := α.isLt; dsimp [S, scale]; omega
  have hd : d ≤ S := by dsimp [S, scale]; omega
  have hn : n ≤ S := by dsimp [S, scale]; omega
  have h13 : S ≤ S ^ 3 := by simpa using Nat.pow_le_pow_right hS (by decide : 1 ≤ 3)
  have h23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS (by decide : 2 ≤ 3)
  have h03 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  calc
    _ ≤ S * (3 * (S + S * S) + 3 * (S * S) + 2 * S + 12) + S + 3 := by gcongr; omega
    _ ≤ 32 * S ^ 3 := by nlinarith

end EthInapproximability.CurrentPaper.MatrixEntryRuntimeBounds
