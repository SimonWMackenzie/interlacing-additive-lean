import EthInapproximability.CurrentPaper.EntryFull
import EthInapproximability.CurrentPaper.EntryRowVerdict

/-!
# Segment 3: ONE per-address entry program with the physical row verdict

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3).

`program v₀` = owner-3's `EntryRowVerdict.rowDispatch` with the unary row
index cell `xc`, the threshold cell `cw 17` (the common word `s * L`),
scratch cells `scr 1 … scr 4`, A = `EntryFull.templateProgram`, B =
`EntryFull.itemProgram v₀`. The branch is chosen physically by the verdict
`x < s * L` on the actual row index; nothing about the address is supplied.
On every template address `(p, ell)` and every item address `(i, x)` it
maps `start w X y []` to `start w X y [rawMatrix …]` exactly.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.EntryRow

open Turing BitMachineEncoding EntryLayout
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

theorem d1 : xc ≠ scr 1 := by simp [xc, scr]
theorem d2 : xc ≠ scr 3 := by simp [xc, scr]
theorem d3 : scr 1 ≠ scr 3 := by simp [scr]
theorem d4 : cw 17 ≠ scr 2 := by simp [cw, scr]
theorem d5 : cw 17 ≠ scr 3 := by simp [cw, scr]
theorem d6 : scr 2 ≠ scr 3 := by simp [scr]
theorem d7 : xc ≠ scr 4 := by simp [xc, scr]
theorem d8 : cw 17 ≠ scr 4 := by simp [cw, scr]
theorem d9 : scr 1 ≠ scr 4 := by simp [scr]
theorem d10 : scr 2 ≠ scr 4 := by simp [scr]
theorem d11 : scr 3 ≠ scr 4 := by simp [scr]
theorem d12 : scr 1 ≠ scr 2 := by simp [scr]
theorem d13 : xc ≠ scr 2 := by simp [xc, scr]
theorem d14 : cw 17 ≠ scr 1 := by simp [cw, scr]

/-- ONE fixed per-address entry program (for the fixed item start control `v₀`). -/
noncomputable def program (v₀ : MatrixStage4RowGraphMachine.Control) :=
  EntryRowVerdict.rowDispatch xc (cw 17) (scr 1) (scr 2) (scr 3) (scr 4) d1 d2 d3 d4 d5 d6
    EntryFull.templateProgram (EntryFull.itemProgram v₀)
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (MultiMove.startLabel (TemplateSeeding.jobs1.map CopyFill.toJob)))))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      (MultiMove.startLabel (ItemSeeding.jobs.map CopyFill.toJob))))
    (TemplateEntry.initial, ((), (none : Option Bool)))
    (ItemEntry.initial v₀, ((), (none : Option Bool)))

theorem entry_template {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (v₀ : MatrixStage4RowGraphMachine.Control)
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let w := TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors)
    let x := p.val * L + ell.val
    ∃ t, ∃ v,
      ((advance (program v₀))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          (EntryRowVerdict.verdictInit,
            (((TemplateEntry.initial, ((), (none : Option Bool))),
              (ItemEntry.initial v₀, ((), (none : Option Bool)))), none)),
          start w x code.val []⟩ : TM2.Cfg (fun _ : ES => Bool) _ _) =
        ⟨none, v, start w x code.val
          [rawMatrix R a s q L nv nb hs family order vectors cap
            (.inl (p, ell)) ((rawColumnCode a s q cy).symm code)]⟩ := by
  intro w x
  obtain ⟨ta, _, v₁, ha⟩ := EntryFull.template_full R hs family order vectors cap
    (rowMajor vectors) code p ell
  have hlt : x < s * L := by
    have h1 : p.val + 1 ≤ s := p.isLt
    have h2 : ell.val < L := ell.isLt
    calc p.val * L + ell.val < p.val * L + L := by omega
      _ = (p.val + 1) * L := by ring
      _ ≤ s * L := Nat.mul_le_mul_right L h1
  obtain ⟨t, _, v, h⟩ := EntryRowVerdict.row_template xc (cw 17) (scr 1) (scr 2) (scr 3) (scr 4)
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14
    EntryFull.templateProgram (EntryFull.itemProgram v₀) _ _ _ _
    (start w x code.val []) x (s * L) rfl rfl rfl rfl rfl rfl hlt v₁ _ ta ha
  exact ⟨t, v, h⟩

theorem rowCode_item {s L nv nb rx : ℕ} (order : ItemOrder nv nb)
    (i : Fin (nv + nb)) (x : Fin rx) :
    s * L ≤ (MatrixStage4Codes.rowCode s L nv nb rx order
      ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))).val := by
  simp only [MatrixStage4Codes.rowCode, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.sumCongr_apply, Sum.map_inr]
  show s * L ≤ s * L + (finProdFinEquiv (i, x)).val
  exact Nat.le_add_right _ _

theorem entry_item {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (v₀ : MatrixStage4RowGraphMachine.Control)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx)
    (hv : (MatrixStage4RowGraphMachine.rowFrame
      (MatrixStage4RowGraphMachine.graphSeed hs vectors R code i x [])
      (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order i x)).var = v₀) :
    let w := TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors)
    let X := (MatrixStage4Codes.rowCode s L nv nb rx order
      ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))).val
    ∃ t, ∃ v,
      ((advance (program v₀))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          (EntryRowVerdict.verdictInit,
            (((TemplateEntry.initial, ((), (none : Option Bool))),
              (ItemEntry.initial v₀, ((), (none : Option Bool)))), none)),
          start w X code.val []⟩ : TM2.Cfg (fun _ : ES => Bool) _ _) =
        ⟨none, v, start w X code.val
          [rawMatrix R a s q L nv nb hs family order vectors cap
            ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))
            ((rawColumnCode a s q cy).symm code)]⟩ := by
  intro w X
  obtain ⟨tb, _, w₁, hb⟩ := EntryFull.item_full R hs family order vectors cap code i x v₀ hv
  obtain ⟨t, _, v, h⟩ := EntryRowVerdict.row_item xc (cw 17) (scr 1) (scr 2) (scr 3) (scr 4)
    d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14
    EntryFull.templateProgram (EntryFull.itemProgram v₀) _ _ _ _
    (start w X code.val []) X (s * L) rfl rfl rfl rfl rfl rfl (rowCode_item order i x) w₁ _ tb hb
  exact ⟨t, v, h⟩

#print axioms entry_template
#print axioms entry_item

end EthInapproximability.CurrentPaper.EntryRow
