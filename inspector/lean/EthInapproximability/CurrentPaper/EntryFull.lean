import EthInapproximability.CurrentPaper.ItemEntry
import EthInapproximability.CurrentPaper.RegionClear

/-!
# Segment 3: complete per-address branch runs (seed, admitted run, answer, clear)

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3).

Each branch program is followed (one charged handoff) by the charged clear
of its whole region (`RegionClear.region_clear`, bound from the cell-wise
growth bound of `TemplateEntry`/`ItemEntry`). The result is the EXACT
start bank with the answer cell set to the literal raw Stage-4 entry:
`start w x y [] ↦ start w x y [rawMatrix …]`. Only the finite control is
existential.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.EntryFull

open Turing BitMachineEncoding BitMachineStackEmbedding EntryLayout
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

/-! ## Item branch -/

noncomputable def itemProgram (v₀ : MatrixStage4RowGraphMachine.Control) :=
  BitMachineRawSequence.program (ItemEntry.program v₀)
    (RegionClear.prog (Fintype.card (Fin 89)) (RegionClear.regionBank ItemEntry.iEmb))
    (0 : Fin (Fintype.card (Fin 89) + 2)) (ItemEntry.initial v₀) ((), (none : Option Bool))

def itemSeedLen {a s q L cy rx : ℕ} (R : Fin rx → Fin cy → Bool) (vtable : List Bool)
    (code : ℕ) (X : ℕ) : ℕ :=
  ∑ k : Fin 89, (ItemSeed.seed (binBase a s q cy) (wordBase a s cy) (s - 1)
    (binBase a s q cy ^ s) code (cy ^ (s + 1)) cy (rowMajor R) [] s q vtable X (s * L) L rx
      k).length

theorem item_full {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx)
    (v₀ : MatrixStage4RowGraphMachine.Control)
    (hv : (MatrixStage4RowGraphMachine.rowFrame
      (MatrixStage4RowGraphMachine.graphSeed hs vectors R code i x [])
      (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order i x)).var = v₀) :
    let w := TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors)
    let X := (rowCode s L nv nb rx order ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))).val
    let B := itemSeedLen (a := a) (s := s) (q := q) (L := L) R (rowMajor vectors) code.val X +
      BitMachineStackGrowth.perStep MatrixStage4RowGraphMachine.program *
        ItemEntry.itemBound (L := L) hs vectors cap R code i x
    ∃ t ≤ ((ItemSeeding.seedCost w X code.val + 1) +
        ItemEntry.itemBound (L := L) hs vectors cap R code i x + 3) + (89 * B + 89 + 2) + 1,
      ∃ v,
        ((advance (itemProgram v₀))^[t])
          (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
              (MultiMove.startLabel (ItemSeeding.jobs.map CopyFill.toJob)))),
            (ItemEntry.initial v₀, ((), none)), start w X code.val []⟩ :
            TM2.Cfg (fun _ : ES => Bool) _ _) =
          ⟨none, v, start w X code.val
            [rawMatrix R a s q L nv nb hs family order vectors cap
              ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))
              ((rawColumnCode a s q cy).symm code)]⟩ := by
  intro w X B
  obtain ⟨t1, ht1, v1, I, h1, hI⟩ := ItemEntry.item_entry R hs family order vectors cap code i x
    v₀ hv
  set bit := rawMatrix R a s q L nv nb hs family order vectors cap
    ((rawRowEquiv s L nv nb order).symm (.inr (i, x))) ((rawColumnCode a s q cy).symm code)
  have hB : ∀ r, (ItemEntry.exitBank w X code.val bit I (ItemEntry.iEmb r)).length ≤ B := by
    intro r
    have hr := hI r
    have hs1 : (ItemSeed.seed (binBase a s q cy) (wordBase a s cy) (s - 1)
        (binBase a s q cy ^ s) code.val (cy ^ (s + 1)) cy (rowMajor R) [] s q (rowMajor vectors)
          X (s * L) L rx r).length ≤
        itemSeedLen (a := a) (s := s) (q := q) (L := L) R (rowMajor vectors) code.val X :=
      Finset.single_le_sum (f := fun k : Fin 89 => (ItemSeed.seed (binBase a s q cy)
        (wordBase a s cy) (s - 1) (binBase a s q cy ^ s) code.val (cy ^ (s + 1)) cy (rowMajor R) []
          s q (rowMajor vectors) X (s * L) L rx k).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    show (I r).length ≤ B
    simp only [B, X] at hr hs1 ⊢
    omega
  obtain ⟨t2, ht2, h2⟩ := RegionClear.region_clear ItemEntry.iEmb
    (ItemEntry.exitBank w X code.val bit I) B hB
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs (ItemEntry.program v₀)
    (RegionClear.prog (Fintype.card (Fin 89)) (RegionClear.regionBank ItemEntry.iEmb))
    _ _ _ _ _ _ _ _ _ _ _ h1 h2
  refine ⟨u, ?_, (ItemEntry.initial v₀, ((), (none : Option Bool))), r.trans ?_⟩
  · simp only [Fintype.card_fin] at ht2
    simp only [w, X] at ht1 ⊢
    omega
  · congr 1
    funext j
    by_cases hj : ∃ k, ItemEntry.iEmb k = j
    · obtain ⟨k, rfl⟩ := hj
      rw [if_pos ⟨k, rfl⟩]
      rfl
    · rw [if_neg hj]
      rcases j with j | j | j | j | j
      · rfl
      · rfl
      · rfl
      · exact (hj ⟨j, rfl⟩).elim
      · rfl

#print axioms item_full

/-! ## Template branch -/

noncomputable def templateProgram :=
  BitMachineRawSequence.program TemplateEntry.program
    (RegionClear.prog (Fintype.card TS) (RegionClear.regionBank TemplateEntry.tEmb))
    (0 : Fin (Fintype.card TS + 2)) TemplateEntry.initial ((), (none : Option Bool))

def templateSeedLen (w : Words) (y st ell : ℕ) : ℕ :=
  ∑ k : TS, (TemplateSeeding.seedT w y st ell k).length

theorem template_full {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (vtable : List Bool)
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let w := TemplateEntry.actualWords a s q L cy rx R family vtable
    let x := p.val * L + ell.val
    let B := templateSeedLen w code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val +
      BitMachineStackGrowth.perStep MatrixStage4TemplateBitMachine.program *
        MatrixStage4TemplateBitMachine.actualBound family code p ell
    ∃ t ≤ (TemplateSeeding.templateCost w x code.val +
        MatrixStage4TemplateBitMachine.actualBound family code p ell + 1 + 2) +
        (Fintype.card TS * B + Fintype.card TS + 2) + 1,
      ∃ v,
        ((advance templateProgram)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (MultiMove.startLabel (TemplateSeeding.jobs1.map CopyFill.toJob))))),
            (TemplateEntry.initial, ((), none)), start w x code.val []⟩ :
            TM2.Cfg (fun _ : ES => Bool) _ _) =
          ⟨none, v, start w x code.val
            [rawMatrix R a s q L nv nb hs family order vectors cap
              (.inl (p, ell)) ((rawColumnCode a s q cy).symm code)]⟩ := by
  intro w x B
  obtain ⟨t1, ht1, v1, T, h1, hT⟩ := TemplateEntry.template_entry R hs family order vectors cap
    vtable code p ell
  set bit := rawMatrix R a s q L nv nb hs family order vectors cap
    (.inl (p, ell)) ((rawColumnCode a s q cy).symm code)
  have hB : ∀ r, (TemplateEntry.exitBank w x code.val bit T (TemplateEntry.tEmb r)).length ≤ B := by
    intro r
    have hr := hT r
    have hs1 : (TemplateSeeding.seedT w code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val
        r).length ≤ templateSeedLen w code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val :=
      Finset.single_le_sum (f := fun k : TS => (TemplateSeeding.seedT w code.val
        (binBase a s q cy ^ (s - 1 - p.val)) ell.val k).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
    show (T r).length ≤ B
    simp only [B, w] at hr hs1 ⊢
    omega
  obtain ⟨t2, ht2, h2⟩ := RegionClear.region_clear TemplateEntry.tEmb
    (TemplateEntry.exitBank w x code.val bit T) B hB
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs TemplateEntry.program
    (RegionClear.prog (Fintype.card TS) (RegionClear.regionBank TemplateEntry.tEmb))
    _ _ _ _ _ _ _ _ _ _ _ h1 h2
  refine ⟨u, ?_, (TemplateEntry.initial, ((), (none : Option Bool))), r.trans ?_⟩
  · simp only [w, x] at ht1 ⊢
    omega
  congr 1
  funext j
  by_cases hj : ∃ k, TemplateEntry.tEmb k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [if_pos ⟨k, rfl⟩]
    rfl
  · rw [if_neg hj]
    rcases j with j | j | j | j
    · rfl
    · rfl
    · exact (hj ⟨j, rfl⟩).elim
    · rfl

#print axioms template_full

end EthInapproximability.CurrentPaper.EntryFull
