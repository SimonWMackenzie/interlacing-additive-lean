import EthInapproximability.CurrentPaper.EntryRow
import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.RawTableTail
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# Segments 3 (uniform clock) and 4 (`EntryRuns` for `encodedRaw`, writer 22)

Lane owner:b-stage4-entry-program-5 (Paper B, unit 2, map item 3).

* `itemV0`, `item_v0`: the literal start control of the (TRACE-draft)
  item branch machine at EVERY address, as one closed constant. So the one
  fixed entry program is `EntryRow.program itemV0`; nothing about the address
  is a program parameter.
* `entry_template_bounded`, `entry_item_bounded`: owner-4's per-address runs
  of that one program (`EntryRow.entry_template` / `entry_item`, whose proofs
  discarded the bound) with the explicit per-address bound kept.
* `tableT`: ONE public clock, the maximum of the per-address bounds over all
  `rows * cols` addresses (depends on the instance only, not on the address).
* `toCS`: a fixed finite renaming `ES ≃ MatrixTableWriter.CellStack K` that
  sends the row-index / column-index / answer cells to the three writer
  cells (the renaming of the other cells is the fixed classical
  `Fintype.equivFin`; a fixed finite relabelling, no input-dependent choice).
* `raw_entry_runs`: the admitted `MatrixTableWriter.EntryRuns` contract for
  the renamed program, entry function agreeing with `encodedRaw` on every
  in-range index, clock `tableT`, fixed bank `cellBank w` (the 19 common
  words; all branch regions blank).
* `raw_table_writer22_actual`: composition with the admitted
  `RawTableTail.raw_table_writer22`: `rawTable` lands in writer cell 22.

The 19 common words in `cellBank w` are still a supplied fixed bank here
(segment 5 produces them). The branch machines are TRACE drafts.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.EntryRunsRaw

open Turing BitMachineEncoding BitMachineStackEmbedding EntryLayout
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

/-! ## The one item start control -/

/-- The literal start control of the item branch machine (the same at every
address; read off from the definitions). -/
def itemV0 : MatrixStage4RowGraphMachine.Control :=
  (MatrixStage4RowMachine.initial, (none, false, (false, none), MatrixStage4AlignmentStream.initial),
    (MatrixTableLookup.initial, MatrixStage4ActiveRankMachine.initial), (false, none),
    ((false, true), false, false), (false, MatrixStage4ColumnMachine.initial),
    MatrixTableLookup.initial)

theorem item_v0 {a s q L nv nb rx cy : ℕ} (hs : 0 < s)
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx) :
    (MatrixStage4RowGraphMachine.rowFrame
      (MatrixStage4RowGraphMachine.graphSeed hs vectors R code i x [])
      (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order i x)).var = itemV0 := by
  simp only [MatrixStage4RowGraphMachine.rowFrame, MatrixStage4RowGraphMachine.graphSeed,
    BitMachineEncoding.renameCfg, BitMachineComposition.liftCfg, Equiv.refl_apply,
    MatrixStage4AlignmentVectorGraph.alignmentFrame,
    MatrixStage4AlignmentVectorGraph.pendingGraphControl,
    MatrixStage4AlignmentVectorGraph.graphInput, MatrixStage4VectorGraphSource.vectorFrame,
    MatrixStage4VectorGraphSource.pending, MatrixStage4VectorGraphSource.sourceTarget,
    MatrixStage4VectorGraphSource.sourceTargetSeed, MatrixStage4GraphTailSource.chooseFrame,
    MatrixStage4PowerTailRead.powerFrame, MatrixStage4TailSourceRead.tailFrame,
    MatrixStage4TailSourceRead.tailInput, MatrixStage4TailFromOrdinal.splitFrame,
    MatrixStage4SelectedPower.cutFrame, MatrixStage4VectorGraphSource.vectorInput,
    MatrixStage4VectorFlagRank.lookupFrame, MatrixStage4OrdinalCopyAlignment.copyFrame,
    MatrixStage4OrdinalCopyAlignment.alignmentInput, MatrixStage4AlignmentFromOrdinal.splitFrame,
    MatrixStage4RowGraphMachine.itemRowInput, MatrixStage4RowMachine.cfg, BitMachineCopy.cfg,
    MatrixUnaryDivision.cfg, MatrixTableLookup.cfg, MatrixUnaryCut.cfg]
  all_goals rfl

/-! ## The one fixed entry program, its start label and start control -/

noncomputable def program := EntryRow.program itemV0

/-- Type ascription helpers: elaborate a label / control against the
label / control type of a given program. -/
def labelOf {S Lb Vb : Type*} (_P : Lb → TM2.Stmt (fun _ : S => Bool) Lb Vb) (l : Lb) : Lb := l
def controlOf {S Lb Vb : Type*} (_P : Lb → TM2.Stmt (fun _ : S => Bool) Lb Vb) (v : Vb) : Vb := v

noncomputable def startLabel :=
  labelOf program
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))

noncomputable def startControl :=
  controlOf program
    (EntryRowVerdict.verdictInit,
      (((TemplateEntry.initial, ((), (none : Option Bool))),
        (ItemEntry.initial itemV0, ((), (none : Option Bool)))), (none : Option Bool)))

/-! ## Per-address bounds -/

/-- Per-address bound at a template row `(p, ell)`. -/
def templateAddrBound {a s q L rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx)) (vtable : List Bool)
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) : ℕ :=
  (2 * (p.val * L + ell.val) + 2) + (2 * (s * L) + 2) +
    (max (p.val * L + ell.val) (s * L) + 2) + 2 +
    (((TemplateSeeding.templateCost (TemplateEntry.actualWords a s q L cy rx R family vtable)
        (p.val * L + ell.val) code.val +
        MatrixStage4TemplateBitMachine.actualBound family code p ell + 1 + 2) +
      (Fintype.card TS *
          (EntryFull.templateSeedLen (TemplateEntry.actualWords a s q L cy rx R family vtable)
              code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val +
            BitMachineStackGrowth.perStep MatrixStage4TemplateBitMachine.program *
              MatrixStage4TemplateBitMachine.actualBound family code p ell) +
        Fintype.card TS + 2) + 1) + 1) + 1

/-- Per-address bound at an item row `(i, x)`. -/
def itemAddrBound {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx) : ℕ :=
  let X := (rowCode s L nv nb rx order ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))).val
  (2 * X + 2) + (2 * (s * L) + 2) + (max X (s * L) + 2) + 2 +
    ((((ItemSeeding.seedCost (TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors))
          X code.val + 1) +
        ItemEntry.itemBound (L := L) hs vectors cap R code i x + 3) +
      (89 * (EntryFull.itemSeedLen (a := a) (s := s) (q := q) (L := L) R (rowMajor vectors)
            code.val X +
          BitMachineStackGrowth.perStep MatrixStage4RowGraphMachine.program *
            ItemEntry.itemBound (L := L) hs vectors cap R code i x) + 89 + 2) + 1) + 1) + 1

theorem entry_template_bounded {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let w := TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors)
    let x := p.val * L + ell.val
    ∃ t ≤ templateAddrBound R family (rowMajor vectors) code p ell, ∃ v,
      ((advance program)^[t])
        (⟨some startLabel, startControl, start w x code.val []⟩ :
          TM2.Cfg (fun _ : ES => Bool) _ _) =
        ⟨none, v, start w x code.val
          [rawMatrix R a s q L nv nb hs family order vectors cap
            (.inl (p, ell)) ((rawColumnCode a s q cy).symm code)]⟩ := by
  intro w x
  obtain ⟨ta, hta, v₁, ha⟩ := EntryFull.template_full R hs family order vectors cap
    (rowMajor vectors) code p ell
  have hlt : x < s * L := by
    have h1 : p.val + 1 ≤ s := p.isLt
    have h2 : ell.val < L := ell.isLt
    calc p.val * L + ell.val < p.val * L + L := by omega
      _ = (p.val + 1) * L := by ring
      _ ≤ s * L := Nat.mul_le_mul_right L h1
  obtain ⟨t, ht, v, h⟩ := EntryRowVerdict.row_template xc (cw 17) (scr 1) (scr 2) (scr 3) (scr 4)
    EntryRow.d1 EntryRow.d2 EntryRow.d3 EntryRow.d4 EntryRow.d5 EntryRow.d6 EntryRow.d7
    EntryRow.d8 EntryRow.d9 EntryRow.d10 EntryRow.d11 EntryRow.d12 EntryRow.d13 EntryRow.d14
    EntryFull.templateProgram (EntryFull.itemProgram itemV0) _ _ _ _
    (start w x code.val []) x (s * L) rfl rfl rfl rfl rfl rfl hlt v₁ _ ta ha
  refine ⟨t, ?_, v, h⟩
  unfold templateAddrBound
  simp only [x] at ht hta
  omega

theorem entry_item_bounded {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx) :
    let w := TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors)
    let X := (rowCode s L nv nb rx order ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))).val
    ∃ t ≤ itemAddrBound R hs family order vectors cap code i x, ∃ v,
      ((advance program)^[t])
        (⟨some startLabel, startControl, start w X code.val []⟩ :
          TM2.Cfg (fun _ : ES => Bool) _ _) =
        ⟨none, v, start w X code.val
          [rawMatrix R a s q L nv nb hs family order vectors cap
            ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))
            ((rawColumnCode a s q cy).symm code)]⟩ := by
  intro w X
  obtain ⟨tb, htb, w₁, hb⟩ := EntryFull.item_full R hs family order vectors cap code i x itemV0
    (item_v0 hs order vectors R code i x)
  obtain ⟨t, ht, v, h⟩ := EntryRowVerdict.row_item xc (cw 17) (scr 1) (scr 2) (scr 3) (scr 4)
    EntryRow.d1 EntryRow.d2 EntryRow.d3 EntryRow.d4 EntryRow.d5 EntryRow.d6 EntryRow.d7
    EntryRow.d8 EntryRow.d9 EntryRow.d10 EntryRow.d11 EntryRow.d12 EntryRow.d13 EntryRow.d14
    EntryFull.templateProgram (EntryFull.itemProgram itemV0) _ _ _ _
    (start w X code.val []) X (s * L) rfl rfl rfl rfl rfl rfl
    (EntryRow.rowCode_item order i x) w₁ _ tb hb
  refine ⟨t, ?_, v, h⟩
  unfold itemAddrBound
  simp only [X] at ht htb ⊢
  omega

#print axioms item_v0
#print axioms entry_template_bounded
#print axioms entry_item_bounded

/-! ## One public clock over all addresses -/

/-- The per-address bound, by the (proof-side) decoding of the row ordinal. -/
def addrBound {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (r : Fin (rows s L nv nb rx)) (c : Fin (cols a s q cy)) : ℕ :=
  Sum.elim (fun pe : Fin s × Fin L => templateAddrBound R family (rowMajor vectors) c pe.1 pe.2)
    (fun ix : Fin (nv + nb) × Fin rx => itemAddrBound R hs family order vectors cap c ix.1 ix.2)
    (rawRowEquiv s L nv nb order ((rowCode s L nv nb rx order).symm r))

/-- ONE public per-entry clock for the whole table: the maximum of the
per-address bounds (a function of the instance only). -/
def tableT {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) : ℕ :=
  Finset.univ.sup (fun rc : Fin (rows s L nv nb rx) × Fin (cols a s q cy) =>
    addrBound R hs family order vectors cap rc.1 rc.2)

theorem addrBound_le {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (r : Fin (rows s L nv nb rx)) (c : Fin (cols a s q cy)) :
    addrBound R hs family order vectors cap r c ≤ tableT R hs family order vectors cap := by
  have h := Finset.le_sup (f := fun rc : Fin (rows s L nv nb rx) × Fin (cols a s q cy) =>
    addrBound R hs family order vectors cap rc.1 rc.2) (Finset.mem_univ (r, c))
  unfold tableT
  exact h

/-! ## Transport to the writer's cell stack -/

abbrev Rest := TS ⊕ (Fin 89 ⊕ (Fin 6 ⊕ (EntryStride.SK ⊕ Fin 8)))
abbrev Other := Fin 19 ⊕ Rest

/-- Number of non-index cells of the entry bank. -/
def K : ℕ := Fintype.card Other

/-- Fixed finite renaming of the non-index cells. -/
noncomputable def eo : Other ≃ Fin K := Fintype.equivFin Other

def split : ES ≃ Other ⊕ Fin 3 where
  toFun
    | .inl i => .inl (.inl i)
    | .inr (.inl j) => .inr j
    | .inr (.inr r) => .inl (.inr r)
  invFun
    | .inl (.inl i) => .inl i
    | .inl (.inr r) => .inr (.inr r)
    | .inr j => .inr (.inl j)
  left_inv := by
    intro e
    rcases e with i | j | r <;> rfl
  right_inv := by
    intro e
    rcases e with (i | r) | j <;> rfl

/-- The fixed renaming `ES ≃ Fin K ⊕ Fin 3`; the three index/answer cells go
to the writer's three distinguished cells. -/
noncomputable def toCS : ES ≃ MatrixTableWriter.CellStack K :=
  split.trans (Equiv.sumCongr eo (Equiv.refl _))

/-- The fixed writer bank: the 19 common words, every region blank. -/
noncomputable def cellBank (w : Words) : Fin K → List Bool :=
  fun k => Sum.elim (common w) (fun _ => []) (eo.symm k)

/-- The renamed entry program on `MatrixTableWriter.CellStack K`. -/
noncomputable def csProgram :=
  fun l => stackStmt toCS.toEmbedding (program l)

theorem start_bank (w : Words) (x y : ℕ) (ans : List Bool) :
    bank toCS.toEmbedding (fun _ => []) (start w x y ans) =
      Sum.elim (cellBank w)
        (![List.replicate x true, List.replicate y true, ans] : Fin 3 → List Bool) := by
  have h := bank_eq_self toCS.toEmbedding
    (Sum.elim (cellBank w)
      (![List.replicate x true, List.replicate y true, ans] : Fin 3 → List Bool))
    (start w x y ans)
  have hb : bank toCS.toEmbedding (fun _ => []) (start w x y ans) =
      bank toCS.toEmbedding
        (Sum.elim (cellBank w)
          (![List.replicate x true, List.replicate y true, ans] : Fin 3 → List Bool))
        (start w x y ans) := by
    funext j
    obtain ⟨e, rfl⟩ := toCS.surjective j
    exact (bank_at _ _ _ e).trans (bank_at _ _ _ e).symm
  rw [hb]
  apply h
  intro e
  rcases e with i | j | r
  · show common w i = cellBank w (eo (.inl i))
    simp [cellBank]
  · show (![rep x, rep y, ans] : Fin 3 → List Bool) j = _
    rfl
  · show ([] : List Bool) = cellBank w (eo (.inr r))
    simp [cellBank]

theorem cs_run (w : Words) (x y : ℕ) (ans ans' : List Bool) (t : ℕ) {L V : Type*}
    (P : L → TM2.Stmt (fun _ : ES => Bool) L V) (l : L) (v v' : V)
    (h : ((advance P)^[t]) (⟨some l, v, start w x y ans⟩ : TM2.Cfg (fun _ : ES => Bool) L V) =
      ⟨none, v', start w x y ans'⟩) :
    ((advance (fun l => stackStmt toCS.toEmbedding (P l)))^[t])
        (MatrixTableWriter.cellCfg (some l) v (cellBank w) x y ans) =
      MatrixTableWriter.cellCfg none v' (cellBank w) x y ans' := by
  have hr := BitMachineStackRun.run toCS.toEmbedding (fun _ => []) P
    ⟨some l, v, start w x y ans⟩ t
  rw [h] at hr
  simp only [stackCfg, start_bank] at hr
  exact hr

/-! ## `EntryRuns` for the literal raw Stage-4 entry -/

/-- Entry function: `encodedRaw` on in-range indices (and `false` outside). -/
def entry {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (x y : ℕ) : Bool :=
  if h : x < rows s L nv nb rx ∧ y < cols a s q cy then
    encodedRaw R a s q L nv nb hs family order vectors cap ⟨x, h.1⟩ ⟨y, h.2⟩
  else false

theorem entry_agrees {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (x : Fin (rows s L nv nb rx)) (y : Fin (cols a s q cy)) :
    entry R hs family order vectors cap x.val y.val =
      encodedRaw R a s q L nv nb hs family order vectors cap x y := by
  unfold entry
  rw [dif_pos ⟨x.isLt, y.isLt⟩]

theorem raw_entry_runs {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) :
    MatrixTableWriter.EntryRuns csProgram startLabel startControl
      (cellBank (TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors)))
      (rows s L nv nb rx) (cols a s q cy) (tableT R hs family order vectors cap)
      (entry R hs family order vectors cap) := by
  intro x hx y hy
  set w := TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors)
  set r := (rowCode s L nv nb rx order).symm ⟨x, hx⟩ with hr
  have hcode : rowCode s L nv nb rx order r = ⟨x, hx⟩ := Equiv.apply_symm_apply _ _
  have hent : entry R hs family order vectors cap x y =
      rawMatrix R a s q L nv nb hs family order vectors cap r
        ((rawColumnCode a s q cy).symm ⟨y, hy⟩) := by
    unfold entry
    rw [dif_pos ⟨hx, hy⟩]
    rfl
  have hbound := addrBound_le R hs family order vectors cap ⟨x, hx⟩ ⟨y, hy⟩
  rcases hsplit : rawRowEquiv s L nv nb order r with ⟨p, ell⟩ | ⟨i, x'⟩
  · -- template row
    have hrr : r = .inl (p, ell) := by
      have := congrArg (rawRowEquiv s L nv nb order).symm hsplit
      simpa using this
    have hxv : p.val * L + ell.val = x := by
      have hv := congrArg Fin.val hcode
      simp only [MatrixStage4Codes.rowCode, Equiv.trans_apply, hsplit, Equiv.sumCongr_apply,
        Sum.map_inl] at hv
      rw [← hv]
      show p.val * L + ell.val = ell.val + L * p.val
      ring
    have hb : addrBound R hs family order vectors cap ⟨x, hx⟩ ⟨y, hy⟩ =
        templateAddrBound R family (rowMajor vectors) ⟨y, hy⟩ p ell := by
      unfold addrBound
      rw [← hr, hsplit]
      rfl
    obtain ⟨t, ht, v, h⟩ := entry_template_bounded R hs family order vectors cap ⟨y, hy⟩ p ell
    refine ⟨t, by omega, v, ?_⟩
    rw [hent, hrr]
    rw [hxv] at h
    exact cs_run w x y [] _ t program startLabel startControl v h
  · -- item row
    have hrr : (rawRowEquiv s L nv nb order).symm (.inr (i, x')) = r := by
      rw [← hsplit]
      exact Equiv.symm_apply_apply _ _
    have hxv : (rowCode s L nv nb rx order
        ((rawRowEquiv s L nv nb order).symm (.inr (i, x')))).val = x := by
      rw [hrr, hcode]
    have hb : addrBound R hs family order vectors cap ⟨x, hx⟩ ⟨y, hy⟩ =
        itemAddrBound R hs family order vectors cap ⟨y, hy⟩ i x' := by
      unfold addrBound
      rw [← hr, hsplit]
      rfl
    obtain ⟨t, ht, v, h⟩ := entry_item_bounded R hs family order vectors cap ⟨y, hy⟩ i x'
    refine ⟨t, by omega, v, ?_⟩
    rw [hent, ← hrr]
    simp only [hxv] at h
    exact cs_run w x y [] _ t program startLabel startControl v h

#print axioms raw_entry_runs

/-! ## Composition with the admitted writer-22 tail -/

theorem raw_table_writer22_actual {a s q L nv nb rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (W : Fin 64 → List Bool) (hblank : W 22 = []) :
    let bank := cellBank (TemplateEntry.actualWords a s q L cy rx R family (rowMajor vectors))
    let T := tableT R hs family order vectors cap
    let word := rawTable R a s q L nv nb hs family order vectors cap
    ∃ t ≤ MatrixTableWriter.writerBound (rows s L nv nb rx) (cols a s q cy) T +
        (2 * (rows s L nv nb rx * cols a s q cy) + 2) + 1,
      ((advance (RawTableTail.program csProgram startLabel startControl))^[t])
        (⟨some RawTableTail.startLabel, RawTableTail.startControl startControl,
          RawTableTail.startBank bank (rows s L nv nb rx) (cols a s q cy) W⟩ :
          TM2.Cfg (fun _ : RawTableTail.Stack K => Bool) _ _) =
        ⟨none, ((startControl, none), none),
          RawTableTail.exitBank bank (rows s L nv nb rx) (cols a s q cy) W word⟩ ∧
      RawTableTail.exitBank bank (rows s L nv nb rx) (cols a s q cy) W word
          (Sum.inr (Sum.inl 22)) = word ∧
      (∀ k : Fin 64, k ≠ 22 →
        RawTableTail.exitBank bank (rows s L nv nb rx) (cols a s q cy) W word
          (Sum.inr (Sum.inl k)) = W k) ∧
      (∀ k : Fin K,
        RawTableTail.exitBank bank (rows s L nv nb rx) (cols a s q cy) W word
          (Sum.inl (Sum.inl (Sum.inl k))) = bank k) := by
  intro bank T word
  exact RawTableTail.raw_table_writer22 csProgram startLabel startControl R a s q L nv nb hs
    family order vectors cap bank T (entry R hs family order vectors cap)
    (entry_agrees R hs family order vectors cap)
    (raw_entry_runs R hs family order vectors cap) W hblank

#print axioms raw_table_writer22_actual

end EthInapproximability.CurrentPaper.EntryRunsRaw
