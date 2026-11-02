import EthInapproximability.CurrentPaper.ItemSeeding
import EthInapproximability.CurrentPaper.TemplateEntry

/-!
# Segment 3 (item branch, per address): seed, admitted run, answer

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3).

ONE fixed three-phase controller (two charged handoffs) on the entry bank
`ES`, parameterized only by the constant start control `v₀` of the admitted
item machine (owner-3's `ItemControl.item_control`: that control is the same
for every address): (A) the checked `ItemSeeding.program`; (B) the admitted
`MatrixStage4RowGraphMachine.program`, embedded on the item region;
(C) `EntryDispatch.moveBit` from item cell 48 to the entry answer cell `ac`.

From the per-address start bank (common words `actualWords`, unary row
index `X = (rowCode … (inr (i, x))).val`, unary column index `code.val`,
blank answer) it halts with: every common word, `X`, the column index
unchanged; answer `[rawMatrix … ((rawRowEquiv …).symm (.inr (i, x))) …]`;
template, division, stride and scratch regions blank; and the item region
equal to the admitted machine's final item bank with cell 48 emptied, each
cell bounded by its seed length plus `perStep * bound`. The region clear is
NOT done here.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.ItemEntry

open Turing BitMachineEncoding BitMachineStackEmbedding EntryLayout
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

def iEmb : Fin 89 ↪ ES := ⟨ic, fun a b h => by simpa [ic] using h⟩

def PB := fun l => stackStmt iEmb (MatrixStage4RowGraphMachine.program l)

def PC := EntryDispatch.moveBit (ic 48) ac

def qBC (v₀ : MatrixStage4RowGraphMachine.Control) :=
  BitMachineRawSequence.program PB PC () v₀ (none : Option Bool)

/-- ONE fixed item-entry controller (for the fixed start control `v₀`). -/
def program (v₀ : MatrixStage4RowGraphMachine.Control) :=
  BitMachineRawSequence.program ItemSeeding.program (qBC v₀)
    (BitMachineRawSequence.leftLabel MatrixStage4RowGraphMachine.rowStart) MultiMove.initial
    (v₀, (none : Option Bool))

def initial (v₀ : MatrixStage4RowGraphMachine.Control) :=
  (MultiMove.initial, (v₀, (none : Option Bool)))

def exitBank (w : Words) (x y : ℕ) (b : Bool) (I : Fin 89 → List Bool) : ES → List Bool :=
  Sum.elim (common w) (Sum.elim ![rep x, rep y, [b]] (Sum.elim (fun _ => [])
    (Sum.elim I (fun _ => []))))

def itemBound {a s q L nv nb rx cy : ℕ} (hs : 0 < s)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (R : Fin rx → Fin cy → Bool)
    (code : Fin (cols a s q cy)) (i : Fin (nv + nb)) (x : Fin rx) : ℕ :=
  (3 * (s * L) + 8 * (x.val + rx * i.val) + 3 * rx + 10) +
    MatrixStage4RowGraphMachine.graphBudget hs vectors cap R code i x + 1

theorem item_entry {a s q L nv nb rx cy : ℕ}
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
    ∃ t ≤ (ItemSeeding.seedCost w X code.val + 1) +
        itemBound (L := L) hs vectors cap R code i x + 3,
      ∃ v, ∃ I : Fin 89 → List Bool,
        ((advance (program v₀))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (MultiMove.startLabel (ItemSeeding.jobs.map CopyFill.toJob))),
            initial v₀, start w X code.val []⟩ : TM2.Cfg (fun _ : ES => Bool) _ _) =
          ⟨none, v, exitBank w X code.val
            (rawMatrix R a s q L nv nb hs family order vectors cap
              ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))
              ((rawColumnCode a s q cy).symm code)) I⟩ ∧
        (∀ k, (I k).length ≤
          (ItemSeed.seed (binBase a s q cy) (wordBase a s cy) (s - 1) (binBase a s q cy ^ s)
            code.val (cy ^ (s + 1)) cy (rowMajor R) [] s q (rowMajor vectors) X (s * L) L rx
              k).length +
            BitMachineStackGrowth.perStep MatrixStage4RowGraphMachine.program *
              itemBound (L := L) hs vectors cap R code i x) := by
  intro w X
  -- Phase A: seeding
  have hA := ItemSeeding.item_seeding w X code.val []
  set SA := ItemSeeding.seeded w X code.val [] with hSAdef
  -- Phase B: the admitted item machine on the item region
  obtain ⟨tB, htB, hl, hans⟩ := MatrixStage4RowGraphMachine.item_graph_run hs family order
    vectors cap R code i x []
  set src := MatrixStage4RowGraphMachine.rowFrame
    (MatrixStage4RowGraphMachine.graphSeed hs vectors R code i x [])
    (MatrixStage4RowGraphMachine.itemRowInput (s := s) (L := L) order i x) with hsrc
  have hseed : src.stk = ItemSeed.seed (binBase a s q cy) (wordBase a s cy) (s - 1)
      (binBase a s q cy ^ s) code.val (cy ^ (s + 1)) cy (rowMajor R) [] s q (rowMajor vectors)
      X (s * L) L rx :=
    ItemSeed.item_seed hs order vectors R code i x []
  have hlab := ItemControl.item_label (L := L) hs order vectors R code i x []
  have hB := BitMachineStackRun.run iEmb SA MatrixStage4RowGraphMachine.program src tB
  set c := MatrixStage4RowGraphMachine.run tB src with hc
  have hstart : stackCfg iEmb SA src =
      (⟨some MatrixStage4RowGraphMachine.rowStart, v₀, SA⟩ :
        TM2.Cfg (fun _ : ES => Bool) _ _) := by
    simp only [stackCfg]
    rw [hlab, hv]
    congr 1
    apply bank_eq_self
    intro k
    rw [hseed]
    rfl
  have hB' : ((advance PB)^[tB])
      (⟨some MatrixStage4RowGraphMachine.rowStart, v₀, SA⟩ :
        TM2.Cfg (fun _ : ES => Bool) _ _) =
      ⟨none, c.var, bank iEmb SA c.stk⟩ := by
    rw [← hstart]
    refine hB.trans ?_
    simp only [stackCfg]
    rw [show (((advance MatrixStage4RowGraphMachine.program)^[tB]) src) = c from rfl, hl]
  -- Phase C: move the answer bit
  set bit := rawMatrix R a s q L nv nb hs family order vectors cap
    ((rawRowEquiv s L nv nb order).symm (.inr (i, x)))
    ((rawColumnCode a s q cy).symm code) with hbit
  have h48 : bank iEmb SA c.stk (ic 48) = bit :: [] := by
    rw [show ic 48 = iEmb 48 from rfl, bank_at]
    exact hans
  have hC := EntryDispatch.move_run (ic 48) ac (by intro h; cases h)
    (bank iEmb SA c.stk) bit [] h48
  obtain ⟨uBC, huBC, rBC⟩ := BitMachineRawSequence.runs PB PC _ _ _ _ _ _ _ _ _ _ _ hB' hC
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs ItemSeeding.program (qBC v₀) _ _ _ _ _ _ _ _ _
    _ _ hA rBC
  refine ⟨u, ?_, (MultiMove.initial, (v₀, some bit)),
    fun k : Fin 89 => if k = (48 : Fin 89) then [] else c.stk k, ?_, ?_⟩
  · unfold itemBound
    omega
  · refine r.trans ?_
    congr 1
    funext j
    by_cases hjI : ∃ k, iEmb k = j
    · obtain ⟨k, rfl⟩ := hjI
      show Function.update (Function.update (bank iEmb SA c.stk) (ic 48) []) ac
          (bit :: bank iEmb SA c.stk ac) (ic k) = if k = (48 : Fin 89) then [] else c.stk k
      rw [Function.update_of_ne (by simp [ic, ac])]
      by_cases hk : k = (48 : Fin 89)
      · subst hk
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne (show ic k ≠ ic 48 from fun h => hk (iEmb.injective h)),
          if_neg hk]
        exact bank_at iEmb SA c.stk k
    · by_cases hja : j = ac
      · subst hja
        rw [Function.update_self, bank_outside iEmb SA c.stk ac
          (by rintro ⟨k, hk⟩; simp [iEmb, ic, ac] at hk)]
        rfl
      · have hj48 : j ≠ ic 48 := fun h => hjI ⟨48, h.symm⟩
        rw [Function.update_of_ne hja, Function.update_of_ne hj48,
          bank_outside iEmb SA c.stk j hjI]
        rcases j with j | j | j | j | j
        · rfl
        · fin_cases j
          · rfl
          · rfl
          · exact (hja (by simp [ac])).elim
        · rfl
        · exact (hjI ⟨j, rfl⟩).elim
        · rfl
  · intro k
    have hg := BitMachineStackGrowth.run_growth MatrixStage4RowGraphMachine.program src tB k
    have hm : BitMachineStackGrowth.perStep MatrixStage4RowGraphMachine.program * tB ≤
        BitMachineStackGrowth.perStep MatrixStage4RowGraphMachine.program *
          itemBound (L := L) hs vectors cap R code i x :=
      Nat.mul_le_mul_left _ htB
    rw [hseed] at hg
    by_cases hk : k = (48 : Fin 89)
    · simp only [hk, if_true, List.length_nil]
      exact Nat.zero_le _
    · simp only [hk, if_false]
      exact le_trans hg (Nat.add_le_add_left hm _)

#print axioms item_entry

end EthInapproximability.CurrentPaper.ItemEntry
