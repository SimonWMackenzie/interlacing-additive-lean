import EthInapproximability.CurrentPaper.TemplateSeeding
import EthInapproximability.CurrentPaper.EntryDispatch
import EthInapproximability.CurrentPaper.ItemControl
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
# Segment 3 (template branch, per address): seed, admitted run, answer

Lane owner:b-stage4-entry-program-4 (Paper B, unit 2, map item 3).

ONE fixed three-phase controller (two charged handoffs) on the entry bank
`ES`: (A) the checked `TemplateSeeding.program`; (B) the admitted
`MatrixStage4TemplateBitMachine.program`, embedded on the template region;
(C) owner-3's `EntryDispatch.moveBit` from the template answer cell
`.inr 5` to the entry answer cell `ac`.

From the per-address start bank (common words = the admitted level values
`actualWords`, unary row index `x = p * L + ell`, unary column index
`y = code.val`, blank answer) it halts with: every common word, `x`, `y`
unchanged; answer cell `[rawMatrix … (.inl (p, ell)) ((rawColumnCode …).symm code)]`;
division, stride, item and scratch regions blank; and the template region
equal to the admitted machine's final template bank with its answer cell
emptied, each cell bounded by its seed length plus
`perStep * actualBound`. Clearing that region (from this bound) is the next
step and is NOT done here.
-/

set_option maxRecDepth 16384

namespace EthInapproximability.CurrentPaper.TemplateEntry

open Turing BitMachineEncoding BitMachineStackEmbedding EntryLayout
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

/-- The common words at their admitted values (the four item-only fields
`vtable` and the rest are the item branch's; here `vtable` is a parameter). -/
def actualWords (a s q L cy rx : ℕ) (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx)) (vtable : List Bool) : Words where
  binB := binBase a s q cy
  wordB := wordBase a s cy
  binPowS := binBase a s q cy ^ s
  q := q
  qOne := qOne a
  firstTable := MatrixStage4FamilyData.fieldTable (MatrixStage4FamilyData.familyFirst family)
  cy := cy
  firstExp := firstLength a s - 1
  cyPowF := cy ^ firstLength a s
  rx := rx
  rowTable := MatrixStage4FamilyData.fieldTable (MatrixStage4FamilyData.familyRow family)
  Rtable := rowMajor R
  s := s
  sM1 := s - 1
  cyPow1 := cy ^ (s + 1)
  vtable := vtable
  sL := s * L
  L := L

def tEmb : TS ↪ ES := ⟨tc, fun a b h => by simpa [tc] using h⟩

def PB := fun l => stackStmt tEmb (MatrixStage4TemplateBitMachine.program l)

def PC := EntryDispatch.moveBit (tc (.inr 5)) ac

def qBC := BitMachineRawSequence.program PB PC () MatrixStage4TemplateBitMachine.initial
  (none : Option Bool)

/-- ONE fixed template-entry controller. -/
def program := BitMachineRawSequence.program TemplateSeeding.program qBC
  (BitMachineRawSequence.leftLabel MatrixStage4TemplateBitMachine.start) TemplateSeeding.initial
  (MatrixStage4TemplateBitMachine.initial, (none : Option Bool))

def initial := (TemplateSeeding.initial, (MatrixStage4TemplateBitMachine.initial,
  (none : Option Bool)))

theorem div_mod_eq {L : ℕ} (p : ℕ) (ell : Fin L) :
    (p * L + ell.val) / L = p ∧ (p * L + ell.val) % L = ell.val := by
  have hL : 0 < L := Nat.lt_of_le_of_lt (Nat.zero_le _) ell.isLt
  exact (Nat.div_mod_unique hL).mpr ⟨by ring, ell.isLt⟩

/-- Final bank shape: everything as at the start except the answer cell and
the template region `T`. -/
def exitBank (w : Words) (x y : ℕ) (b : Bool) (T : TS → List Bool) : ES → List Bool :=
  Sum.elim (common w) (Sum.elim ![rep x, rep y, [b]] (Sum.elim T (fun _ => [])))

theorem template_entry {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s) (vtable : List Bool)
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let w := actualWords a s q L cy rx R family vtable
    let x := p.val * L + ell.val
    ∃ t ≤ TemplateSeeding.templateCost w x code.val +
        MatrixStage4TemplateBitMachine.actualBound family code p ell + 1 + 2,
      ∃ v, ∃ T : TS → List Bool,
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
              (MultiMove.startLabel (TemplateSeeding.jobs1.map CopyFill.toJob)))),
            initial, start w x code.val []⟩ : TM2.Cfg (fun _ : ES => Bool) _ _) =
          ⟨none, v, exitBank w x code.val
            (rawMatrix R a s q L nv nb hs family order vectors cap
              (.inl (p, ell)) ((rawColumnCode a s q cy).symm code)) T⟩ ∧
        (∀ k, (T k).length ≤
          (TemplateSeeding.seedT w code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val k).length +
            BitMachineStackGrowth.perStep MatrixStage4TemplateBitMachine.program *
              MatrixStage4TemplateBitMachine.actualBound family code p ell) := by
  intro w x
  obtain ⟨hdiv, hmod⟩ := div_mod_eq (L := L) p.val ell
  -- Phase A: seeding
  obtain ⟨tA, htA, hA⟩ := TemplateSeeding.template_seeding w x code.val []
  have hSA : TemplateSeeding.seeded w x code.val [] =
      Sum.elim (common w) (Sum.elim ![rep x, rep code.val, []]
        (Sum.elim (TemplateSeeding.seedT w code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val)
          (fun _ => []))) := by
    have e1 : x / w.L = p.val := hdiv
    have e2 : x % w.L = ell.val := hmod
    simp only [TemplateSeeding.seeded]
    rw [e1, e2]
    rfl
  rw [hSA] at hA
  set SA := Sum.elim (common w) (Sum.elim ![rep x, rep code.val, []]
        (Sum.elim (TemplateSeeding.seedT w code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val)
          (fun _ => []))) with hSAdef
  -- Phase B: the admitted template machine on the template region
  obtain ⟨tB, htB, hl, hans⟩ := MatrixStage4TemplateBitMachine.actual_raw_template R hs family
    order vectors cap code p ell
  set src := MatrixStage4TemplateBitMachine.actualSource R family code p ell with hsrc
  have hseed : src.stk =
      TemplateSeeding.seedT w code.val (binBase a s q cy ^ (s - 1 - p.val)) ell.val :=
    TemplateSeed.template_seed R family code p ell
  have hctl := ItemControl.template_control R family code p ell
  have hB := BitMachineStackRun.run tEmb SA MatrixStage4TemplateBitMachine.program src tB
  set c := MatrixStage4TemplateBitMachine.run tB src with hc
  have hstart : stackCfg tEmb SA src =
      (⟨some MatrixStage4TemplateBitMachine.start, MatrixStage4TemplateBitMachine.initial, SA⟩ :
        TM2.Cfg (fun _ : ES => Bool) _ _) := by
    simp only [stackCfg]
    congr 1
    apply bank_eq_self
    intro k
    rw [hseed]
    rfl
  have hB' : ((advance PB)^[tB])
      (⟨some MatrixStage4TemplateBitMachine.start, MatrixStage4TemplateBitMachine.initial, SA⟩ :
        TM2.Cfg (fun _ : ES => Bool) _ _) =
      ⟨none, c.var, bank tEmb SA c.stk⟩ := by
    rw [← hstart]
    refine hB.trans ?_
    simp only [stackCfg]
    rw [show (((advance MatrixStage4TemplateBitMachine.program)^[tB]) src) = c from rfl, hl]
  -- Phase C: move the answer bit
  set bit := rawMatrix R a s q L nv nb hs family order vectors cap
    (.inl (p, ell)) ((rawColumnCode a s q cy).symm code) with hbit
  have h5 : bank tEmb SA c.stk (tc (.inr 5)) = bit :: [] := by
    rw [show tc (.inr 5) = tEmb (.inr 5) from rfl, bank_at]
    exact hans
  have hC := EntryDispatch.move_run (tc (.inr 5)) ac (by intro h; cases h)
    (bank tEmb SA c.stk) bit [] h5
  -- compose B;C then A;(B;C)
  obtain ⟨uBC, huBC, rBC⟩ := BitMachineRawSequence.runs PB PC _ _ _ _ _ _ _ _ _ _ _ hB' hC
  obtain ⟨u, hu, r⟩ := BitMachineRawSequence.runs TemplateSeeding.program qBC _ _ _ _ _ _ _ _ _
    _ _ hA rBC
  refine ⟨u, by omega, (TemplateSeeding.initial, (MatrixStage4TemplateBitMachine.initial, some bit)),
    fun k : TS => if k = (Sum.inr 5 : TS) then [] else c.stk k, ?_, ?_⟩
  · refine r.trans ?_
    congr 1
    funext j
    by_cases hjT : ∃ k, tEmb k = j
    · obtain ⟨k, rfl⟩ := hjT
      show Function.update (Function.update (bank tEmb SA c.stk) (tc (.inr 5)) []) ac
          (bit :: bank tEmb SA c.stk ac) (tc k) = if k = (Sum.inr 5 : TS) then [] else c.stk k
      rw [Function.update_of_ne (by simp [tc, ac])]
      by_cases hk : k = (Sum.inr 5 : TS)
      · subst hk
        rw [Function.update_self]
        rfl
      · rw [Function.update_of_ne (show tc k ≠ tc (Sum.inr 5) from fun h => hk (tEmb.injective h)),
          if_neg hk]
        exact bank_at tEmb SA c.stk k
    · by_cases hja : j = ac
      · subst hja
        rw [Function.update_self, bank_outside tEmb SA c.stk ac
          (by rintro ⟨k, hk⟩; simp [tEmb, tc, ac] at hk)]
        rfl
      · have hj5 : j ≠ tc (.inr 5) := fun h => hjT ⟨.inr 5, h.symm⟩
        rw [Function.update_of_ne hja, Function.update_of_ne hj5,
          bank_outside tEmb SA c.stk j hjT]
        rcases j with j | j | j | j
        · rfl
        · fin_cases j
          · rfl
          · rfl
          · exact (hja (by simp [ac])).elim
        · exact (hjT ⟨j, rfl⟩).elim
        · rfl
  · intro k
    have hg := BitMachineStackGrowth.run_growth MatrixStage4TemplateBitMachine.program src tB k
    have hm : BitMachineStackGrowth.perStep MatrixStage4TemplateBitMachine.program * tB ≤
        BitMachineStackGrowth.perStep MatrixStage4TemplateBitMachine.program *
          MatrixStage4TemplateBitMachine.actualBound family code p ell :=
      Nat.mul_le_mul_left _ htB
    rw [hseed] at hg
    by_cases hk : k = (Sum.inr 5 : TS)
    · simp only [hk, if_true, List.length_nil]
      exact Nat.zero_le _
    · simp only [hk, if_false]
      exact le_trans hg (Nat.add_le_add_left hm _)

#print axioms template_entry

end EthInapproximability.CurrentPaper.TemplateEntry
