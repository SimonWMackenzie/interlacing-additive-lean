import EthInapproximability.CurrentPaper.MatrixStage4TemplateFirstPair
import EthInapproximability.CurrentPaper.MatrixStage4TemplateRowField

/-!
# Physical family source-row field after first-symbol production

The first-symbol program preserves the computed family-pair address. This
fixed connector starts the actual field-address/gather/decode suffix on that
bank and a complete literal family-row table, yielding both source-row and
source-symbol unary words in one halted state.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateRowConnector

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4TemplateFirstConnector.Stack ⊕
  MatrixStage4TemplateRowField.Stack
abbrev Label := MatrixStage4TemplateFirstConnector.Label ⊕
  (Unit ⊕ MatrixStage4TemplateRowField.Label)
abbrev Control := MatrixStage4TemplateFirstConnector.Control ×
  MatrixStage4TemplateRowField.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def priorSlots : MatrixStage4TemplateFirstConnector.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def rowSlots : MatrixStage4TemplateRowField.Stack ↪ Stack where
  toFun k := if k = MatrixStage4TemplateFirstPair.fieldPairSlot then
      .inl MatrixStage4TemplateFirstPair.finalPairSlot else .inr k
  inj' := by
    intro a b h
    by_cases ha : a = MatrixStage4TemplateFirstPair.fieldPairSlot
    · subst a
      by_cases hb : b = MatrixStage4TemplateFirstPair.fieldPairSlot
      · exact hb.symm
      · simp [hb] at h
    · by_cases hb : b = MatrixStage4TemplateFirstPair.fieldPairSlot
      · subst b
        simp [ha] at h
      · simpa [ha, hb] using h

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt priorSlots Sum.inl
      (fun v => (v,MatrixStage4TemplateRowField.initial)) Prod.fst
      (some (.inr (.inl ()))) (MatrixStage4TemplateFirstConnector.program l)
  | .inr (.inl ()) => load
      (fun _ => (MatrixStage4TemplateFirstConnector.initial,
        MatrixStage4TemplateRowField.initial))
      (goto (fun _ => .inr (.inr MatrixStage4TemplateRowField.start)))
  | .inr (.inr l) => stmt rowSlots (Sum.inr ∘ Sum.inr)
      (fun v => (MatrixStage4TemplateFirstConnector.initial,v)) Prod.snd none
      (MatrixStage4TemplateFieldDecode.program l)

def start : Label := .inl MatrixStage4TemplateFirstConnector.start
def initial : Control :=
  (MatrixStage4TemplateFirstConnector.initial,MatrixStage4TemplateRowField.initial)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def extra {rows width : ℕ} (f : Fin rows → Fin width) :
    MatrixStage4TemplateRowField.Stack → List Bool :=
  MatrixStage4TemplateRowField.decodeBank 0 width
    (MatrixStage4FamilyData.fieldTable f)

def priorBank {rows width : ℕ}
    (c : MatrixStage4TemplateFirstConnector.Config)
    (f : Fin rows → Fin width) : Stack → List Bool :=
  Sum.elim c.stk (extra f)

theorem prior_bank_eq (old new : MatrixStage4TemplateFirstConnector.Stack → List Bool)
    (foreign : MatrixStage4TemplateRowField.Stack → List Bool) :
    bank priorSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at priorSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem prior_phase (l : MatrixStage4TemplateFirstConnector.Label)
    (v : MatrixStage4TemplateFirstConnector.Control)
    (S : MatrixStage4TemplateFirstConnector.Stack → List Bool)
    {rows width : ℕ} (f : Fin rows → Fin width) (B : ℕ)
    (hhalt : (MatrixStage4TemplateFirstConnector.run B ⟨some l,v,S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l))
        (v,MatrixStage4TemplateRowField.initial)
        (priorBank ⟨some l,v,S⟩ f)) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4TemplateFirstConnector.run B ⟨some l,v,S⟩).var,
          MatrixStage4TemplateRowField.initial)
        (priorBank (MatrixStage4TemplateFirstConnector.run B ⟨some l,v,S⟩)
          f) := by
  let c : MatrixStage4TemplateFirstConnector.Config := ⟨some l,v,S⟩
  have hp (u : MatrixStage4TemplateFirstConnector.Label) :
      program (.inl u) = stmt priorSlots Sum.inl
        (fun w => (w,MatrixStage4TemplateRowField.initial)) Prod.fst
        (some (.inr (.inl ())))
        (MatrixStage4TemplateFirstConnector.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs priorSlots (priorBank c f)
    Sum.inl (fun w => (w,MatrixStage4TemplateRowField.initial)) Prod.fst
    (by intro w; rfl) (some (.inr (.inl ())))
    MatrixStage4TemplateFirstConnector.program program hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4TemplateFirstConnector.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4TemplateFirstConnector.run, priorBank, c, prior_bank_eq,
    hhalt'] using he

theorem bridge (v : MatrixStage4TemplateFirstConnector.Control)
    (S : Stack → List Bool) :
    run 1 (cfg (some (.inr (.inl ())))
      (v,MatrixStage4TemplateRowField.initial) S) =
    cfg (some (.inr (.inr MatrixStage4TemplateRowField.start)))
      initial S := by
  simp [run, cfg, initial, advance, TM2.step, TM2.stepAux, program]

theorem extra_matches {rows width : ℕ} (f : Fin rows → Fin width)
    (r : Fin rows) (k : MatrixStage4TemplateRowField.Stack)
    (hk : k ≠ MatrixStage4TemplateFirstPair.fieldPairSlot) :
    extra f k =
      (MatrixStage4TemplateRowField.input f r).stk k := by
  change MatrixStage4TemplateRowField.decodeBank 0 width
      (MatrixStage4FamilyData.fieldTable f) k =
    MatrixStage4TemplateRowField.decodeBank r.val width
      (MatrixStage4FamilyData.fieldTable f) k
  cases k with
  | inr j =>
      fin_cases j <;>
        simp [extra, MatrixStage4TemplateRowField.input,
          MatrixStage4TemplateRowField.decodeBank]
  | inl k =>
      cases k with
      | inr j =>
          fin_cases j <;>
            simp [extra, MatrixStage4TemplateRowField.input,
              MatrixStage4TemplateRowField.decodeBank,
              MatrixStage4TemplateRowField.gatherBank]
      | inl k =>
          cases k with
          | inr j =>
              fin_cases j <;>
                simp [extra, MatrixStage4TemplateRowField.input,
                  MatrixStage4TemplateRowField.decodeBank,
                  MatrixStage4TemplateRowField.gatherBank,
                  MatrixStage4TemplateRowField.addressBank,
                  MatrixStage4TemplateFieldStart.extra]
          | inl k =>
              cases k with
              | inl j =>
                  fin_cases j <;>
                    simp [extra, MatrixStage4TemplateRowField.input,
                      MatrixStage4TemplateRowField.decodeBank,
                      MatrixStage4TemplateRowField.gatherBank,
                      MatrixStage4TemplateRowField.addressBank,
                      MatrixStage4TemplateRowField.entryBank]
              | inr j =>
                  fin_cases j <;>
                    simp_all [extra, MatrixStage4TemplateRowField.input,
                      MatrixStage4TemplateRowField.decodeBank,
                      MatrixStage4TemplateRowField.gatherBank,
                      MatrixStage4TemplateRowField.addressBank,
                      MatrixStage4TemplateRowField.entryBank,
                      MatrixStage4TemplateRowField.pairExtra,
                      MatrixStage4TemplateFirstPair.fieldPairSlot]

theorem row_input_pair {rows width : ℕ}
    (f : Fin rows → Fin width) (r : Fin rows) :
    (MatrixStage4TemplateRowField.input f r).stk
      MatrixStage4TemplateFirstPair.fieldPairSlot =
        List.replicate r.val true := by
  simp [MatrixStage4TemplateRowField.input,
    MatrixStage4TemplateRowField.decodeBank,
    MatrixStage4TemplateRowField.gatherBank,
    MatrixStage4TemplateRowField.addressBank,
    MatrixStage4TemplateRowField.entryBank,
    MatrixStage4TemplateRowField.pairExtra,
    MatrixStage4TemplateFirstPair.fieldPairSlot,
    MatrixStage4TemplateFieldDecode.cfg]

theorem row_phase (S : Stack → List Bool)
    (c : MatrixStage4TemplateRowField.Config) (B : ℕ)
    (hstart : c.l = some MatrixStage4TemplateRowField.start)
    (hinput : ∀ k : MatrixStage4TemplateRowField.Stack,
      S (rowSlots k) = c.stk k)
    (hhalt : (MatrixStage4TemplateRowField.run B c).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inr (.inr MatrixStage4TemplateRowField.start)))
        (MatrixStage4TemplateFirstConnector.initial,c.var) S) =
      cfg none
        (MatrixStage4TemplateFirstConnector.initial,
          (MatrixStage4TemplateRowField.run B c).var)
        (bank rowSlots S (MatrixStage4TemplateRowField.run B c).stk) := by
  have hp (u : MatrixStage4TemplateRowField.Label) :
      program (.inr (.inr u)) = stmt rowSlots (Sum.inr ∘ Sum.inr)
        (fun v => (MatrixStage4TemplateFirstConnector.initial,v)) Prod.snd none
        (MatrixStage4TemplateFieldDecode.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs rowSlots S (Sum.inr ∘ Sum.inr)
    (fun v => (MatrixStage4TemplateFirstConnector.initial,v)) Prod.snd
    (by intro v; rfl) none MatrixStage4TemplateFieldDecode.program program
    hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hbank : bank rowSlots S c.stk = S :=
    bank_eq_self rowSlots S c.stk (by intro k; exact (hinput k).symm)
  have hhalt' : (((advance MatrixStage4TemplateFieldDecode.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4TemplateRowField.run, hbank, hstart, hhalt'] using he

noncomputable def actualSource {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) : Config :=
  cfg (some start) initial
    (priorBank
      (MatrixStage4TemplateFirstConnector.actualSource family code p ell)
      (MatrixStage4FamilyData.familyRow family))

def actualBound {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) : ℕ :=
  MatrixStage4TemplateFirstConnector.actualBound family code p ell + 1 +
    MatrixStage4TemplateRowField.decodeBound
      (MatrixStage4FamilyData.familyRow family)
      (MatrixStage4TemplateFieldGather.selectedRow code p ell)

theorem actual_row_and_symbol {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let γ := (((rawColumnCode a s q cy).symm code).2 p).2
    let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
    let x := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).2
    ∃ t ≤ actualBound family code p ell,
      (run t (actualSource family code p ell)).l = none ∧
      (run t (actualSource family code p ell)).stk (.inl (.inr 23)) =
        List.replicate (γ (firstCoordinate a s j)).val true ∧
      (run t (actualSource family code p ell)).stk (.inr (.inr 0)) =
        List.replicate x.val true := by
  dsimp
  let γ := (((rawColumnCode a s q cy).symm code).2 p).2
  let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
  let x := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).2
  let r := MatrixStage4TemplateFieldGather.selectedRow code p ell
  let f := MatrixStage4FamilyData.familyRow family
  let c₁ := MatrixStage4TemplateFirstConnector.actualSource family code p ell
  obtain ⟨tp,htp,hhalt,hsymbol,hpair⟩ :=
    MatrixStage4TemplateFirstPair.actual_first_symbol_pair family code p ell
  have hhalt' : (MatrixStage4TemplateFirstConnector.run tp c₁).l = none := by
    simpa only [c₁] using hhalt
  have hsymbol' : (MatrixStage4TemplateFirstConnector.run tp c₁).stk
      (.inr 23) = List.replicate (γ (firstCoordinate a s j)).val true := by
    simpa only [c₁, γ, j] using hsymbol
  have hpair' : (MatrixStage4TemplateFirstConnector.run tp c₁).stk
      MatrixStage4TemplateFirstPair.finalPairSlot =
        List.replicate r.val true := by
    simpa only [c₁, r, MatrixStage4TemplateFieldGather.selectedRow_val]
      using hpair
  obtain ⟨t₁,ht₁,h₁⟩ := prior_phase
    MatrixStage4TemplateFirstConnector.start
    MatrixStage4TemplateFirstConnector.initial c₁.stk f tp hhalt'
  have h₁' : run t₁ (actualSource family code p ell) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4TemplateFirstConnector.run tp c₁).var,
          MatrixStage4TemplateRowField.initial)
        (priorBank (MatrixStage4TemplateFirstConnector.run tp c₁) f) := by
    simpa only [actualSource, start, initial, c₁] using h₁
  let S := priorBank (MatrixStage4TemplateFirstConnector.run tp c₁) f
  let cRow := MatrixStage4TemplateRowField.input f r
  have hinput : ∀ k : MatrixStage4TemplateRowField.Stack,
      S (rowSlots k) = cRow.stk k := by
    intro k
    by_cases hk : k = MatrixStage4TemplateFirstPair.fieldPairSlot
    · subst k
      simpa only [S, cRow, priorBank, rowSlots, if_pos rfl,
        Sum.elim_inl, MatrixStage4TemplateFirstPair.finalPairSlot,
        row_input_pair] using hpair'
    · simpa [S, cRow, priorBank, rowSlots, hk] using
        extra_matches f r k hk
  obtain ⟨tr,htr,hrun,hrow⟩ := MatrixStage4TemplateRowField.output f r
  have hrow' : (MatrixStage4TemplateRowField.run tr cRow).stk (.inr 0) =
      List.replicate x.val true := by
    have hfx : f r = x := by
      simpa only [f, r, x, MatrixStage4TemplateFieldGather.selectedRow] using
        MatrixStage4FamilyData.familyRow_at family ell
          (MatrixStage4TemplateFieldGather.selectedFin code p)
    simpa only [cRow, hfx] using hrow
  have hstart : cRow.l = some MatrixStage4TemplateRowField.start := rfl
  have hvar : cRow.var = MatrixStage4TemplateRowField.initial := rfl
  have hhaltRow : (MatrixStage4TemplateRowField.run tr cRow).l = none := by
    simpa only [cRow] using hrun
  obtain ⟨t₂,ht₂,h₂⟩ := row_phase S cRow tr hstart hinput hhaltRow
  have h12 := run_add h₁' 1
  rw [bridge] at h12
  have h123 := run_add h12 t₂
  change run (t₁+1+t₂) (actualSource family code p ell) =
    run t₂ (cfg (some (.inr (.inr MatrixStage4TemplateRowField.start)))
      (MatrixStage4TemplateFirstConnector.initial,
        MatrixStage4TemplateRowField.initial) S) at h123
  rw [← hvar, h₂] at h123
  refine ⟨t₁+1+t₂, by dsimp [actualBound, f, r] at htp htr ⊢; omega,
    ?_, ?_, ?_⟩
  · rw [h123]
    rfl
  · rw [h123]
    simp only [cfg]
    have ho :
        bank rowSlots S (MatrixStage4TemplateRowField.run tr cRow).stk
          (.inl (.inr 23)) = S (.inl (.inr 23)) :=
      bank_outside rowSlots S _ (.inl (.inr 23)) (by decide)
    rw [ho]
    simpa only [S, priorBank, Sum.elim_inl] using hsymbol'
  · rw [h123]
    have ho := bank_at rowSlots S
      (MatrixStage4TemplateRowField.run tr cRow).stk (.inr 0)
    simpa only [cfg, rowSlots, if_neg (by decide :
      (.inr (0 : Fin 1)) ≠ MatrixStage4TemplateFirstPair.fieldPairSlot),
      hrow'] using ho

end EthInapproximability.CurrentPaper.MatrixStage4TemplateRowConnector
