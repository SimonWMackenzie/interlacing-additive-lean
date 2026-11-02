import EthInapproximability.CurrentPaper.MatrixStage4TemplateRowConnector
import EthInapproximability.CurrentPaper.MatrixStage4PayloadRead

/-!
# Literal raw Stage--4 template entry machine

This fixed controller starts on the original raw column ordinal and template
row, complete one-hot family tables, a literal row-major `R` table, and
explicit unary dimensions. It composes both family-field reads, variable
first-coordinate digit selection, and the final literal source-bit lookup.
No selected family value, source coordinate, address, or answer is an input.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateBitMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4TemplateRowConnector.Stack ⊕ Fin 8
abbrev Label := MatrixStage4TemplateRowConnector.Label ⊕
  (Unit ⊕ MatrixTableLookup.Label)
abbrev Control := MatrixStage4TemplateRowConnector.Control ×
  MatrixTableLookup.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def priorSlots : MatrixStage4TemplateRowConnector.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def lookupSlots : MatrixTableLookup.Stack ↪ Stack where
  toFun := ![Sum.inl (.inr (.inr 0)), Sum.inr 0,
    Sum.inl (.inl (.inr 23)), Sum.inr 1, Sum.inr 2,
    Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7]
  inj' := by decide

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt priorSlots Sum.inl
      (fun v => (v,MatrixTableLookup.initial)) Prod.fst
      (some (.inr (.inl ()))) (MatrixStage4TemplateRowConnector.program l)
  | .inr (.inl ()) => load
      (fun _ => (MatrixStage4TemplateRowConnector.initial,
        MatrixTableLookup.initial))
      (goto (fun _ => .inr (.inr MatrixTableLookup.start)))
  | .inr (.inr l) => stmt lookupSlots (Sum.inr ∘ Sum.inr)
      (fun v => (MatrixStage4TemplateRowConnector.initial,v)) Prod.snd none
      (MatrixTableLookup.program l)

def start : Label := .inl MatrixStage4TemplateRowConnector.start
def initial : Control :=
  (MatrixStage4TemplateRowConnector.initial,MatrixTableLookup.initial)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def extra {rx cy : ℕ} (R : Fin rx → Fin cy → Bool) : Fin 8 → List Bool :=
  ![List.replicate cy true, [], [], [], rowMajor R, [], [], []]

def priorBank {rx cy : ℕ}
    (c : MatrixStage4TemplateRowConnector.Config)
    (R : Fin rx → Fin cy → Bool) : Stack → List Bool :=
  Sum.elim c.stk (extra R)

theorem prior_bank_eq (old new : MatrixStage4TemplateRowConnector.Stack → List Bool)
    (foreign : Fin 8 → List Bool) :
    bank priorSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at priorSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem prior_phase (l : MatrixStage4TemplateRowConnector.Label)
    (v : MatrixStage4TemplateRowConnector.Control)
    (S : MatrixStage4TemplateRowConnector.Stack → List Bool)
    {rx cy : ℕ} (R : Fin rx → Fin cy → Bool) (B : ℕ)
    (hhalt : (MatrixStage4TemplateRowConnector.run B ⟨some l, v, S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l)) (v,MatrixTableLookup.initial)
        (priorBank ⟨some l,v,S⟩ R)) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4TemplateRowConnector.run B ⟨some l,v,S⟩).var,
          MatrixTableLookup.initial)
        (priorBank (MatrixStage4TemplateRowConnector.run B ⟨some l,v,S⟩)
          R) := by
  let c : MatrixStage4TemplateRowConnector.Config := ⟨some l,v,S⟩
  have hp (u : MatrixStage4TemplateRowConnector.Label) :
      program (.inl u) = stmt priorSlots Sum.inl
        (fun w => (w,MatrixTableLookup.initial)) Prod.fst
        (some (.inr (.inl ())))
        (MatrixStage4TemplateRowConnector.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs priorSlots (priorBank c R)
    Sum.inl (fun w => (w,MatrixTableLookup.initial)) Prod.fst
    (by intro w; rfl) (some (.inr (.inl ())))
    MatrixStage4TemplateRowConnector.program program hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4TemplateRowConnector.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4TemplateRowConnector.run, priorBank, c, prior_bank_eq,
    hhalt'] using he

theorem bridge (v : MatrixStage4TemplateRowConnector.Control)
    (S : Stack → List Bool) :
    run 1 (cfg (some (.inr (.inl ())))
      (v,MatrixTableLookup.initial) S) =
    cfg (some (.inr (.inr MatrixTableLookup.start))) initial S := by
  simp [run, cfg, initial, advance, TM2.step, TM2.stepAux, program]

theorem lookup_phase (S : Stack → List Bool)
    (c : MatrixTableLookup.Config) (B : ℕ)
    (hstart : c.l = some MatrixTableLookup.start)
    (hinput : ∀ k : MatrixTableLookup.Stack,
      S (lookupSlots k) = c.stk k)
    (hhalt : (MatrixTableLookup.run B c).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inr (.inr MatrixTableLookup.start)))
        (MatrixStage4TemplateRowConnector.initial,c.var) S) =
      cfg none
        (MatrixStage4TemplateRowConnector.initial,
          (MatrixTableLookup.run B c).var)
        (bank lookupSlots S (MatrixTableLookup.run B c).stk) := by
  have hp (u : MatrixTableLookup.Label) :
      program (.inr (.inr u)) = stmt lookupSlots (Sum.inr ∘ Sum.inr)
        (fun v => (MatrixStage4TemplateRowConnector.initial,v)) Prod.snd none
        (MatrixTableLookup.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs lookupSlots S (Sum.inr ∘ Sum.inr)
    (fun v => (MatrixStage4TemplateRowConnector.initial,v)) Prod.snd
    (by intro v; rfl) none MatrixTableLookup.program program hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hbank : bank lookupSlots S c.stk = S :=
    bank_eq_self lookupSlots S c.stk (by intro k; exact (hinput k).symm)
  have hhalt' : (((advance MatrixTableLookup.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixTableLookup.run, hbank, hstart, hhalt'] using he

noncomputable def actualSource {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) : Config :=
  cfg (some start) initial
    (priorBank (MatrixStage4TemplateRowConnector.actualSource family code p ell) R)

def actualBound {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) : ℕ :=
  let γ := (((rawColumnCode a s q cy).symm code).2 p).2
  let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
  let x := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).2
  MatrixStage4TemplateRowConnector.actualBound family code p ell + 1 +
    32*(x.val+cy+(γ (firstCoordinate a s j)).val+rx*cy+1)^2

def columnSlot (i : MatrixStage4ColumnMachine.Stack) : Stack :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inl i))))))

def entrySlot (i : Fin 5) : Stack :=
  .inl (.inl (.inl (.inl (.inl (.inl (.inr i))))))

def firstTableSlot : Stack :=
  .inl (.inl (.inl (.inl (.inr 0))))

def rowTableSlot : Stack :=
  .inl (.inr (.inl (.inr 0)))

theorem source_code {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (actualSource R family code p ell).stk (columnSlot 0) =
      List.replicate code.val true := by
  rfl

theorem source_stride {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (actualSource R family code p ell).stk (columnSlot 2) =
      List.replicate ((binBase a s q cy)^(s-1-p.val)) true := by
  rfl

theorem source_ell {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (actualSource R family code p ell).stk (entrySlot 0) =
      List.replicate ell.val true := by
  rfl

theorem source_q {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (actualSource R family code p ell).stk (entrySlot 1) =
      List.replicate q true := by
  rfl

theorem source_first_table {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (actualSource R family code p ell).stk firstTableSlot =
      MatrixStage4FamilyData.fieldTable
        (MatrixStage4FamilyData.familyFirst family) := by
  rfl

theorem source_row_table {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (actualSource R family code p ell).stk rowTableSlot =
      MatrixStage4FamilyData.fieldTable
        (MatrixStage4FamilyData.familyRow family) := by
  rfl

theorem source_R {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (actualSource R family code p ell).stk (.inr 4) = rowMajor R := by
  rfl

theorem actual_bit {a s q L rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool)
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let γ := (((rawColumnCode a s q cy).symm code).2 p).2
    let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
    let x := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).2
    let y := γ (firstCoordinate a s j)
    ∃ t ≤ actualBound family code p ell,
      (run t (actualSource R family code p ell)).l = none ∧
      (run t (actualSource R family code p ell)).stk (.inr 5) =
        [R x y] := by
  dsimp
  let γ := (((rawColumnCode a s q cy).symm code).2 p).2
  let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
  let x := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).2
  let y := γ (firstCoordinate a s j)
  let c₁ := MatrixStage4TemplateRowConnector.actualSource family code p ell
  obtain ⟨tp,htp,hhalt,hcol,hrow⟩ :=
    MatrixStage4TemplateRowConnector.actual_row_and_symbol family code p ell
  have hhalt' : (MatrixStage4TemplateRowConnector.run tp c₁).l = none := by
    simpa only [c₁] using hhalt
  have hcol' : (MatrixStage4TemplateRowConnector.run tp c₁).stk
      (.inl (.inr 23)) = List.replicate y.val true := by
    simpa only [c₁, y, γ, j] using hcol
  have hrow' : (MatrixStage4TemplateRowConnector.run tp c₁).stk
      (.inr (.inr 0)) = List.replicate x.val true := by
    simpa only [c₁, x] using hrow
  obtain ⟨t₁,ht₁,h₁⟩ := prior_phase
    MatrixStage4TemplateRowConnector.start
    MatrixStage4TemplateRowConnector.initial c₁.stk R tp hhalt'
  have h₁' : run t₁ (actualSource R family code p ell) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4TemplateRowConnector.run tp c₁).var,
          MatrixTableLookup.initial)
        (priorBank (MatrixStage4TemplateRowConnector.run tp c₁) R) := by
    simpa only [actualSource, start, initial, c₁] using h₁
  let S := priorBank (MatrixStage4TemplateRowConnector.run tp c₁) R
  let cLookup := MatrixTableLookup.cfg (some MatrixTableLookup.start)
    MatrixTableLookup.initial (List.replicate x.val true)
    (List.replicate cy true) (List.replicate y.val true)
    [] (rowMajor R) []
  have hinput : ∀ k : MatrixTableLookup.Stack,
      S (lookupSlots k) = cLookup.stk k := by
    intro k
    fin_cases k <;>
      simp [S, cLookup, priorBank, extra, lookupSlots,
        MatrixTableLookup.cfg, hrow', hcol']
  obtain ⟨tr,htr,hrun⟩ := MatrixStage4PayloadRead.source_run R x y []
  have hstart : cLookup.l = some MatrixTableLookup.start := rfl
  have hvar : cLookup.var = MatrixTableLookup.initial := rfl
  have hhaltLookup : (MatrixTableLookup.run tr cLookup).l = none := by
    rw [hrun]
    rfl
  obtain ⟨t₂,ht₂,h₂⟩ := lookup_phase S cLookup tr hstart hinput hhaltLookup
  have h12 := run_add h₁' 1
  rw [bridge] at h12
  have h123 := run_add h12 t₂
  change run (t₁+1+t₂) (actualSource R family code p ell) =
    run t₂ (cfg (some (.inr (.inr MatrixTableLookup.start)))
      (MatrixStage4TemplateRowConnector.initial,
        MatrixTableLookup.initial) S) at h123
  rw [← hvar, h₂] at h123
  refine ⟨t₁+1+t₂, by dsimp [actualBound, γ, j, x, y] at htp htr ⊢; omega,
    ?_, ?_⟩
  · rw [h123]
    rfl
  · rw [h123]
    have ho := bank_at lookupSlots S (MatrixTableLookup.run tr cLookup).stk
      (7 : MatrixTableLookup.Stack)
    have hout : (MatrixTableLookup.run tr cLookup).stk
        (7 : MatrixTableLookup.Stack) = [R x y] := by
      rw [hrun]
      rfl
    rw [hout] at ho
    simpa [cfg, lookupSlots, x, y, γ, j] using ho

theorem actual_raw_template {a s q L nv nb rx cy : ℕ}
    (R : Fin rx → Fin cy → Bool) (hs : 0 < s)
    (family : SecondFamily a q L (Fin rx))
    (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    ∃ t ≤ actualBound family code p ell,
      (run t (actualSource R family code p ell)).l = none ∧
      (run t (actualSource R family code p ell)).stk (.inr 5) =
        [rawMatrix R a s q L nv nb hs family order vectors cap
          (.inl (p,ell)) ((rawColumnCode a s q cy).symm code)] := by
  obtain ⟨t,ht,hh,hb⟩ := actual_bit R family code p ell
  refine ⟨t,ht,hh,?_⟩
  simpa only [rawMatrix_template, secondMatrix_apply,
    MatrixStage4TemplateFieldGather.selectedFin] using hb

end EthInapproximability.CurrentPaper.MatrixStage4TemplateBitMachine
