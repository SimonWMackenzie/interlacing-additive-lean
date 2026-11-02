import EthInapproximability.CurrentPaper.MatrixStage4TemplateEntryMachine

/-!
# Physical template family-field start

This fixed program first computes the selected family-pair index from the
actual raw column ordinal, then multiplies that index by a supplied unary
field width.  The width is a dimension, not a selected family value.  The
result is the starting offset for a literal one-hot family-field table.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldStart

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4TemplateEntryMachine.Stack ⊕ Fin 5
abbrev Label := MatrixStage4TemplateEntryMachine.Label ⊕ MatrixAddressMachine.Label
abbrev Control := MatrixStage4TemplateEntryMachine.Control × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def priorSlots : MatrixStage4TemplateEntryMachine.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def fieldSlots : Fin 6 ↪ Stack where
  toFun := ![Sum.inl (.inr 4), Sum.inr 0, Sum.inr 1,
    Sum.inr 2, Sum.inr 3, Sum.inr 4]
  inj' := by decide

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt priorSlots Sum.inl (fun v => (v,false)) Prod.fst
      (some (.inr .outer)) (MatrixStage4TemplateEntryMachine.program l)
  | .inr l => stmt fieldSlots Sum.inr
      (fun v => (MatrixStage4TemplateEntryMachine.initial,v)) Prod.snd none
      (MatrixAddressMachine.program l)

def start : Label := .inl MatrixStage4TemplateEntryMachine.start
def initial : Control := (MatrixStage4TemplateEntryMachine.initial,false)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def extra (width : ℕ) : Fin 5 → List Bool :=
  ![List.replicate width true, [], [], [], []]

def priorBank (c : MatrixStage4TemplateEntryMachine.Config) (width : ℕ) :
    Stack → List Bool := Sum.elim c.stk (extra width)

theorem prior_bank_eq (old new : MatrixStage4TemplateEntryMachine.Stack → List Bool)
    (foreign : Fin 5 → List Bool) :
    bank priorSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at priorSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem prior_phase (l : MatrixStage4TemplateEntryMachine.Label)
    (v : MatrixStage4TemplateEntryMachine.Control)
    (S : MatrixStage4TemplateEntryMachine.Stack → List Bool)
    (width B : ℕ)
    (hhalt : (MatrixStage4TemplateEntryMachine.run B ⟨some l,v,S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l)) (v,false)
        (priorBank ⟨some l,v,S⟩ width)) =
      cfg (some (.inr .outer))
        ((MatrixStage4TemplateEntryMachine.run B ⟨some l,v,S⟩).var,false)
        (priorBank (MatrixStage4TemplateEntryMachine.run B ⟨some l,v,S⟩)
          width) := by
  let c : MatrixStage4TemplateEntryMachine.Config := ⟨some l,v,S⟩
  have hp (u : MatrixStage4TemplateEntryMachine.Label) :
      program (.inl u) = stmt priorSlots Sum.inl
        (fun w => (w,false)) Prod.fst (some (.inr .outer))
        (MatrixStage4TemplateEntryMachine.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs priorSlots (priorBank c width)
    Sum.inl (fun w => (w,false)) Prod.fst (by intro w; rfl)
    (some (.inr .outer)) MatrixStage4TemplateEntryMachine.program program
    hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4TemplateEntryMachine.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4TemplateEntryMachine.run, priorBank, c, prior_bank_eq,
    hhalt'] using he

theorem field_phase (S : Stack → List Bool) (row width : ℕ)
    (hinput : ∀ k : Fin 6,
      S (fieldSlots k) =
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate row true) (List.replicate width true)
          [] [] [] []).stk k) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width 0,
      run t (cfg (some (.inr .outer)) initial S) =
        cfg none initial
          (bank fieldSlots S
            (MatrixAddressMachine.cfg none false
              (List.replicate row true) (List.replicate width true)
              [] [] [] (List.replicate (row*width) true)).stk) := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate row true) (List.replicate width true) [] [] [] []
  let out := MatrixAddressMachine.cfg none false
    (List.replicate row true) (List.replicate width true)
    [] [] [] (List.replicate (row*width) true)
  have hrun : MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime row width 0) c = out := by
    simpa only [c, out, Nat.add_zero, List.append_nil] using
      MatrixAddressMachine.address_run row width 0 false []
  have hhalt : (((advance MatrixAddressMachine.program)^[
      MatrixAddressMachine.exactTime row width 0]) c).l = none := by
    rw [← MatrixAddressMachine.run, hrun]
    rfl
  have hp (u : MatrixAddressMachine.Label) :
      program (.inr u) = stmt fieldSlots Sum.inr
        (fun w => (MatrixStage4TemplateEntryMachine.initial,w)) Prod.snd none
        (MatrixAddressMachine.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs fieldSlots S Sum.inr
    (fun w => (MatrixStage4TemplateEntryMachine.initial,w)) Prod.snd
    (by intro w; rfl) none MatrixAddressMachine.program program
    hp c (MatrixAddressMachine.exactTime row width 0) hhalt
  refine ⟨t,ht,?_⟩
  have hbank : bank fieldSlots S c.stk = S :=
    bank_eq_self fieldSlots S c.stk (by intro k; exact (hinput k).symm)
  rw [show (((advance MatrixAddressMachine.program)^[
    MatrixAddressMachine.exactTime row width 0]) c) = out from hrun] at he
  simpa only [run, cfg, initial, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    c, out, hbank] using he

def source {a s q L cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) (ell : Fin L) (width : ℕ) : Config :=
  cfg (some start) initial
    (priorBank
      (MatrixStage4TemplateEntryMachine.cfg
        (some MatrixStage4TemplateEntryMachine.start)
        MatrixStage4TemplateEntryMachine.initial
        (MatrixStage4TemplateEntryMachine.columnBank
          (MatrixStage4TemplateEntryMachine.columnInput code p)
          ell.val q)) width)

noncomputable def pairOutput {a s q L cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) (ell : Fin L) : MatrixStage4TemplateEntryMachine.Config :=
  MatrixStage4TemplateEntryMachine.cfg none
    MatrixStage4TemplateEntryMachine.initial
    (bank MatrixStage4TemplateEntryMachine.addressSlots
      (MatrixStage4TemplateEntryMachine.columnBank
        (MatrixStage4TemplateEntryMachine.columnOutput code p) ell.val q)
      (MatrixAddressMachine.cfg none false
        (List.replicate ell.val true) (List.replicate q true)
        (List.replicate
          (MatrixStage4TemplateEntryMachine.selectedAlpha code p) true)
        [] []
        (List.replicate
          (ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)
          true)).stk)

noncomputable def fieldOutput {a s q L cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) (ell : Fin L) (width : ℕ) : Config :=
  let row := ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p
  cfg none initial
    (bank fieldSlots (priorBank (pairOutput code p ell) width)
      (MatrixAddressMachine.cfg none false
        (List.replicate row true) (List.replicate width true)
        [] [] [] (List.replicate (row*width) true)).stk)

def exactBound {a s q L cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) (ell : Fin L) (width : ℕ) : ℕ :=
  MatrixStage4TemplateEntryMachine.columnTime code p +
    MatrixAddressMachine.exactTime ell.val q
      (MatrixStage4TemplateEntryMachine.selectedAlpha code p) +
    MatrixAddressMachine.exactTime
      (ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)
      width 0

theorem field_start_run {a s q L cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (width : ℕ) :
    ∃ t ≤ exactBound code p ell width,
      run t (source code p ell width) = fieldOutput code p ell width := by
  let row := ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p
  obtain ⟨tp,htp,hp⟩ :=
    MatrixStage4TemplateEntryMachine.column_address_run code p ell
  have hh : (MatrixStage4TemplateEntryMachine.run tp
      (MatrixStage4TemplateEntryMachine.cfg
        (some MatrixStage4TemplateEntryMachine.start)
        MatrixStage4TemplateEntryMachine.initial
        (MatrixStage4TemplateEntryMachine.columnBank
          (MatrixStage4TemplateEntryMachine.columnInput code p)
          ell.val q))).l = none := by
    rw [hp]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := prior_phase
    MatrixStage4TemplateEntryMachine.start
    MatrixStage4TemplateEntryMachine.initial
    (MatrixStage4TemplateEntryMachine.columnBank
      (MatrixStage4TemplateEntryMachine.columnInput code p) ell.val q)
    width tp hh
  have h₁' : run t₁ (source code p ell width) =
      cfg (some (.inr .outer)) initial
        (priorBank (pairOutput code p ell) width) := by
    simp only [MatrixStage4TemplateEntryMachine.cfg] at hp
    rw [hp] at h₁
    simpa only [source, pairOutput, initial] using h₁
  let S := priorBank (pairOutput code p ell) width
  have hpair : (pairOutput code p ell).stk (.inr 4) =
      List.replicate row true := by
    simpa only [pairOutput, MatrixStage4TemplateEntryMachine.cfg,
      MatrixStage4TemplateEntryMachine.addressSlots,
      MatrixAddressMachine.cfg, row] using
      (bank_at MatrixStage4TemplateEntryMachine.addressSlots
        (MatrixStage4TemplateEntryMachine.columnBank
          (MatrixStage4TemplateEntryMachine.columnOutput code p) ell.val q)
        (MatrixAddressMachine.cfg none false
          (List.replicate ell.val true) (List.replicate q true)
          (List.replicate
            (MatrixStage4TemplateEntryMachine.selectedAlpha code p) true)
          [] [] (List.replicate row true)).stk 5)
  have hinput : ∀ k : Fin 6,
      S (fieldSlots k) =
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate row true) (List.replicate width true)
          [] [] [] []).stk k := by
    intro k
    fin_cases k <;>
      simp [S, priorBank, extra, fieldSlots, MatrixAddressMachine.cfg, hpair]
  obtain ⟨t₂,ht₂,h₂⟩ := field_phase S row width hinput
  refine ⟨t₁+t₂, by dsimp [exactBound, row] at ht₂ ⊢; omega, ?_⟩
  simpa only [S, fieldOutput, row] using (run_add h₁' t₂).trans h₂

theorem field_start_outputs {a s q L cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (width : ℕ) :
    ∃ t ≤ exactBound code p ell width,
      (run t (source code p ell width)).l = none ∧
      (run t (source code p ell width)).stk (.inr 4) =
        List.replicate
          ((ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)*width)
          true ∧
      (run t (source code p ell width)).stk (.inl (.inr 4)) =
        List.replicate
          (ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)
          true := by
  obtain ⟨t,ht,he⟩ := field_start_run code p ell width
  refine ⟨t,ht,?_,?_,?_⟩
  all_goals rw [he]
  · rfl
  · simpa only [fieldOutput, cfg, fieldSlots, MatrixAddressMachine.cfg] using
      (bank_at fieldSlots (priorBank (pairOutput code p ell) width)
        (MatrixAddressMachine.cfg none false
          (List.replicate
            (ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p) true)
          (List.replicate width true) [] [] []
          (List.replicate
            ((ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)*width)
            true)).stk 5)
  · simpa only [fieldOutput, cfg, fieldSlots, MatrixAddressMachine.cfg] using
      (bank_at fieldSlots (priorBank (pairOutput code p ell) width)
        (MatrixAddressMachine.cfg none false
          (List.replicate
            (ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p) true)
          (List.replicate width true) [] [] []
          (List.replicate
            ((ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)*width)
            true)).stk 0)

end EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldStart
