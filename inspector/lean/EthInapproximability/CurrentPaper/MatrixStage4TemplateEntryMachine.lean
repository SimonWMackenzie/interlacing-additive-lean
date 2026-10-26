import EthInapproximability.CurrentPaper.MatrixStage4ColumnMachine
import EthInapproximability.CurrentPaper.MatrixStage4FamilyAddress
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# First physical template-entry handoff

The raw Stage--4 template bit needs the selected bin's selector `α`, then the
pair address `ℓ*q+α` into both literal family-field tables.  This fixed
controller physically runs the selected-bin column decoder and then runs the
unary multiply-add address machine on its output register.  It neither starts
with a selected `α` nor treats a family-field or final matrix bit as an input.
The downstream family gathers and source-bit lookup remain separate stages.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateEntryMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4ColumnMachine.Stack ⊕ Fin 5
abbrev Label := MatrixStage4ColumnMachine.Label ⊕ MatrixAddressMachine.Label
abbrev Control := MatrixStage4ColumnMachine.Control × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def columnSlots : MatrixStage4ColumnMachine.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

/-- Address registers: row=`ℓ`, width=`q`, column=`α` returned in local bank
15, two empty scratch banks, and a fresh unary output bank. -/
def addressSlots : Fin 6 ↪ Stack where
  toFun := ![Sum.inr 0, Sum.inr 1, Sum.inl 15,
    Sum.inr 2, Sum.inr 3, Sum.inr 4]
  inj' := by decide

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt columnSlots Sum.inl (fun v => (v,false)) Prod.fst
      (some (.inr .outer)) (MatrixStage4ColumnMachine.program l)
  | .inr l => stmt addressSlots Sum.inr
      (fun v => (MatrixStage4ColumnMachine.initial,v)) Prod.snd none
      (MatrixAddressMachine.program l)

def start : Label := .inl MatrixStage4ColumnMachine.outerStart
def initial : Control := (MatrixStage4ColumnMachine.initial,false)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def extra (ell q : ℕ) : Fin 5 → List Bool :=
  ![List.replicate ell true, List.replicate q true, [], [], []]

def columnBank (c : MatrixStage4ColumnMachine.Config) (ell q : ℕ) :
    Stack → List Bool := Sum.elim c.stk (extra ell q)

theorem column_bank_eq (old new : MatrixStage4ColumnMachine.Stack → List Bool)
    (foreign : Fin 5 → List Bool) :
    bank columnSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at columnSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem column_phase (l : MatrixStage4ColumnMachine.Label)
    (v : MatrixStage4ColumnMachine.Control)
    (S : MatrixStage4ColumnMachine.Stack → List Bool) (ell q B : ℕ)
    (hhalt : (MatrixStage4ColumnMachine.run B ⟨some l,v,S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l))
        (v,false) (columnBank ⟨some l,v,S⟩ ell q)) =
      cfg (some (.inr .outer))
        ((MatrixStage4ColumnMachine.run B ⟨some l,v,S⟩).var,false)
        (columnBank (MatrixStage4ColumnMachine.run B ⟨some l,v,S⟩) ell q) := by
  let c : MatrixStage4ColumnMachine.Config := ⟨some l,v,S⟩
  have hprogram (u : MatrixStage4ColumnMachine.Label) :
      program (.inl u) = stmt columnSlots Sum.inl
        (fun w => (w,false)) Prod.fst (some (.inr .outer))
        (MatrixStage4ColumnMachine.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs columnSlots (columnBank c ell q)
    Sum.inl (fun w => (w,false)) Prod.fst (by intro w; rfl)
    (some (.inr .outer)) MatrixStage4ColumnMachine.program program
    hprogram c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4ColumnMachine.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4ColumnMachine.run, columnBank, c, column_bank_eq,
    hhalt'] using he

theorem address_phase (S : Stack → List Bool) (ell q alpha : ℕ)
    (hinput : ∀ k : Fin 6,
      S (addressSlots k) =
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate ell true) (List.replicate q true)
          (List.replicate alpha true) [] [] []).stk k) :
    ∃ t ≤ MatrixAddressMachine.exactTime ell q alpha,
      run t (cfg (some (.inr .outer)) initial S) =
        cfg none initial
          (bank addressSlots S
            (MatrixAddressMachine.cfg none false
              (List.replicate ell true) (List.replicate q true)
              (List.replicate alpha true) [] []
              (List.replicate (ell*q+alpha) true)).stk) := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate ell true) (List.replicate q true)
    (List.replicate alpha true) [] [] []
  let out := MatrixAddressMachine.cfg none false
    (List.replicate ell true) (List.replicate q true)
    (List.replicate alpha true) [] []
    (List.replicate (ell*q+alpha) true)
  have hrun : MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime ell q alpha) c = out := by
    simpa only [c, out, List.append_nil] using
      MatrixAddressMachine.address_run ell q alpha false []
  have hhalt : (((advance MatrixAddressMachine.program)^[
      MatrixAddressMachine.exactTime ell q alpha]) c).l = none := by
    rw [← MatrixAddressMachine.run, hrun]
    rfl
  have hprogram (u : MatrixAddressMachine.Label) :
      program (.inr u) = stmt addressSlots Sum.inr
        (fun w => (MatrixStage4ColumnMachine.initial,w)) Prod.snd none
        (MatrixAddressMachine.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs addressSlots S Sum.inr
    (fun w => (MatrixStage4ColumnMachine.initial,w)) Prod.snd
    (by intro w; rfl) none MatrixAddressMachine.program program
    hprogram c (MatrixAddressMachine.exactTime ell q alpha) hhalt
  refine ⟨t,ht,?_⟩
  have hbank : bank addressSlots S c.stk = S :=
    bank_eq_self addressSlots S c.stk (by intro k; exact (hinput k).symm)
  rw [show (((advance MatrixAddressMachine.program)^[
    MatrixAddressMachine.exactTime ell q alpha]) c) = out from hrun] at he
  simpa only [run, cfg, initial, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    c, out, hbank] using he

def selectedAlpha {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) : ℕ :=
  (((rawColumnCode a s q cy).symm code).2 p).1.val

def columnInput {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) : MatrixStage4ColumnMachine.Config :=
  MatrixStage4ColumnMachine.cfg
    (some MatrixStage4ColumnMachine.outerStart)
    MatrixStage4ColumnMachine.initial
    (List.replicate code.val true)
    (List.replicate ((binBase a s q cy)^s) true)
    (List.replicate ((binBase a s q cy)^(s-1-p.val)) true)
    (List.replicate (binBase a s q cy) true)
    (List.replicate (wordBase a s cy) true)
    [] [] [] [] [] [] [] []

def columnOutput {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) : MatrixStage4ColumnMachine.Config :=
  let base := binBase a s q cy
  let stride := base^(s-1-p.val)
  let outer := base^s
  let b := code.val%outer
  let k := b/stride
  let r := ((rawColumnCode a s q cy).symm code).2 p
  MatrixStage4ColumnMachine.cfg none MatrixStage4ColumnMachine.initial
    [] (List.replicate outer true) (List.replicate stride true)
    (List.replicate base true) (List.replicate (wordBase a s cy) true)
    [] (List.replicate (b%stride) true) []
    (List.replicate
      ((tupleCode cy (s+1)) ((rawColumnCode a s q cy).symm code).1).val true)
    [] (List.replicate (k/base) true)
    (List.replicate (firstWordCode a s cy r.2).val true)
    (List.replicate r.1.val true)

def columnTime {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) : ℕ :=
  let base := binBase a s q cy
  let stride := base^(s-1-p.val)
  let outer := base^s
  let b := code.val%outer
  let k := b/stride
  let d := k%base
  MatrixUnaryDivision.totalTime code.val outer +
    MatrixUnaryDivision.totalTime b stride +
    MatrixUnaryDivision.totalTime k base +
    MatrixUnaryDivision.totalTime d (wordBase a s cy) + 1

theorem column_actual {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) :
    ∃ t ≤ columnTime code p,
      MatrixStage4ColumnMachine.run t (columnInput code p) =
        columnOutput code p := by
  simpa only [columnTime, columnInput, columnOutput] using
    MatrixStage4ColumnMachine.raw_column_run code p

theorem columnOutput_alpha {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) :
    (columnOutput code p).stk 15 = List.replicate (selectedAlpha code p) true :=
  rfl

theorem column_address_run {a s q L cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    ∃ t ≤ columnTime code p +
        MatrixAddressMachine.exactTime ell.val q (selectedAlpha code p),
      run t (cfg (some start) initial
        (columnBank (columnInput code p) ell.val q)) =
      cfg none initial
        (bank addressSlots (columnBank (columnOutput code p) ell.val q)
          (MatrixAddressMachine.cfg none false
            (List.replicate ell.val true) (List.replicate q true)
            (List.replicate (selectedAlpha code p) true) [] []
            (List.replicate (ell.val*q+selectedAlpha code p) true)).stk) := by
  obtain ⟨tc,htc,hc⟩ := column_actual code p
  have hh : (MatrixStage4ColumnMachine.run tc (columnInput code p)).l = none := by
    rw [hc]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := column_phase MatrixStage4ColumnMachine.outerStart
    MatrixStage4ColumnMachine.initial (columnInput code p).stk ell.val q tc hh
  change run t₁ (cfg (some start) initial
      (columnBank (columnInput code p) ell.val q)) =
    cfg (some (.inr .outer))
      ((MatrixStage4ColumnMachine.run tc (columnInput code p)).var,false)
      (columnBank (MatrixStage4ColumnMachine.run tc (columnInput code p))
        ell.val q) at h₁
  rw [hc] at h₁
  have h₁' : run t₁ (cfg (some start) initial
      (columnBank (columnInput code p) ell.val q)) =
      cfg (some (.inr .outer)) initial
        (columnBank (columnOutput code p) ell.val q) := by
    exact h₁
  let S := columnBank (columnOutput code p) ell.val q
  have hinput : ∀ k : Fin 6,
      S (addressSlots k) =
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate ell.val true) (List.replicate q true)
          (List.replicate (selectedAlpha code p) true) [] [] []).stk k := by
    intro k
    fin_cases k <;> simp [S, columnBank, extra, addressSlots,
      columnOutput_alpha, MatrixAddressMachine.cfg]
  obtain ⟨t₂,ht₂,h₂⟩ := address_phase S ell.val q
    (selectedAlpha code p) hinput
  refine ⟨t₁+t₂, by omega, ?_⟩
  simpa only [S] using (run_add h₁' t₂).trans h₂

/-- The selected `α` is not an input.  The fixed controller leaves the
physically decoded selector, original `ℓ` and `q`, and their unary pair
address in explicit terminal banks. -/
theorem column_address_outputs {a s q L cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    ∃ t ≤ columnTime code p +
        MatrixAddressMachine.exactTime ell.val q (selectedAlpha code p),
      (run t (cfg (some start) initial
        (columnBank (columnInput code p) ell.val q))).l = none ∧
      (run t (cfg (some start) initial
        (columnBank (columnInput code p) ell.val q))).stk (.inr 4) =
          List.replicate (ell.val*q+selectedAlpha code p) true ∧
      (run t (cfg (some start) initial
        (columnBank (columnInput code p) ell.val q))).stk (.inl 15) =
          List.replicate (selectedAlpha code p) true ∧
      (run t (cfg (some start) initial
        (columnBank (columnInput code p) ell.val q))).stk (.inr 0) =
          List.replicate ell.val true ∧
      (run t (cfg (some start) initial
        (columnBank (columnInput code p) ell.val q))).stk (.inr 1) =
          List.replicate q true := by
  obtain ⟨t,ht,he⟩ := column_address_run code p ell
  refine ⟨t,ht,?_,?_,?_,?_,?_⟩
  all_goals rw [he]
  · rfl
  · simpa only [cfg, addressSlots, MatrixAddressMachine.cfg] using
      (bank_at addressSlots
        (columnBank (columnOutput code p) ell.val q)
        (MatrixAddressMachine.cfg none false
          (List.replicate ell.val true) (List.replicate q true)
          (List.replicate (selectedAlpha code p) true) [] []
          (List.replicate (ell.val*q+selectedAlpha code p) true)).stk 5)
  · simpa only [cfg, addressSlots, MatrixAddressMachine.cfg] using
      (bank_at addressSlots
        (columnBank (columnOutput code p) ell.val q)
        (MatrixAddressMachine.cfg none false
          (List.replicate ell.val true) (List.replicate q true)
          (List.replicate (selectedAlpha code p) true) [] []
          (List.replicate (ell.val*q+selectedAlpha code p) true)).stk 2)
  · simpa only [cfg, addressSlots, MatrixAddressMachine.cfg] using
      (bank_at addressSlots
        (columnBank (columnOutput code p) ell.val q)
        (MatrixAddressMachine.cfg none false
          (List.replicate ell.val true) (List.replicate q true)
          (List.replicate (selectedAlpha code p) true) [] []
          (List.replicate (ell.val*q+selectedAlpha code p) true)).stk 0)
  · simpa only [cfg, addressSlots, MatrixAddressMachine.cfg] using
      (bank_at addressSlots
        (columnBank (columnOutput code p) ell.val q)
        (MatrixAddressMachine.cfg none false
          (List.replicate ell.val true) (List.replicate q true)
          (List.replicate (selectedAlpha code p) true) [] []
          (List.replicate (ell.val*q+selectedAlpha code p) true)).stk 1)

theorem pair_address_eq {a s q L cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    ell.val*q+selectedAlpha code p =
      (finProdFinEquiv
        (ell, (((rawColumnCode a s q cy).symm code).2 p).1)).val := by
  simp [selectedAlpha, finProdFinEquiv_apply_val]
  ring

end EthInapproximability.CurrentPaper.MatrixStage4TemplateEntryMachine
