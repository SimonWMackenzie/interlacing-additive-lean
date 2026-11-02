import EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldStart
import EthInapproximability.CurrentPaper.MatrixStage4FamilyData

/-!
# Physical family-field gather after selected-bin address calculation

The first phase computes the one-hot field's starting offset from the raw
column code. The second phase reads the literal field table with the existing
source-preserving word-gather program. Only dimensions and the full table are
initial data; neither the selected family field nor the final bit is loaded.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldGather

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4TemplateFieldStart.Stack ⊕ Fin 8
abbrev Label := MatrixStage4TemplateFieldStart.Label ⊕ MatrixWordGather.Forward.Label
abbrev Control := MatrixStage4TemplateFieldStart.Control × MatrixWordGather.Forward.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def priorSlots : MatrixStage4TemplateFieldStart.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def gatherSlots : MatrixWordGather.Forward.Stack ↪ Stack where
  toFun
    | .inl 0 => .inl (.inr 4)
    | .inl 1 => .inr 4
    | .inl 2 => .inr 5
    | .inl 3 => .inr 0
    | .inl 4 => .inr 6
    | .inl 5 => .inr 1
    | .inl 6 => .inr 7
    | .inr 0 => .inr 2
    | .inr 1 => .inr 3
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def gatherInitial : MatrixWordGather.Forward.Control :=
  (MatrixWordGather.baseControl, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt priorSlots Sum.inl
      (fun v => (v,gatherInitial)) Prod.fst
      (some (.inr (.inr .test))) (MatrixStage4TemplateFieldStart.program l)
  | .inr l => stmt gatherSlots Sum.inr
      (fun v => (MatrixStage4TemplateFieldStart.initial,v)) Prod.snd none
      (MatrixWordGather.Forward.program l)

def start : Label := .inl MatrixStage4TemplateFieldStart.start
def initial : Control := (MatrixStage4TemplateFieldStart.initial,gatherInitial)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def extra (width : ℕ) (table : List Bool) : Fin 8 → List Bool :=
  ![table, [], List.replicate width true, [], [], [], [], []]

def priorBank (c : MatrixStage4TemplateFieldStart.Config)
    (width : ℕ) (table : List Bool) : Stack → List Bool :=
  Sum.elim c.stk (extra width table)

theorem prior_bank_eq (old new : MatrixStage4TemplateFieldStart.Stack → List Bool)
    (foreign : Fin 8 → List Bool) :
    bank priorSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at priorSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem prior_phase (l : MatrixStage4TemplateFieldStart.Label)
    (v : MatrixStage4TemplateFieldStart.Control)
    (S : MatrixStage4TemplateFieldStart.Stack → List Bool)
    (width B : ℕ) (table : List Bool)
    (hhalt : (MatrixStage4TemplateFieldStart.run B ⟨some l,v,S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l)) (v,gatherInitial)
        (priorBank ⟨some l,v,S⟩ width table)) =
      cfg (some (.inr (.inr .test)))
        ((MatrixStage4TemplateFieldStart.run B ⟨some l,v,S⟩).var,gatherInitial)
        (priorBank (MatrixStage4TemplateFieldStart.run B ⟨some l,v,S⟩)
          width table) := by
  let c : MatrixStage4TemplateFieldStart.Config := ⟨some l,v,S⟩
  have hp (u : MatrixStage4TemplateFieldStart.Label) :
      program (.inl u) = stmt priorSlots Sum.inl
        (fun w => (w,gatherInitial)) Prod.fst
        (some (.inr (.inr .test)))
        (MatrixStage4TemplateFieldStart.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs priorSlots (priorBank c width table)
    Sum.inl (fun w => (w,gatherInitial)) Prod.fst (by intro w; rfl)
    (some (.inr (.inr .test))) MatrixStage4TemplateFieldStart.program program
    hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4TemplateFieldStart.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4TemplateFieldStart.run, priorBank, c, prior_bank_eq,
    hhalt'] using he

theorem gather_phase {rows m : ℕ} (f : Fin rows → Fin m)
    (r : Fin rows) (S : Stack → List Bool)
    (hinput : ∀ k : MatrixWordGather.Forward.Stack,
      S (gatherSlots k) =
        (MatrixWordGather.Forward.cfg (some (.inr .test)) none
          (List.replicate (r.val*m) true)
          (MatrixStage4FamilyData.fieldTable f) []
          (List.replicate m true) []).stk k) :
    ∃ t ≤ m * (3*(r.val*m+m)+3*(rows*m)+11)+2,
      run t (cfg (some (.inr (.inr .test))) initial S) =
      cfg none initial
        (bank gatherSlots S
          (MatrixWordGather.Forward.cfg none none
            (List.replicate (r.val*m+m) true)
            (MatrixStage4FamilyData.fieldTable f) [] []
            (MatrixStage4FamilyData.oneHot m (f r))).stk) := by
  let c := MatrixWordGather.Forward.cfg (some (.inr .test)) none
    (List.replicate (r.val*m) true)
    (MatrixStage4FamilyData.fieldTable f) []
    (List.replicate m true) []
  let out := MatrixWordGather.Forward.cfg none none
    (List.replicate (r.val*m+m) true)
    (MatrixStage4FamilyData.fieldTable f) [] []
    (MatrixStage4FamilyData.oneHot m (f r))
  obtain ⟨t,ht,hrun⟩ := MatrixStage4FamilyData.field_gather_run f r
  have hhalt : (((advance MatrixWordGather.Forward.program)^[t]) c).l = none := by
    rw [← MatrixWordGather.Forward.run, hrun]
    rfl
  have hp (u : MatrixWordGather.Forward.Label) :
      program (.inr u) = stmt gatherSlots Sum.inr
        (fun v => (MatrixStage4TemplateFieldStart.initial,v)) Prod.snd none
        (MatrixWordGather.Forward.program u) := rfl
  obtain ⟨t',ht',he⟩ := outputs gatherSlots S Sum.inr
    (fun v => (MatrixStage4TemplateFieldStart.initial,v)) Prod.snd
    (by intro v; rfl) none MatrixWordGather.Forward.program program
    hp c t hhalt
  refine ⟨t', by omega, ?_⟩
  have hbank : bank gatherSlots S c.stk = S :=
    bank_eq_self gatherSlots S c.stk (by intro k; exact (hinput k).symm)
  rw [show (((advance MatrixWordGather.Forward.program)^[t]) c) = out from hrun] at he
  simpa only [run, cfg, initial, gatherInitial,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, c, out, hbank] using he

def selectedFin {a s q cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) : Fin q :=
  (((rawColumnCode a s q cy).symm code).2 p).1

def selectedRow {a s q L cy : ℕ} (code : Fin (cols a s q cy))
    (p : Fin s) (ell : Fin L) : Fin (L*q) :=
  finProdFinEquiv (ell, selectedFin code p)

theorem selectedRow_val {a s q L cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (selectedRow code p ell).val =
      ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p := by
  exact (MatrixStage4TemplateEntryMachine.pair_address_eq code p ell).symm

noncomputable def source {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) : Config :=
  cfg (some start) initial
    (priorBank (MatrixStage4TemplateFieldStart.source code p ell m)
      m (MatrixStage4FamilyData.fieldTable f))

noncomputable def output {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) : Config :=
  let r := selectedRow code p ell
  let S := priorBank (MatrixStage4TemplateFieldStart.fieldOutput code p ell m)
    m (MatrixStage4FamilyData.fieldTable f)
  cfg none initial
    (bank gatherSlots S
      (MatrixWordGather.Forward.cfg none none
        (List.replicate (r.val*m+m) true)
        (MatrixStage4FamilyData.fieldTable f) [] []
        (MatrixStage4FamilyData.oneHot m (f r))).stk)

def exactBound {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) : ℕ :=
  MatrixStage4TemplateFieldStart.exactBound code p ell m +
    m * (3*((selectedRow code p ell).val*m+m)+3*(L*q*m)+11)+2

theorem field_gather_run {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) :
    ∃ t ≤ exactBound code p ell f,
      run t (source code p ell f) = output code p ell f := by
  let r := selectedRow code p ell
  let table := MatrixStage4FamilyData.fieldTable f
  obtain ⟨tp,htp,hp⟩ :=
    MatrixStage4TemplateFieldStart.field_start_run code p ell m
  have hh : (MatrixStage4TemplateFieldStart.run tp
      (MatrixStage4TemplateFieldStart.source code p ell m)).l = none := by
    rw [hp]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := prior_phase
    MatrixStage4TemplateFieldStart.start
    MatrixStage4TemplateFieldStart.initial
    (MatrixStage4TemplateFieldStart.source code p ell m).stk
    m tp table hh
  have h₁' : run t₁ (source code p ell f) =
      cfg (some (.inr (.inr .test))) initial
        (priorBank (MatrixStage4TemplateFieldStart.fieldOutput code p ell m)
          m table) := by
    simp only [MatrixStage4TemplateFieldStart.source,
      MatrixStage4TemplateFieldStart.cfg] at hp
    simp only [MatrixStage4TemplateFieldStart.source,
      MatrixStage4TemplateFieldStart.cfg] at h₁
    rw [hp] at h₁
    simpa only [source, start, initial, table] using h₁
  let S := priorBank (MatrixStage4TemplateFieldStart.fieldOutput code p ell m)
    m table
  have hstart :
      (MatrixStage4TemplateFieldStart.fieldOutput code p ell m).stk (.inr 4) =
        List.replicate (r.val*m) true := by
    rw [selectedRow_val]
    simpa only [MatrixStage4TemplateFieldStart.fieldOutput,
      MatrixStage4TemplateFieldStart.cfg,
      MatrixStage4TemplateFieldStart.fieldSlots,
      MatrixAddressMachine.cfg] using
      (bank_at MatrixStage4TemplateFieldStart.fieldSlots
        (MatrixStage4TemplateFieldStart.priorBank
          (MatrixStage4TemplateFieldStart.pairOutput code p ell) m)
        (MatrixAddressMachine.cfg none false
          (List.replicate
            (ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)
            true)
          (List.replicate m true) [] [] []
          (List.replicate
            ((ell.val*q+MatrixStage4TemplateEntryMachine.selectedAlpha code p)*m)
            true)).stk 5)
  have hinput : ∀ k : MatrixWordGather.Forward.Stack,
      S (gatherSlots k) =
        (MatrixWordGather.Forward.cfg (some (.inr .test)) none
          (List.replicate (r.val*m) true) table []
          (List.replicate m true) []).stk k := by
    intro k
    cases k with
    | inl j =>
        fin_cases j <;>
          simp [S, priorBank, extra, gatherSlots,
            MatrixWordGather.Forward.cfg, hstart]
    | inr j =>
        fin_cases j <;>
          simp [S, priorBank, extra, gatherSlots,
            MatrixWordGather.Forward.cfg, hstart]
  obtain ⟨t₂,ht₂,h₂⟩ := gather_phase f r S hinput
  refine ⟨t₁+t₂, by dsimp [exactBound, r] at ht₂ ⊢; omega, ?_⟩
  simpa only [output, S, r, table] using (run_add h₁' t₂).trans h₂

theorem field_gather_output {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) :
    ∃ t ≤ exactBound code p ell f,
      (run t (source code p ell f)).l = none ∧
      (run t (source code p ell f)).stk (.inr 3) =
        MatrixStage4FamilyData.oneHot m (f (selectedRow code p ell)) := by
  obtain ⟨t,ht,he⟩ := field_gather_run code p ell f
  refine ⟨t,ht,?_,?_⟩
  all_goals rw [he]
  · rfl
  · simpa only [output, cfg, gatherSlots, MatrixWordGather.Forward.cfg] using
      (bank_at gatherSlots
        (priorBank (MatrixStage4TemplateFieldStart.fieldOutput code p ell m)
          m (MatrixStage4FamilyData.fieldTable f))
        (MatrixWordGather.Forward.cfg none none
          (List.replicate ((selectedRow code p ell).val*m+m) true)
          (MatrixStage4FamilyData.fieldTable f) [] []
          (MatrixStage4FamilyData.oneHot m (f (selectedRow code p ell)))).stk
        (.inr 1))

end EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldGather
