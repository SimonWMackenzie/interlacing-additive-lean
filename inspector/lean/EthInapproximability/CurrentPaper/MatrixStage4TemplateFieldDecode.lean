import EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldGather

/-!
# Physical decode of a gathered template family field

The literal one-hot word is gathered from the full family table by the prior
fixed controller. This fixed final phase consumes that word and writes its
selected index in unary, without putting the index in control or input.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldDecode

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4TemplateFieldGather.Stack ⊕ Fin 1
abbrev Label := MatrixStage4TemplateFieldGather.Label ⊕ Unit
abbrev Control := MatrixStage4TemplateFieldGather.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def priorSlots : MatrixStage4TemplateFieldGather.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def decodeSlots : Fin 2 ↪ Stack where
  toFun := ![Sum.inl (.inr 3), Sum.inr 0]
  inj' := by decide

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt priorSlots Sum.inl (fun v => (v,none)) Prod.fst
      (some (.inr ())) (MatrixStage4TemplateFieldGather.program l)
  | .inr l => stmt decodeSlots Sum.inr
      (fun v => (MatrixStage4TemplateFieldGather.initial,v)) Prod.snd none
      (MatrixStage4OneHot.program l)

def start : Label := .inl MatrixStage4TemplateFieldGather.start
def initial : Control := (MatrixStage4TemplateFieldGather.initial,none)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def priorBank (c : MatrixStage4TemplateFieldGather.Config) : Stack → List Bool :=
  Sum.elim c.stk (![[]] : Fin 1 → List Bool)

theorem prior_bank_eq (old new : MatrixStage4TemplateFieldGather.Stack → List Bool)
    (foreign : Fin 1 → List Bool) :
    bank priorSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at priorSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem prior_phase (l : MatrixStage4TemplateFieldGather.Label)
    (v : MatrixStage4TemplateFieldGather.Control)
    (S : MatrixStage4TemplateFieldGather.Stack → List Bool)
    (B : ℕ)
    (hhalt : (MatrixStage4TemplateFieldGather.run B ⟨some l,v,S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l)) (v,none)
        (priorBank ⟨some l,v,S⟩)) =
      cfg (some (.inr ()))
        ((MatrixStage4TemplateFieldGather.run B ⟨some l,v,S⟩).var,none)
        (priorBank (MatrixStage4TemplateFieldGather.run B ⟨some l,v,S⟩)) := by
  let c : MatrixStage4TemplateFieldGather.Config := ⟨some l,v,S⟩
  have hp (u : MatrixStage4TemplateFieldGather.Label) :
      program (.inl u) = stmt priorSlots Sum.inl
        (fun w => (w,none)) Prod.fst (some (.inr ()))
        (MatrixStage4TemplateFieldGather.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs priorSlots (priorBank c)
    Sum.inl (fun w => (w,none)) Prod.fst (by intro w; rfl)
    (some (.inr ())) MatrixStage4TemplateFieldGather.program program
    hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4TemplateFieldGather.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4TemplateFieldGather.run, priorBank, c, prior_bank_eq,
    hhalt'] using he

theorem decode_phase {rows m : ℕ} (f : Fin rows → Fin m)
    (r : Fin rows) (S : Stack → List Bool)
    (hinput : ∀ k : Fin 2,
      S (decodeSlots k) =
        (MatrixStage4OneHot.cfg (some ()) none
          (MatrixStage4FamilyData.oneHot m (f r)) []).stk k) :
    ∃ t ≤ (f r).val+1,
      run t (cfg (some (.inr ())) initial S) =
        cfg none initial
          (bank decodeSlots S
            (MatrixStage4OneHot.cfg none none
              (List.replicate (m-1-(f r).val) false)
              (List.replicate (f r).val true)).stk) := by
  let c := MatrixStage4OneHot.cfg (some ()) none
    (MatrixStage4FamilyData.oneHot m (f r)) []
  let out := MatrixStage4OneHot.cfg none none
    (List.replicate (m-1-(f r).val) false)
    (List.replicate (f r).val true)
  have hrun : MatrixStage4OneHot.run ((f r).val+1) c = out :=
    MatrixStage4FamilyData.field_decode_run f r
  have hhalt : (((advance MatrixStage4OneHot.program)^[(f r).val+1]) c).l = none := by
    rw [← MatrixStage4OneHot.run, hrun]
    rfl
  have hp (u : Unit) :
      program (.inr u) = stmt decodeSlots Sum.inr
        (fun v => (MatrixStage4TemplateFieldGather.initial,v)) Prod.snd none
        (MatrixStage4OneHot.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs decodeSlots S Sum.inr
    (fun v => (MatrixStage4TemplateFieldGather.initial,v)) Prod.snd
    (by intro v; rfl) none MatrixStage4OneHot.program program
    hp c ((f r).val+1) hhalt
  refine ⟨t,ht,?_⟩
  have hbank : bank decodeSlots S c.stk = S :=
    bank_eq_self decodeSlots S c.stk (by intro k; exact (hinput k).symm)
  rw [show (((advance MatrixStage4OneHot.program)^[(f r).val+1]) c) = out from hrun] at he
  simpa only [run, cfg, initial, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    c, out, hbank] using he

noncomputable def source {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) : Config :=
  cfg (some start) initial
    (priorBank (MatrixStage4TemplateFieldGather.source code p ell f))

noncomputable def output {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) : Config :=
  let r := MatrixStage4TemplateFieldGather.selectedRow code p ell
  let S := priorBank (MatrixStage4TemplateFieldGather.output code p ell f)
  cfg none initial
    (bank decodeSlots S
      (MatrixStage4OneHot.cfg none none
        (List.replicate (m-1-(f r).val) false)
        (List.replicate (f r).val true)).stk)

def exactBound {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) : ℕ :=
  MatrixStage4TemplateFieldGather.exactBound code p ell f +
    (f (MatrixStage4TemplateFieldGather.selectedRow code p ell)).val+1

theorem field_decode_run {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) :
    ∃ t ≤ exactBound code p ell f,
      run t (source code p ell f) = output code p ell f := by
  let r := MatrixStage4TemplateFieldGather.selectedRow code p ell
  obtain ⟨tp,htp,hp⟩ :=
    MatrixStage4TemplateFieldGather.field_gather_run code p ell f
  have hh : (MatrixStage4TemplateFieldGather.run tp
      (MatrixStage4TemplateFieldGather.source code p ell f)).l = none := by
    rw [hp]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := prior_phase
    MatrixStage4TemplateFieldGather.start
    MatrixStage4TemplateFieldGather.initial
    (MatrixStage4TemplateFieldGather.source code p ell f).stk tp hh
  have h₁' : run t₁ (source code p ell f) =
      cfg (some (.inr ())) initial
        (priorBank (MatrixStage4TemplateFieldGather.output code p ell f)) := by
    simp only [MatrixStage4TemplateFieldGather.source,
      MatrixStage4TemplateFieldGather.cfg] at hp h₁
    rw [hp] at h₁
    simpa only [source, start, initial] using h₁
  let S := priorBank (MatrixStage4TemplateFieldGather.output code p ell f)
  have honeHot :
      (MatrixStage4TemplateFieldGather.output code p ell f).stk (.inr 3) =
        MatrixStage4FamilyData.oneHot m (f r) := by
    simpa only [MatrixStage4TemplateFieldGather.output,
      MatrixStage4TemplateFieldGather.cfg,
      MatrixStage4TemplateFieldGather.gatherSlots,
      MatrixWordGather.Forward.cfg] using
      (bank_at MatrixStage4TemplateFieldGather.gatherSlots
        (MatrixStage4TemplateFieldGather.priorBank
          (MatrixStage4TemplateFieldStart.fieldOutput code p ell m)
          m (MatrixStage4FamilyData.fieldTable f))
        (MatrixWordGather.Forward.cfg none none
          (List.replicate (r.val*m+m) true)
          (MatrixStage4FamilyData.fieldTable f) [] []
          (MatrixStage4FamilyData.oneHot m (f r))).stk (.inr 1))
  have hinput : ∀ k : Fin 2,
      S (decodeSlots k) =
        (MatrixStage4OneHot.cfg (some ()) none
          (MatrixStage4FamilyData.oneHot m (f r)) []).stk k := by
    intro k
    fin_cases k <;>
      simp [S, priorBank, decodeSlots, MatrixStage4OneHot.cfg, honeHot]
  obtain ⟨t₂,ht₂,h₂⟩ := decode_phase f r S hinput
  refine ⟨t₁+t₂, by dsimp [exactBound, r] at ht₂ ⊢; omega, ?_⟩
  simpa only [output, S, r] using (run_add h₁' t₂).trans h₂

theorem field_decode_output {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) :
    ∃ t ≤ exactBound code p ell f,
      (run t (source code p ell f)).l = none ∧
      (run t (source code p ell f)).stk (.inr 0) =
        List.replicate
          (f (MatrixStage4TemplateFieldGather.selectedRow code p ell)).val
          true := by
  obtain ⟨t,ht,he⟩ := field_decode_run code p ell f
  refine ⟨t,ht,?_,?_⟩
  all_goals rw [he]
  · rfl
  · simpa only [output, cfg, decodeSlots, MatrixStage4OneHot.cfg] using
      (bank_at decodeSlots
        (priorBank (MatrixStage4TemplateFieldGather.output code p ell f))
        (MatrixStage4OneHot.cfg none none
          (List.replicate
            (m-1-(f (MatrixStage4TemplateFieldGather.selectedRow code p ell)).val)
            false)
          (List.replicate
            (f (MatrixStage4TemplateFieldGather.selectedRow code p ell)).val
            true)).stk 1)

/-- The first-coordinate field of the actual Stage--4 family, obtained by
running the fixed decoder on its complete literal one-hot table. -/
theorem family_first_output {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    ∃ t ≤ exactBound code p ell (MatrixStage4FamilyData.familyFirst family),
      (run t (source code p ell
        (MatrixStage4FamilyData.familyFirst family))).l = none ∧
      (run t (source code p ell
        (MatrixStage4FamilyData.familyFirst family))).stk (.inr 0) =
        List.replicate
          (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1.val
          true := by
  simpa only [MatrixStage4TemplateFieldGather.selectedRow,
    MatrixStage4FamilyData.familyFirst_at] using
    field_decode_output code p ell (MatrixStage4FamilyData.familyFirst family)

/-- The source-row field is decoded by the same fixed program with the other
literal table and its unary width. -/
theorem family_row_output {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    ∃ t ≤ exactBound code p ell (MatrixStage4FamilyData.familyRow family),
      (run t (source code p ell
        (MatrixStage4FamilyData.familyRow family))).l = none ∧
      (run t (source code p ell
        (MatrixStage4FamilyData.familyRow family))).stk (.inr 0) =
        List.replicate
          (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).2.val
          true := by
  simpa only [MatrixStage4TemplateFieldGather.selectedRow,
    MatrixStage4FamilyData.familyRow_at] using
    field_decode_output code p ell (MatrixStage4FamilyData.familyRow family)

end EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldDecode
