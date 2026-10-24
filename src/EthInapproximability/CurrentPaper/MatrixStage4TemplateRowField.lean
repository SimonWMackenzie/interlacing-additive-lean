import EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldDecode

/-!
# Reusing the fixed family-field suffix on a computed pair address

The selector/first-field controller has already produced `ℓ*q+α`.  Starting
at the *internal* field-address label of the same fixed field decoder, this
run computes the row-field table offset, gathers its one-hot word from the
full literal table, and decodes it to unary. This is a local suffix theorem;
the later connector supplies the pair address physically.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateRowField

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4TemplateFieldDecode.Stack
abbrev Label := MatrixStage4TemplateFieldDecode.Label
abbrev Control := MatrixStage4TemplateFieldDecode.Control
abbrev Config := MatrixStage4TemplateFieldDecode.Config

def start : Label := .inl (.inl (.inr .outer))
def initial : Control := MatrixStage4TemplateFieldDecode.initial
def run := MatrixStage4TemplateFieldDecode.run

def pairExtra (row : ℕ) : Fin 5 → List Bool :=
  ![[], [], [], [], List.replicate row true]

def entryBank (row : ℕ) : MatrixStage4TemplateEntryMachine.Stack → List Bool :=
  Sum.elim (fun _ : MatrixStage4ColumnMachine.Stack => []) (pairExtra row)

def addressBank (row width : ℕ) : MatrixStage4TemplateFieldStart.Stack → List Bool :=
  Sum.elim (entryBank row) (MatrixStage4TemplateFieldStart.extra width)

def gatherBank (row width : ℕ) (table : List Bool) :
    MatrixStage4TemplateFieldGather.Stack → List Bool :=
  Sum.elim (addressBank row width) (MatrixStage4TemplateFieldGather.extra width table)

def decodeBank (row width : ℕ) (table : List Bool) : Stack → List Bool :=
  Sum.elim (gatherBank row width table) (![[]] : Fin 1 → List Bool)

def input {rows width : ℕ} (f : Fin rows → Fin width)
    (r : Fin rows) : Config :=
  MatrixStage4TemplateFieldDecode.cfg (some start) initial
    (decodeBank r.val width (MatrixStage4FamilyData.fieldTable f))

noncomputable def addressResult (row width : ℕ) :
    MatrixStage4TemplateFieldStart.Stack → List Bool :=
  bank MatrixStage4TemplateFieldStart.fieldSlots (addressBank row width)
    (MatrixAddressMachine.cfg none false
      (List.replicate row true) (List.replicate width true)
      [] [] [] (List.replicate (row*width) true)).stk

theorem address_run (row width : ℕ) :
    ∃ t ≤ MatrixAddressMachine.exactTime row width 0,
      MatrixStage4TemplateFieldStart.run t
        (MatrixStage4TemplateFieldStart.cfg
          (some (.inr .outer)) MatrixStage4TemplateFieldStart.initial
          (addressBank row width)) =
      MatrixStage4TemplateFieldStart.cfg none
        MatrixStage4TemplateFieldStart.initial
        (addressResult row width) := by
  have hinput : ∀ k : Fin 6,
      addressBank row width (MatrixStage4TemplateFieldStart.fieldSlots k) =
        (MatrixAddressMachine.cfg (some .outer) false
          (List.replicate row true) (List.replicate width true)
          [] [] [] []).stk k := by
    intro k
    fin_cases k <;>
      simp [addressBank, entryBank, pairExtra,
        MatrixStage4TemplateFieldStart.extra,
        MatrixStage4TemplateFieldStart.fieldSlots,
        MatrixAddressMachine.cfg]
  simpa only [addressResult] using
    MatrixStage4TemplateFieldStart.field_phase
      (addressBank row width) row width hinput

noncomputable def gatherResult {rows width : ℕ}
    (f : Fin rows → Fin width) (r : Fin rows) :
    MatrixStage4TemplateFieldGather.Stack → List Bool :=
  let S := MatrixStage4TemplateFieldGather.priorBank
    (MatrixStage4TemplateFieldStart.cfg none
      MatrixStage4TemplateFieldStart.initial (addressResult r.val width))
    width (MatrixStage4FamilyData.fieldTable f)
  bank MatrixStage4TemplateFieldGather.gatherSlots S
    (MatrixWordGather.Forward.cfg none none
      (List.replicate (r.val*width+width) true)
      (MatrixStage4FamilyData.fieldTable f) [] []
      (MatrixStage4FamilyData.oneHot width (f r))).stk

def gatherBound {rows width : ℕ} (r : Fin rows) : ℕ :=
  MatrixAddressMachine.exactTime r.val width 0 +
    width * (3*(r.val*width+width)+3*(rows*width)+11)+2

theorem gather_run {rows width : ℕ}
    (f : Fin rows → Fin width) (r : Fin rows) :
    ∃ t ≤ gatherBound (width := width) r,
      MatrixStage4TemplateFieldGather.run t
        (MatrixStage4TemplateFieldGather.cfg
          (some (.inl (.inr .outer)))
          MatrixStage4TemplateFieldGather.initial
          (gatherBank r.val width (MatrixStage4FamilyData.fieldTable f))) =
      MatrixStage4TemplateFieldGather.cfg none
        MatrixStage4TemplateFieldGather.initial (gatherResult f r) := by
  let table := MatrixStage4FamilyData.fieldTable f
  obtain ⟨ta,hta,ha⟩ := address_run r.val width
  have hh : (MatrixStage4TemplateFieldStart.run ta
      (MatrixStage4TemplateFieldStart.cfg (some (.inr .outer))
        MatrixStage4TemplateFieldStart.initial
        (addressBank r.val width))).l = none := by
    rw [ha]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := MatrixStage4TemplateFieldGather.prior_phase
    (.inr .outer) MatrixStage4TemplateFieldStart.initial
    (addressBank r.val width) width ta table hh
  have h₁' : MatrixStage4TemplateFieldGather.run t₁
      (MatrixStage4TemplateFieldGather.cfg
        (some (.inl (.inr .outer)))
        MatrixStage4TemplateFieldGather.initial
        (gatherBank r.val width table)) =
      MatrixStage4TemplateFieldGather.cfg (some (.inr (.inr .test)))
        MatrixStage4TemplateFieldGather.initial
        (MatrixStage4TemplateFieldGather.priorBank
          (MatrixStage4TemplateFieldStart.cfg none
            MatrixStage4TemplateFieldStart.initial
            (addressResult r.val width)) width table) := by
    simp only [MatrixStage4TemplateFieldStart.cfg] at ha h₁
    rw [ha] at h₁
    simpa only [MatrixStage4TemplateFieldGather.initial,
      MatrixStage4TemplateFieldGather.gatherInitial,
      gatherBank, MatrixStage4TemplateFieldGather.priorBank,
      MatrixStage4TemplateFieldGather.cfg] using h₁
  let S := MatrixStage4TemplateFieldGather.priorBank
    (MatrixStage4TemplateFieldStart.cfg none
      MatrixStage4TemplateFieldStart.initial (addressResult r.val width))
    width table
  have haddr : (addressResult r.val width) (.inr 4) =
      List.replicate (r.val*width) true := by
    simpa only [addressResult,
      MatrixStage4TemplateFieldStart.fieldSlots,
      MatrixAddressMachine.cfg] using
      (bank_at MatrixStage4TemplateFieldStart.fieldSlots
        (addressBank r.val width)
        (MatrixAddressMachine.cfg none false
          (List.replicate r.val true) (List.replicate width true)
          [] [] [] (List.replicate (r.val*width) true)).stk 5)
  have hinput : ∀ k : MatrixWordGather.Forward.Stack,
      S (MatrixStage4TemplateFieldGather.gatherSlots k) =
        (MatrixWordGather.Forward.cfg (some (.inr .test)) none
          (List.replicate (r.val*width) true) table []
          (List.replicate width true) []).stk k := by
    intro k
    cases k with
    | inl j =>
        fin_cases j <;>
          simp [S, MatrixStage4TemplateFieldGather.priorBank,
            MatrixStage4TemplateFieldGather.extra,
            MatrixStage4TemplateFieldGather.gatherSlots,
            MatrixWordGather.Forward.cfg,
            MatrixStage4TemplateFieldStart.cfg, haddr]
    | inr j =>
        fin_cases j <;>
          simp [S, MatrixStage4TemplateFieldGather.priorBank,
            MatrixStage4TemplateFieldGather.extra,
            MatrixStage4TemplateFieldGather.gatherSlots,
            MatrixWordGather.Forward.cfg]
  obtain ⟨t₂,ht₂,h₂⟩ :=
    MatrixStage4TemplateFieldGather.gather_phase f r S hinput
  refine ⟨t₁+t₂, by dsimp [gatherBound] at hta ht₂ ⊢; omega, ?_⟩
  simpa only [gatherResult, S, table] using
    (MatrixStage4TemplateFieldGather.run_add h₁' t₂).trans h₂

noncomputable def decodeResult {rows width : ℕ}
    (f : Fin rows → Fin width) (r : Fin rows) : Stack → List Bool :=
  let S := MatrixStage4TemplateFieldDecode.priorBank
    (MatrixStage4TemplateFieldGather.cfg none
      MatrixStage4TemplateFieldGather.initial (gatherResult f r))
  bank MatrixStage4TemplateFieldDecode.decodeSlots S
    (MatrixStage4OneHot.cfg none none
      (List.replicate (width-1-(f r).val) false)
      (List.replicate (f r).val true)).stk

def decodeBound {rows width : ℕ} (f : Fin rows → Fin width)
    (r : Fin rows) : ℕ :=
  gatherBound (width := width) r + (f r).val+1

theorem decode_run {rows width : ℕ}
    (f : Fin rows → Fin width) (r : Fin rows) :
    ∃ t ≤ decodeBound f r,
      run t (input f r) =
        MatrixStage4TemplateFieldDecode.cfg none initial (decodeResult f r) := by
  let table := MatrixStage4FamilyData.fieldTable f
  obtain ⟨tg,htg,hg⟩ := gather_run f r
  have hh : (MatrixStage4TemplateFieldGather.run tg
      (MatrixStage4TemplateFieldGather.cfg
        (some (.inl (.inr .outer)))
        MatrixStage4TemplateFieldGather.initial
        (gatherBank r.val width table))).l = none := by
    rw [hg]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := MatrixStage4TemplateFieldDecode.prior_phase
    (.inl (.inr .outer)) MatrixStage4TemplateFieldGather.initial
    (gatherBank r.val width table) tg hh
  have h₁' : run t₁ (input f r) =
      MatrixStage4TemplateFieldDecode.cfg (some (.inr ())) initial
        (MatrixStage4TemplateFieldDecode.priorBank
          (MatrixStage4TemplateFieldGather.cfg none
            MatrixStage4TemplateFieldGather.initial
            (gatherResult f r))) := by
    simp only [MatrixStage4TemplateFieldGather.cfg] at hg h₁
    rw [hg] at h₁
    simpa only [run, input, start, initial, decodeBank,
      MatrixStage4TemplateFieldDecode.priorBank,
      MatrixStage4TemplateFieldDecode.cfg] using h₁
  let S := MatrixStage4TemplateFieldDecode.priorBank
    (MatrixStage4TemplateFieldGather.cfg none
      MatrixStage4TemplateFieldGather.initial (gatherResult f r))
  have honeHot : (gatherResult f r) (.inr 3) =
      MatrixStage4FamilyData.oneHot width (f r) := by
    simpa only [gatherResult,
      MatrixStage4TemplateFieldGather.gatherSlots,
      MatrixWordGather.Forward.cfg] using
      (bank_at MatrixStage4TemplateFieldGather.gatherSlots
        (MatrixStage4TemplateFieldGather.priorBank
          (MatrixStage4TemplateFieldStart.cfg none
            MatrixStage4TemplateFieldStart.initial
            (addressResult r.val width))
          width table)
        (MatrixWordGather.Forward.cfg none none
          (List.replicate (r.val*width+width) true)
          table [] [] (MatrixStage4FamilyData.oneHot width (f r))).stk
        (.inr 1))
  have hinput : ∀ k : Fin 2,
      S (MatrixStage4TemplateFieldDecode.decodeSlots k) =
        (MatrixStage4OneHot.cfg (some ()) none
          (MatrixStage4FamilyData.oneHot width (f r)) []).stk k := by
    intro k
    fin_cases k <;>
      simp [S, MatrixStage4TemplateFieldDecode.priorBank,
        MatrixStage4TemplateFieldDecode.decodeSlots,
        MatrixStage4OneHot.cfg,
        MatrixStage4TemplateFieldGather.cfg, honeHot]
  obtain ⟨t₂,ht₂,h₂⟩ :=
    MatrixStage4TemplateFieldDecode.decode_phase f r S hinput
  refine ⟨t₁+t₂, by dsimp [decodeBound] at htg ht₂ ⊢; omega, ?_⟩
  simpa only [decodeResult, S, run] using
    (MatrixStage4TemplateFieldDecode.run_add h₁' t₂).trans h₂

theorem output {rows width : ℕ}
    (f : Fin rows → Fin width) (r : Fin rows) :
    ∃ t ≤ decodeBound f r,
      (run t (input f r)).l = none ∧
      (run t (input f r)).stk (.inr 0) =
        List.replicate (f r).val true := by
  obtain ⟨t,ht,he⟩ := decode_run f r
  refine ⟨t,ht,?_,?_⟩
  all_goals rw [he]
  · rfl
  · simpa only [decodeResult, MatrixStage4TemplateFieldDecode.cfg,
      MatrixStage4TemplateFieldDecode.decodeSlots,
      MatrixStage4OneHot.cfg] using
      (bank_at MatrixStage4TemplateFieldDecode.decodeSlots
        (MatrixStage4TemplateFieldDecode.priorBank
          (MatrixStage4TemplateFieldGather.cfg none
            MatrixStage4TemplateFieldGather.initial (gatherResult f r)))
        (MatrixStage4OneHot.cfg none none
          (List.replicate (width-1-(f r).val) false)
          (List.replicate (f r).val true)).stk 1)

end EthInapproximability.CurrentPaper.MatrixStage4TemplateRowField
