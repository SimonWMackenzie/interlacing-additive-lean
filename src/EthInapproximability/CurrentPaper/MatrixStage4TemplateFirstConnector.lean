import EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldDecode
import EthInapproximability.CurrentPaper.MatrixStage4FirstDigitMachine

/-!
# Physical handoff from selected family-first field to its source digit

The family-first field decoder and first-word digit controller are both fixed
programs. This owner transports the physically decoded coordinate and the
preserved first-word ordinal into the digit controller without supplying
either selected value at the start.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4TemplateFirstConnector

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

def wordSlot : MatrixStage4TemplateFieldDecode.Stack :=
  .inl (.inl (.inl (.inl 14)))

theorem decoded_word_preserved {a s q L cy m : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L)
    (f : Fin (L*q) → Fin m) :
    (MatrixStage4TemplateFieldDecode.output code p ell f).stk wordSlot =
      List.replicate
        (firstWordCode a s cy
          (((rawColumnCode a s q cy).symm code).2 p).2).val true := by
  unfold MatrixStage4TemplateFieldDecode.output
  dsimp only [MatrixStage4TemplateFieldDecode.cfg]
  rw [bank_outside MatrixStage4TemplateFieldDecode.decodeSlots _ _ wordSlot
    (by decide)]
  unfold MatrixStage4TemplateFieldDecode.priorBank
  change (MatrixStage4TemplateFieldGather.output code p ell f).stk
    (.inl (.inl (.inl 14))) = _
  unfold MatrixStage4TemplateFieldGather.output
  dsimp only [MatrixStage4TemplateFieldGather.cfg]
  rw [bank_outside MatrixStage4TemplateFieldGather.gatherSlots _ _
    (.inl (.inl (.inl 14))) (by decide)]
  unfold MatrixStage4TemplateFieldGather.priorBank
  change (MatrixStage4TemplateFieldStart.fieldOutput code p ell m).stk
    (.inl (.inl 14)) = _
  unfold MatrixStage4TemplateFieldStart.fieldOutput
  dsimp only [MatrixStage4TemplateFieldStart.cfg]
  rw [bank_outside MatrixStage4TemplateFieldStart.fieldSlots _ _
    (.inl (.inl 14)) (by decide)]
  unfold MatrixStage4TemplateFieldStart.priorBank
  change (MatrixStage4TemplateFieldStart.pairOutput code p ell).stk
    (.inl 14) = _
  unfold MatrixStage4TemplateFieldStart.pairOutput
  dsimp only [MatrixStage4TemplateEntryMachine.cfg]
  rw [bank_outside MatrixStage4TemplateEntryMachine.addressSlots _ _
    (.inl 14) (by decide)]
  simp only [MatrixStage4TemplateEntryMachine.columnBank, Sum.elim_inl,
    MatrixStage4TemplateEntryMachine.columnOutput,
    MatrixStage4ColumnMachine.cfg]
  rfl

theorem decoded_first_value {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    (MatrixStage4TemplateFieldDecode.output code p ell
      (MatrixStage4FamilyData.familyFirst family)).stk (.inr 0) =
      List.replicate
        (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1.val
        true := by
  simpa only [MatrixStage4TemplateFieldDecode.output,
    MatrixStage4TemplateFieldDecode.cfg,
    MatrixStage4TemplateFieldDecode.decodeSlots,
    MatrixStage4TemplateFieldGather.selectedRow,
    MatrixStage4FamilyData.familyFirst_at,
    MatrixStage4OneHot.cfg] using
    (bank_at MatrixStage4TemplateFieldDecode.decodeSlots
      (MatrixStage4TemplateFieldDecode.priorBank
        (MatrixStage4TemplateFieldGather.output code p ell
          (MatrixStage4FamilyData.familyFirst family)))
      (MatrixStage4OneHot.cfg none none
        (List.replicate
          (qOne a-1-
            (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1.val)
          false)
        (List.replicate
          (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1.val
          true)).stk 1)

abbrev Stack := MatrixStage4TemplateFieldDecode.Stack ⊕ Fin 24
abbrev Label := MatrixStage4TemplateFieldDecode.Label ⊕
  (Unit ⊕ MatrixStage4FirstDigitMachine.Label)
abbrev Control := MatrixStage4TemplateFieldDecode.Control ×
  MatrixStage4FirstDigitMachine.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def priorSlots : MatrixStage4TemplateFieldDecode.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def digitSlots : MatrixStage4FirstDigitMachine.Stack ↪ Stack where
  toFun
    | .inl 0 => .inr 0
    | .inl 1 => .inr 1
    | .inl 2 => .inr 2
    | .inl 3 => .inr 3
    | .inl 4 => .inr 4
    | .inl 5 => .inr 5
    | .inl 6 => .inr 6
    | .inl 7 => .inl (.inr 0)
    | .inl 8 => .inr 7
    | .inl 9 => .inr 8
    | .inl 10 => .inr 9
    | .inr 0 => .inl wordSlot
    | .inr 1 => .inr 10
    | .inr 2 => .inr 11
    | .inr 3 => .inr 12
    | .inr 4 => .inr 13
    | .inr 5 => .inr 14
    | .inr 6 => .inr 15
    | .inr 7 => .inr 16
    | .inr 8 => .inr 17
    | .inr 9 => .inr 18
    | .inr 10 => .inr 19
    | .inr 11 => .inr 20
    | .inr 12 => .inr 21
    | .inr 13 => .inr 22
    | .inr 14 => .inr 23
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [wordSlot]

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt priorSlots Sum.inl
      (fun v => (v,MatrixStage4FirstDigitMachine.initial)) Prod.fst
      (some (.inr (.inl ()))) (MatrixStage4TemplateFieldDecode.program l)
  | .inr (.inl ()) => load
      (fun _ => (MatrixStage4TemplateFieldDecode.initial,
        MatrixStage4FirstDigitMachine.initial))
      (goto (fun _ => .inr (.inr MatrixStage4FirstDigitMachine.start)))
  | .inr (.inr l) => stmt digitSlots (Sum.inr ∘ Sum.inr)
      (fun v => (MatrixStage4TemplateFieldDecode.initial,v)) Prod.snd none
      (MatrixStage4FirstDigitMachine.program l)

def start : Label := .inl MatrixStage4TemplateFieldDecode.start
def initial : Control :=
  (MatrixStage4TemplateFieldDecode.initial,MatrixStage4FirstDigitMachine.initial)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def extra (outer base exponent : ℕ) : Fin 24 → List Bool :=
  ![[true], List.replicate base true, [], [], [], [],
    List.replicate exponent true, [], [], [],
    List.replicate outer true, List.replicate base true, [true],
    [], [], [], [], [], [], [], [], [], [], []]

def priorBank (c : MatrixStage4TemplateFieldDecode.Config)
    (outer base exponent : ℕ) : Stack → List Bool :=
  Sum.elim c.stk (extra outer base exponent)

theorem prior_bank_eq (old new : MatrixStage4TemplateFieldDecode.Stack → List Bool)
    (foreign : Fin 24 → List Bool) :
    bank priorSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at priorSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem prior_phase (l : MatrixStage4TemplateFieldDecode.Label)
    (v : MatrixStage4TemplateFieldDecode.Control)
    (S : MatrixStage4TemplateFieldDecode.Stack → List Bool)
    (outer base exponent B : ℕ)
    (hhalt : (MatrixStage4TemplateFieldDecode.run B ⟨some l,v,S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l))
        (v,MatrixStage4FirstDigitMachine.initial)
        (priorBank ⟨some l,v,S⟩ outer base exponent)) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4TemplateFieldDecode.run B ⟨some l,v,S⟩).var,
          MatrixStage4FirstDigitMachine.initial)
        (priorBank (MatrixStage4TemplateFieldDecode.run B ⟨some l,v,S⟩)
          outer base exponent) := by
  let c : MatrixStage4TemplateFieldDecode.Config := ⟨some l,v,S⟩
  have hp (u : MatrixStage4TemplateFieldDecode.Label) :
      program (.inl u) = stmt priorSlots Sum.inl
        (fun w => (w,MatrixStage4FirstDigitMachine.initial)) Prod.fst
        (some (.inr (.inl ())))
        (MatrixStage4TemplateFieldDecode.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs priorSlots
    (priorBank c outer base exponent)
    Sum.inl (fun w => (w,MatrixStage4FirstDigitMachine.initial)) Prod.fst
    (by intro w; rfl) (some (.inr (.inl ())))
    MatrixStage4TemplateFieldDecode.program program hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4TemplateFieldDecode.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4TemplateFieldDecode.run, priorBank, c, prior_bank_eq,
    hhalt'] using he

theorem bridge (v : MatrixStage4TemplateFieldDecode.Control)
    (S : Stack → List Bool) :
    run 1 (cfg (some (.inr (.inl ())))
      (v,MatrixStage4FirstDigitMachine.initial) S) =
    cfg (some (.inr (.inr MatrixStage4FirstDigitMachine.start)))
      initial S := by
  simp [run, cfg, initial, advance, TM2.step, TM2.stepAux, program]

theorem digit_phase (S : Stack → List Bool)
    (c : MatrixStage4FirstDigitMachine.Config) (B : ℕ)
    (hstart : c.l = some MatrixStage4FirstDigitMachine.start)
    (hinput : ∀ k : MatrixStage4FirstDigitMachine.Stack,
      S (digitSlots k) = c.stk k)
    (hhalt : (MatrixStage4FirstDigitMachine.run B c).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inr (.inr MatrixStage4FirstDigitMachine.start)))
        (MatrixStage4TemplateFieldDecode.initial,c.var) S) =
      cfg none
        (MatrixStage4TemplateFieldDecode.initial,
          (MatrixStage4FirstDigitMachine.run B c).var)
        (bank digitSlots S (MatrixStage4FirstDigitMachine.run B c).stk) := by
  have hp (u : MatrixStage4FirstDigitMachine.Label) :
      program (.inr (.inr u)) = stmt digitSlots (Sum.inr ∘ Sum.inr)
        (fun v => (MatrixStage4TemplateFieldDecode.initial,v)) Prod.snd none
        (MatrixStage4FirstDigitMachine.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs digitSlots S (Sum.inr ∘ Sum.inr)
    (fun v => (MatrixStage4TemplateFieldDecode.initial,v)) Prod.snd
    (by intro v; rfl) none MatrixStage4FirstDigitMachine.program program
    hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hbank : bank digitSlots S c.stk = S :=
    bank_eq_self digitSlots S c.stk (by intro k; exact (hinput k).symm)
  have hhalt' : (((advance MatrixStage4FirstDigitMachine.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4FirstDigitMachine.run, hbank, hstart, hhalt'] using he

theorem digit_input_matches (S : MatrixStage4TemplateFieldDecode.Stack → List Bool)
    (n outer base exponent : ℕ) (pos : Fin (exponent+1))
    (hj : S (.inr 0) = List.replicate pos.val true)
    (hw : S wordSlot = List.replicate n true) :
    ∀ k : MatrixStage4FirstDigitMachine.Stack,
      priorBank ⟨none,MatrixStage4TemplateFieldDecode.initial,S⟩
        outer base exponent (digitSlots k) =
      (MatrixStage4FirstDigitMachine.source n outer base exponent pos).stk k := by
  intro k
  cases k with
  | inl j =>
      fin_cases j <;>
        simp [priorBank, extra, digitSlots,
          MatrixStage4FirstDigitMachine.source,
          MatrixStage4FirstDigitMachine.powerBank,
          MatrixStage4FirstDigitMachine.powerInput,
          MatrixStage4SelectedPower.cutFrame,
          MatrixStage4SelectedPower.cutStacks,
          MatrixStage4SelectedPower.cutPermutation,
          MatrixUnaryCut.cfg, MatrixStage4FirstDigitMachine.cfg,
          BitMachineEncoding.renameCfg, BitMachineComposition.liftCfg,
          finSumFinEquiv, hj] <;> rfl
  | inr j =>
      fin_cases j <;>
        simp [priorBank, extra, digitSlots,
          MatrixStage4FirstDigitMachine.source,
          MatrixStage4FirstDigitMachine.powerBank,
          MatrixStage4FirstDigitMachine.extra,
          MatrixStage4FirstDigitMachine.powerInput,
          MatrixStage4FirstDigitMachine.cfg, hw]

noncomputable def actualSource {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) : Config :=
  cfg (some start) initial
    (priorBank (MatrixStage4TemplateFieldDecode.source code p ell
      (MatrixStage4FamilyData.familyFirst family))
      (cy^(firstLength a s)) cy (firstLength a s-1))

def actualBound {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) : ℕ :=
  let γ := (((rawColumnCode a s q cy).symm code).2 p).2
  let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
  MatrixStage4TemplateFieldDecode.exactBound code p ell
    (MatrixStage4FamilyData.familyFirst family) + 1 +
    MatrixStage4FirstDigitMachine.digitBound
      (firstWordCode a s cy γ).val (cy^(firstLength a s)) cy
      (firstLength a s-1) (MatrixStage4FirstDigitMachine.firstPosition (s := s) j)

/-- The selected first-coordinate source symbol is produced from the original
raw column ordinal and complete literal family-first table by a single fixed
program. The family field, first-word ordinal, stride, and symbol are never
preloaded as selected inputs. -/
theorem actual_first_symbol {a s q L rx cy : ℕ}
    (family : SecondFamily a q L (Fin rx))
    (code : Fin (cols a s q cy)) (p : Fin s) (ell : Fin L) :
    let γ := (((rawColumnCode a s q cy).symm code).2 p).2
    let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
    ∃ t ≤ actualBound family code p ell,
      (run t (actualSource family code p ell)).l = none ∧
      (run t (actualSource family code p ell)).stk (.inr 23) =
        List.replicate (γ (firstCoordinate a s j)).val true := by
  dsimp
  let γ := (((rawColumnCode a s q cy).symm code).2 p).2
  let j := (family ell (MatrixStage4TemplateFieldGather.selectedFin code p)).1
  let pos := MatrixStage4FirstDigitMachine.firstPosition (s := s) j
  let n := (firstWordCode a s cy γ).val
  let outer := cy^(firstLength a s)
  let exponent := firstLength a s-1
  let f := MatrixStage4FamilyData.familyFirst family
  let cDigit := MatrixStage4FirstDigitMachine.source n outer cy exponent pos
  obtain ⟨tp,htp,hp⟩ :=
    MatrixStage4TemplateFieldDecode.field_decode_run code p ell f
  have hh : (MatrixStage4TemplateFieldDecode.run tp
      (MatrixStage4TemplateFieldDecode.source code p ell f)).l = none := by
    rw [hp]
    rfl
  obtain ⟨t₁,ht₁,h₁⟩ := prior_phase
    MatrixStage4TemplateFieldDecode.start
    MatrixStage4TemplateFieldDecode.initial
    (MatrixStage4TemplateFieldDecode.source code p ell f).stk
    outer cy exponent tp hh
  have h₁' : run t₁ (actualSource family code p ell) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4TemplateFieldDecode.output code p ell f).var,
          MatrixStage4FirstDigitMachine.initial)
        (priorBank (MatrixStage4TemplateFieldDecode.output code p ell f)
          outer cy exponent) := by
    simp only [MatrixStage4TemplateFieldDecode.source,
      MatrixStage4TemplateFieldDecode.cfg] at hp h₁
    rw [hp] at h₁
    simpa only [actualSource, start, initial, outer, exponent, f] using h₁
  let S := priorBank (MatrixStage4TemplateFieldDecode.output code p ell f)
    outer cy exponent
  have hj : (MatrixStage4TemplateFieldDecode.output code p ell f).stk
      (.inr 0) = List.replicate pos.val true := by
    simpa only [f, pos, MatrixStage4FirstDigitMachine.firstPosition_val] using
      decoded_first_value family code p ell
  have hw : (MatrixStage4TemplateFieldDecode.output code p ell f).stk
      wordSlot = List.replicate n true := by
    simpa only [f, n, γ] using decoded_word_preserved code p ell f
  have hinput : ∀ k : MatrixStage4FirstDigitMachine.Stack,
      S (digitSlots k) = cDigit.stk k := by
    intro k
    simpa only [S, cDigit] using
      digit_input_matches
        (MatrixStage4TemplateFieldDecode.output code p ell f).stk
        n outer cy exponent pos hj hw k
  obtain ⟨td,htd,hd,hsymbol⟩ :=
    MatrixStage4FirstDigitMachine.first_word_digit_output γ j
  have hd' : (MatrixStage4FirstDigitMachine.run td cDigit).l = none := by
    simpa only [cDigit, n, outer, exponent, pos] using hd
  have hsymbol' : (MatrixStage4FirstDigitMachine.run td cDigit).stk
      (.inr 14) = List.replicate (γ (firstCoordinate a s j)).val true := by
    simpa only [cDigit, n, outer, exponent, pos] using hsymbol
  have hstart : cDigit.l = some MatrixStage4FirstDigitMachine.start := rfl
  have hvar : cDigit.var = MatrixStage4FirstDigitMachine.initial := by
    rfl
  obtain ⟨t₂,ht₂,h₂⟩ := digit_phase S cDigit td hstart hinput hd'
  have h12 := run_add h₁' 1
  rw [bridge] at h12
  have h123 := run_add h12 t₂
  change run (t₁+1+t₂) (actualSource family code p ell) =
    run t₂ (cfg (some (.inr (.inr MatrixStage4FirstDigitMachine.start)))
      (MatrixStage4TemplateFieldDecode.initial,
        MatrixStage4FirstDigitMachine.initial) S) at h123
  rw [← hvar, h₂] at h123
  refine ⟨t₁+1+t₂, ?_, ?_, ?_⟩
  · dsimp [actualBound, f, γ, j, pos, n, outer, exponent] at htp htd ⊢
    omega
  · rw [h123]
    rfl
  · rw [h123]
    have hout := bank_at digitSlots S
      (MatrixStage4FirstDigitMachine.run td cDigit).stk (.inr 14)
    simpa only [cfg, digitSlots, hsymbol'] using hout

end EthInapproximability.CurrentPaper.MatrixStage4TemplateFirstConnector
