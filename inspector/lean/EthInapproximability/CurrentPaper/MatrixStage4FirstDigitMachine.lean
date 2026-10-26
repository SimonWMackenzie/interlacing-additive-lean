import EthInapproximability.CurrentPaper.MatrixStage4TemplateFieldDecode
import EthInapproximability.CurrentPaper.MatrixStage4SelectedPower

/-!
# Charged first-word digit from a selected coordinate

The first-coordinate family field has already been physically decoded to a
unary index by `MatrixStage4TemplateFieldDecode`. This separate fixed program
computes the corresponding unary base power and extracts that digit from a
unary first-word ordinal. It does not start with the stride or digit.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4FirstDigitMachine

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineStackEmbedding
open Construction MatrixStage4Codes MatrixStage4Digits MatrixMaterialization

abbrev Stack := MatrixStage4SelectedPower.Stack ⊕ Fin 15
abbrev Label := MatrixStage4SelectedPower.Label ⊕
  (Unit ⊕ MatrixStage4ColumnMachine.Label)
abbrev Control := MatrixStage4SelectedPower.Control × MatrixStage4ColumnMachine.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def powerSlots : MatrixStage4SelectedPower.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def digitSlots : MatrixStage4ColumnMachine.Stack ↪ Stack where
  toFun := ![Sum.inr 0, Sum.inr 1, Sum.inl 0, Sum.inr 2,
    Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6,
    Sum.inr 7, Sum.inr 8, Sum.inr 9, Sum.inr 10,
    Sum.inr 11, Sum.inr 12, Sum.inr 13, Sum.inr 14]
  inj' := by decide

def saved : MatrixStage4SelectedPower.Control :=
  ((false,false),(false,false))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => stmt powerSlots Sum.inl
      (fun v => (v,MatrixStage4ColumnMachine.initial)) Prod.fst
      (some (.inr (.inl ())))
      (MatrixStage4SelectedPower.program l)
  | .inr (.inl ()) => load (fun v => (saved,v.2))
      (goto (fun _ => .inr (.inr MatrixStage4ColumnMachine.outerStart)))
  | .inr (.inr l) => stmt digitSlots (Sum.inr ∘ Sum.inr)
      (fun v => (saved,v)) Prod.snd none
      (MatrixStage4ColumnMachine.program l)

def start : Label := .inl MatrixStage4SelectedPower.cutStart
def initial : Control := (((false,true),(false,false)),MatrixStage4ColumnMachine.initial)
def cfg (l : Option Label) (v : Control) (S : Stack → List Bool) : Config :=
  ⟨l,v,S⟩
def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def extra (n outer base : ℕ) : Fin 15 → List Bool :=
  ![List.replicate n true, List.replicate outer true,
    List.replicate base true, [true], [], [], [], [], [], [], [], [], [], [], []]

def powerBank (c : MatrixStage4SelectedPower.Config)
    (n outer base : ℕ) : Stack → List Bool :=
  Sum.elim c.stk (extra n outer base)

theorem power_bank_eq (old new : MatrixStage4SelectedPower.Stack → List Bool)
    (foreign : Fin 15 → List Bool) :
    bank powerSlots (Sum.elim old foreign) new = Sum.elim new foreign := by
  funext k
  cases k with
  | inl j => exact bank_at powerSlots (Sum.elim old foreign) new j
  | inr j =>
      apply bank_outside
      rintro ⟨i, hi⟩
      cases hi

theorem power_phase (l : MatrixStage4SelectedPower.Label)
    (v : MatrixStage4SelectedPower.Control)
    (S : MatrixStage4SelectedPower.Stack → List Bool)
    (n outer base B : ℕ)
    (hhalt : (MatrixStage4SelectedPower.run B ⟨some l,v,S⟩).l = none) :
    ∃ t ≤ B,
      run t (cfg (some (.inl l)) (v,MatrixStage4ColumnMachine.initial)
        (powerBank ⟨some l,v,S⟩ n outer base)) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4SelectedPower.run B ⟨some l,v,S⟩).var,
          MatrixStage4ColumnMachine.initial)
        (powerBank (MatrixStage4SelectedPower.run B ⟨some l,v,S⟩)
          n outer base) := by
  let c : MatrixStage4SelectedPower.Config := ⟨some l,v,S⟩
  have hp (u : MatrixStage4SelectedPower.Label) :
      program (.inl u) = stmt powerSlots Sum.inl
        (fun w => (w,MatrixStage4ColumnMachine.initial)) Prod.fst
        (some (.inr (.inl ())))
        (MatrixStage4SelectedPower.program u) := rfl
  obtain ⟨t,ht,he⟩ := outputs powerSlots (powerBank c n outer base)
    Sum.inl (fun w => (w,MatrixStage4ColumnMachine.initial)) Prod.fst
    (by intro w; rfl) (some (.inr (.inl ())))
    MatrixStage4SelectedPower.program program hp c B hhalt
  refine ⟨t,ht,?_⟩
  have hhalt' : (((advance MatrixStage4SelectedPower.program)^[B]) c).l = none :=
    hhalt
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    MatrixStage4SelectedPower.run, powerBank, c, power_bank_eq,
    hhalt'] using he

theorem bridge (old : MatrixStage4SelectedPower.Control)
    (S : Stack → List Bool) :
    run 1 (cfg (some (.inr (.inl ())))
      (old,MatrixStage4ColumnMachine.initial) S) =
    cfg (some (.inr (.inr MatrixStage4ColumnMachine.outerStart)))
      (saved,MatrixStage4ColumnMachine.initial) S := by
  simp [run, cfg, advance, TM2.step, TM2.stepAux, program]

theorem digit_phase (S : Stack → List Bool)
    (n outer stride base : ℕ)
    (hinput : ∀ k : MatrixStage4ColumnMachine.Stack,
      S (digitSlots k) =
        (MatrixStage4ColumnMachine.cfg
          (some MatrixStage4ColumnMachine.outerStart)
          MatrixStage4ColumnMachine.initial
          (List.replicate n true) (List.replicate outer true)
          (List.replicate stride true) (List.replicate base true)
          [true] [] [] [] [] [] [] [] []).stk k) :
    ∃ t ≤ MatrixUnaryDivision.totalTime n outer +
        MatrixUnaryDivision.totalTime (n%outer) stride +
        MatrixUnaryDivision.totalTime ((n%outer)/stride) base +
        MatrixUnaryDivision.totalTime (((n%outer)/stride)%base) 1 + 1,
      run t (cfg (some (.inr (.inr MatrixStage4ColumnMachine.outerStart)))
        (saved,MatrixStage4ColumnMachine.initial) S) =
      cfg none (saved,MatrixStage4ColumnMachine.initial)
        (bank digitSlots S
          (MatrixStage4ColumnMachine.cfg none MatrixStage4ColumnMachine.initial
            [] (List.replicate outer true) (List.replicate stride true)
            (List.replicate base true) [true] []
            (List.replicate ((n%outer)%stride) true) []
            (List.replicate (n/outer) true) []
            (List.replicate (((n%outer)/stride)/base) true)
            (List.replicate ((((n%outer)/stride)%base)%1) true)
            (List.replicate ((((n%outer)/stride)%base)/1) true)).stk) := by
  let c := MatrixStage4ColumnMachine.cfg
    (some MatrixStage4ColumnMachine.outerStart)
    MatrixStage4ColumnMachine.initial
    (List.replicate n true) (List.replicate outer true)
    (List.replicate stride true) (List.replicate base true)
    [true] [] [] [] [] [] [] [] []
  obtain ⟨t,ht,hrun⟩ := MatrixStage4ColumnMachine.column_run
    n outer stride base 1
  simp only [List.replicate_one] at hrun
  have hhalt : (((advance MatrixStage4ColumnMachine.program)^[t]) c).l = none := by
    rw [← MatrixStage4ColumnMachine.run, hrun]
    rfl
  have hp (u : MatrixStage4ColumnMachine.Label) :
      program (.inr (.inr u)) = stmt digitSlots (Sum.inr ∘ Sum.inr)
        (fun v => (saved,v)) Prod.snd none
        (MatrixStage4ColumnMachine.program u) := rfl
  obtain ⟨t',ht',he⟩ := outputs digitSlots S (Sum.inr ∘ Sum.inr)
    (fun v => (saved,v)) Prod.snd (by intro v; rfl) none
    MatrixStage4ColumnMachine.program program hp c t hhalt
  refine ⟨t', le_trans ht' ht, ?_⟩
  have hbank : bank digitSlots S c.stk = S :=
    bank_eq_self digitSlots S c.stk (by intro k; exact (hinput k).symm)
  rw [show (((advance MatrixStage4ColumnMachine.program)^[t]) c) =
    MatrixStage4ColumnMachine.run t c from rfl, hrun] at he
  simpa only [run, cfg, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg,
    c, hbank] using he

def powerInput (base s : ℕ) (j : Fin (s+1)) :
    MatrixStage4SelectedPower.Config :=
  MatrixStage4SelectedPower.cutFrame (List.replicate base true)
    (MatrixUnaryCut.cfg (some .scan) (false,true)
      (List.replicate s true) (List.replicate j.val true) [] [])

def source (n outer base s : ℕ) (j : Fin (s+1)) : Config :=
  let c := powerInput base s j
  cfg (some start) (c.var,MatrixStage4ColumnMachine.initial)
    (powerBank c n outer base)

def digitBound (n outer base s : ℕ) (j : Fin (s+1)) : ℕ :=
  let stride := base^(s-j.val)
  let b := n%outer
  let k := b/stride
  let d := k%base
  (3*j.val+4+MatrixWeightedPower.powerBound base (s-j.val)+2) + 1 +
    (MatrixUnaryDivision.totalTime n outer+
      MatrixUnaryDivision.totalTime b stride+
      MatrixUnaryDivision.totalTime k base+
      MatrixUnaryDivision.totalTime d 1+1)

/-- Starting with a unary word ordinal and a unary selected coordinate, the
fixed program actually computes the variable stride and digit. The optional
outer modulus remains an explicitly supplied unary dimension. -/
theorem digit_output (n outer base s : ℕ) (j : Fin (s+1)) :
    let stride := base^(s-j.val)
    ∃ t ≤ digitBound n outer base s j,
      (run t (source n outer base s j)).l = none ∧
      (run t (source n outer base s j)).stk (.inr 14) =
        List.replicate (((n%outer)/stride)%base) true := by
  dsimp
  let stride := base^(s-j.val)
  let c := powerInput base s j
  obtain ⟨tp,htp,hl,hstride⟩ :=
    MatrixStage4SelectedPower.selected_power_run base s j
  have hhalt : (MatrixStage4SelectedPower.run tp c).l = none := by
    simpa only [c, powerInput] using hl
  have hstride' : (MatrixStage4SelectedPower.run tp c).stk 0 =
      List.replicate stride true := by
    simpa only [c, powerInput, stride] using hstride
  obtain ⟨t₁,ht₁,h₁⟩ := power_phase MatrixStage4SelectedPower.cutStart
    c.var c.stk n outer base tp hhalt
  have h₁' : run t₁ (source n outer base s j) =
      cfg (some (.inr (.inl ())))
        ((MatrixStage4SelectedPower.run tp c).var,
          MatrixStage4ColumnMachine.initial)
        (powerBank (MatrixStage4SelectedPower.run tp c) n outer base) := by
    simpa only [source, start, c] using h₁
  let S := powerBank (MatrixStage4SelectedPower.run tp c) n outer base
  have hinput : ∀ k : MatrixStage4ColumnMachine.Stack,
      S (digitSlots k) =
        (MatrixStage4ColumnMachine.cfg
          (some MatrixStage4ColumnMachine.outerStart)
          MatrixStage4ColumnMachine.initial
          (List.replicate n true) (List.replicate outer true)
          (List.replicate stride true) (List.replicate base true)
          [true] [] [] [] [] [] [] [] []).stk k := by
    intro k
    fin_cases k <;>
      simp [S, powerBank, extra, digitSlots,
        MatrixStage4ColumnMachine.cfg, hstride']
  obtain ⟨t₂,ht₂,h₂⟩ := digit_phase S n outer stride base hinput
  have h12 := run_add h₁' 1
  rw [bridge] at h12
  have h123 := run_add h12 t₂
  rw [h₂] at h123
  refine ⟨t₁+1+t₂, ?_, ?_, ?_⟩
  · dsimp [digitBound, stride] at htp ht₂ ⊢
    omega
  · rw [h123]
    rfl
  · rw [h123]
    simpa only [cfg, digitSlots, MatrixStage4ColumnMachine.cfg,
      Nat.div_one] using
      (bank_at digitSlots S
        (MatrixStage4ColumnMachine.cfg none MatrixStage4ColumnMachine.initial
          [] (List.replicate outer true) (List.replicate stride true)
          (List.replicate base true) [true] []
          (List.replicate ((n%outer)%stride) true) []
          (List.replicate (n/outer) true) []
          (List.replicate (((n%outer)/stride)/base) true)
          (List.replicate ((((n%outer)/stride)%base)%1) true)
          (List.replicate ((((n%outer)/stride)%base)/1) true)).stk 15)

def firstPosition {a s : ℕ} (j : Fin (qOne a)) :
    Fin ((firstLength a s - 1)+1) := by
  refine ⟨j.val, ?_⟩
  have hj := j.isLt
  unfold firstLength
  omega

@[simp] theorem firstPosition_val {a s : ℕ} (j : Fin (qOne a)) :
    (firstPosition (s := s) j).val = j.val := rfl

theorem first_word_digit_output {a s cy : ℕ}
    (γ : FirstColumns a s (Fin cy)) (j : Fin (qOne a)) :
    let code := firstWordCode a s cy γ
    let pos := firstPosition (s := s) j
    ∃ t ≤ digitBound code.val (cy^(firstLength a s)) cy
        (firstLength a s-1) pos,
      (run t (source code.val (cy^(firstLength a s)) cy
        (firstLength a s-1) pos)).l = none ∧
      (run t (source code.val (cy^(firstLength a s)) cy
        (firstLength a s-1) pos)).stk (.inr 14) =
        List.replicate (γ (firstCoordinate a s j)).val true := by
  dsimp
  let code := firstWordCode a s cy γ
  let pos := firstPosition (s := s) j
  obtain ⟨t,ht,hl,hout⟩ :=
    digit_output code.val (cy^(firstLength a s)) cy
      (firstLength a s-1) pos
  have hlength : firstLength a s - 1 + 1 = firstLength a s := by
    have hj := j.isLt
    unfold firstLength
    omega
  have hmod : code.val % cy^(firstLength a s) = code.val := by
    exact Nat.mod_eq_of_lt code.isLt
  have hdigit :
      code.val / cy^((firstLength a s-1)-pos.val) % cy =
        (γ (firstCoordinate a s j)).val := by
    have htuple := MatrixLabelArithmetic.tuple_digit code
      (firstCoordinate a s j)
    have hcoord : pos.val = (firstCoordinate a s j).val := by
      rfl
    rw [hcoord]
    simpa only [code, firstWordCode, Equiv.symm_apply_apply] using htuple.symm
  refine ⟨t,ht,hl,?_⟩
  simpa only [hmod, hlength, hdigit, pos, code] using hout

end EthInapproximability.CurrentPaper.MatrixStage4FirstDigitMachine
