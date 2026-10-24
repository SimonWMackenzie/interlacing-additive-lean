import CurrentAdditive.CodeDPairProductTargetV2
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-!
Literal nested rational packet flattening. The input is a two-field packet,
each field itself a three-field RawRat record. Two local parsers install the
six words in disjoint staging stacks; the twelve-field serializer emits the
flat packet. All other staging fields are empty.
-/

namespace EthInapproximability.CurrentPaper.RationalProductNestedFlat

open Turing TM2.Stmt BitMachineEncoding
open BitMachineBankCodec

abbrev Stack := Fin 14 ⊕ Fin 3
abbrev Bank := Fin 14 → List Bool

inductive Admin where
  | afterOuter | afterX | afterY
  deriving DecidableEq, Fintype

abbrev Label := BitMachineBankCodec.ParserLabel 2 ⊕
  (BitMachineBankCodec.ParserLabel 3 ⊕
    (BitMachineBankCodec.ParserLabel 3 ⊕
      (BitMachineBankSerialize.Label 12 ⊕ Admin)))
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def outerSlots : BitMachineBankCodec.Stack 2 ↪ Stack where
  toFun
    | .inl i => .inl (if i = 0 then 12 else 13)
    | .inr j => .inr j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp at h ⊢
        | inr b => simp at h
    | inr a =>
        cases b with
        | inl b => simp at h
        | inr b => simpa using h

def xSlots : BitMachineBankCodec.Stack 3 ↪ Stack where
  toFun
    | .inl i => .inl ⟨i.val, by omega⟩
    | .inr j => if j = 0 then .inl 12 else .inr j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            exact congrArg Sum.inl (Fin.ext (by
              have hv := congrArg Fin.val (Sum.inl.inj h)
              simpa using hv))
        | inr b =>
            fin_cases b
            · have hv := congrArg Fin.val (Sum.inl.inj h)
              simp at hv
              omega
            · simp at h
            · simp at h
    | inr a =>
        cases b with
        | inl b =>
            fin_cases a
            · have hv := congrArg Fin.val (Sum.inl.inj h)
              simp at hv
              omega
            · simp at h
            · simp at h
        | inr b => fin_cases a <;> fin_cases b <;> simp at h ⊢

def ySlots : BitMachineBankCodec.Stack 3 ↪ Stack where
  toFun
    | .inl i => .inl ⟨i.val+6, by omega⟩
    | .inr j => if j = 0 then .inl 13 else .inr j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            exact congrArg Sum.inl (Fin.ext (by
              have hv := congrArg Fin.val (Sum.inl.inj h)
              simp at hv
              omega))
        | inr b =>
            fin_cases b
            · have hv := congrArg Fin.val (Sum.inl.inj h)
              simp at hv
              omega
            · simp at h
            · simp at h
    | inr a =>
        cases b with
        | inl b =>
            fin_cases a
            · have hv := congrArg Fin.val (Sum.inl.inj h)
              simp at hv
              omega
            · simp at h
            · simp at h
        | inr b => fin_cases a <;> fin_cases b <;> simp at h ⊢

def serSlots : BitMachineBankSerialize.Stack 12 ↪ Stack where
  toFun
    | .inl i => .inl ⟨i.val, by omega⟩
    | .inr j => .inr j
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b =>
            exact congrArg Sum.inl (Fin.ext (by
              have hv := congrArg Fin.val (Sum.inl.inj h)
              simpa using hv))
        | inr b => simp at h
    | inr a =>
        cases b with
        | inl b => simp at h
        | inr b => simpa using h

def outerLabel : BitMachineBankCodec.ParserLabel 2 → Label := Sum.inl
def xLabel : BitMachineBankCodec.ParserLabel 3 → Label := fun l => .inr (.inl l)
def yLabel : BitMachineBankCodec.ParserLabel 3 → Label := fun l => .inr (.inr (.inl l))
def serLabel : BitMachineBankSerialize.Label 12 → Label :=
  fun l => .inr (.inr (.inr (.inl l)))
def adminLabel : Admin → Label := fun l => .inr (.inr (.inr (.inr l)))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt outerSlots outerLabel id id
      (some (adminLabel .afterOuter)) (BitMachineBankCodec.parser 2 l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt xSlots xLabel id id
      (some (adminLabel .afterX)) (BitMachineBankCodec.parser 3 l)
  | .inr (.inr (.inl l)) => BitMachineStackEmbedding.stmt ySlots yLabel id id
      (some (adminLabel .afterY)) (BitMachineBankCodec.parser 3 l)
  | .inr (.inr (.inr (.inl l))) =>
      BitMachineStackEmbedding.stmt serSlots serLabel id id none
        (BitMachineBankSerialize.program 12 l)
  | .inr (.inr (.inr (.inr .afterOuter))) =>
      branch (fun v => v.getD false)
        (load (fun _ => none) (goto (fun _ => xLabel (.scan 0)))) halt
  | .inr (.inr (.inr (.inr .afterX))) =>
      branch (fun v => v.getD false)
        (load (fun _ => none) (goto (fun _ => yLabel (.scan 0)))) halt
  | .inr (.inr (.inr (.inr .afterY))) =>
      branch (fun v => v.getD false)
        (load (fun _ => none) (goto (fun _ => serLabel (.emit 0)))) halt

def cfg (l : Option Label) (v : Control) (S : Bank)
    (source saved output : List Bool) : Config :=
  ⟨l,v,BitMachineBankCodec.contents S source saved output⟩

def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (m n : Nat) (c : Config) :
    run (m+n) c = run n (run m c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance program) n m c

theorem parser_embed_success (K : Nat)
    (ι : BitMachineBankCodec.Stack K ↪ Stack)
    (labels : BitMachineBankCodec.ParserLabel K → Label)
    (next : Label)
    (hprogram : ∀ l, program (labels l) =
      BitMachineStackEmbedding.stmt ι labels id id (some next)
        (BitMachineBankCodec.parser K l))
    (foreign : Stack → List Bool) (input : List Bool)
    (S : BitMachineBankCodec.Bank K)
    (hd : BitMachineBankCodec.decode K input = some S) :
    ∃ t ≤ (2*K+1)*(input.length+1),
      run t
        (BitMachineStackEmbedding.cfg ι foreign labels id (some next)
          (BitMachineBankCodec.parserCfg (some (.scan 0)) none
            (fun _ => []) input [] [])) =
      BitMachineStackEmbedding.cfg ι foreign labels id (some next)
        (BitMachineBankCodec.parserCfg none (some true) S [] [] []) := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct K input []
  rw [hd] at hp
  change BitMachineBankCodec.parserRun t
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) =
    BitMachineBankCodec.parserCfg none (some true) S [] [] [] at hp
  have hh := congrArg (fun c => c.l) hp
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs ι foreign
    labels id id (by intro v; rfl) (some next)
    (BitMachineBankCodec.parser K) program hprogram
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t
    (by simpa only [BitMachineBankCodec.parserRun] using hh)
  refine ⟨u,hu.trans ht,?_⟩
  unfold BitMachineBankCodec.parserRun at hp
  rw [hp] at hr
  exact hr

theorem parser_embed_failure (K : Nat)
    (ι : BitMachineBankCodec.Stack K ↪ Stack)
    (labels : BitMachineBankCodec.ParserLabel K → Label)
    (next : Label)
    (hprogram : ∀ l, program (labels l) =
      BitMachineStackEmbedding.stmt ι labels id id (some next)
        (BitMachineBankCodec.parser K l))
    (foreign : Stack → List Bool) (input : List Bool)
    (hd : BitMachineBankCodec.decode K input = none) :
    ∃ t ≤ (2*K+1)*(input.length+1),
      let c := run t
        (BitMachineStackEmbedding.cfg ι foreign labels id (some next)
          (BitMachineBankCodec.parserCfg (some (.scan 0)) none
            (fun _ => []) input [] []))
      c.l = some next ∧ c.var = some false ∧ c.stk (ι (.inr 2)) = [] := by
  obtain ⟨t,ht,hp⟩ := BitMachineBankCodec.parser_correct K input []
  rw [hd] at hp
  let c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack K => Bool)
      (BitMachineBankCodec.ParserLabel K) Control :=
    BitMachineBankCodec.parserRun t
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none
        (fun _ => []) input [] [])
  change c.l = none ∧ c.var = some false ∧ c.stk (.inr 2) = [] at hp
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs ι foreign
    labels id id (by intro v; rfl) (some next)
    (BitMachineBankCodec.parser K) program hprogram
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) input [] []) t hp.1
  refine ⟨u,hu.trans ht,?_⟩
  change _ ∧ _ ∧ _
  change run u _ = BitMachineStackEmbedding.cfg ι foreign labels id
    (some next) c at hr
  rw [hr]
  constructor
  · simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hp.1]
  constructor
  · simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hp.2.1]
  · simp [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg,
      BitMachineStackEmbedding.bank_at,
      BitMachineInline.cfg, hp.2.2]

noncomputable def outerState (S : BitMachineBankCodec.Bank 2) : Config :=
  BitMachineStackEmbedding.cfg outerSlots (fun _ => []) outerLabel id
    (some (adminLabel .afterOuter))
    (BitMachineBankCodec.parserCfg none (some true) S [] [] [])

theorem outer_state_at (S : BitMachineBankCodec.Bank 2)
    (k : BitMachineBankCodec.Stack 2) :
    (outerState S).stk (outerSlots k) =
      (BitMachineBankCodec.parserCfg none (some true) S [] [] []).stk k := by
  simp [outerState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_at, BitMachineInline.cfg]

theorem outer_state_empty (S : BitMachineBankCodec.Bank 2)
    (j : Fin 14) (hj12 : j ≠ 12) (hj13 : j ≠ 13) :
    (outerState S).stk (.inl j) = [] := by
  have hout : ¬ ∃ k : BitMachineBankCodec.Stack 2,
      outerSlots k = (.inl j : Stack) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k =>
        fin_cases k
        · exact hj12 (Sum.inl.inj hk).symm
        · exact hj13 (Sum.inl.inj hk).symm
    | inr k => cases hk
  simp [outerState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_outside _ _ _ _ hout]

theorem outer_state_shape (S : BitMachineBankCodec.Bank 2) :
    (outerState S).stk (.inl 12) = S 0 ∧
    (outerState S).stk (.inl 13) = S 1 ∧
    (outerState S).stk (.inr 1) = [] ∧
    (outerState S).stk (.inr 2) = [] := by
  have h0 := outer_state_at S (.inl 0)
  have h1 := outer_state_at S (.inl 1)
  have hs := outer_state_at S (.inr 1)
  have ho := outer_state_at S (.inr 2)
  simpa [outerSlots, BitMachineBankCodec.parserCfg,
    BitMachineBankCodec.contents] using And.intro h0 (And.intro h1 (And.intro hs ho))

private theorem outer_program_eq (l : BitMachineBankCodec.ParserLabel 2) :
    program (outerLabel l) =
      BitMachineStackEmbedding.stmt outerSlots outerLabel id id
        (some (adminLabel .afterOuter)) (BitMachineBankCodec.parser 2 l) := rfl

theorem parse_outer (input : List Bool) (S : BitMachineBankCodec.Bank 2)
    (hd : BitMachineBankCodec.decode 2 input = some S) :
    ∃ t ≤ 5*(input.length+1),
      run t
        (BitMachineStackEmbedding.cfg outerSlots (fun _ => []) outerLabel id
          (some (adminLabel .afterOuter))
          (BitMachineBankCodec.parserCfg (some (.scan 0)) none
            (fun _ => []) input [] [])) = outerState S := by
  exact parser_embed_success 2 outerSlots outerLabel
    (adminLabel .afterOuter) outer_program_eq (fun _ => []) input S hd

noncomputable def xStart (S : BitMachineBankCodec.Bank 2) : Config :=
  BitMachineStackEmbedding.cfg xSlots (outerState S).stk xLabel id
    (some (adminLabel .afterX))
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) (S 0) [] [])

theorem outer_admin (S : BitMachineBankCodec.Bank 2) :
    advance program (outerState S) =
      ⟨some (xLabel (.scan 0)), none, (outerState S).stk⟩ := by
  change advance program
    (⟨some (adminLabel .afterOuter), some true, (outerState S).stk⟩ : Config) = _
  simp [advance, TM2.step, TM2.stepAux, program, adminLabel, xLabel]

theorem outer_to_x_start (S : BitMachineBankCodec.Bank 2) :
    advance program (outerState S) = xStart S := by
  rw [outer_admin]
  unfold xStart BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply (BitMachineStackEmbedding.bank_eq_self xSlots
    (outerState S).stk
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) (S 0) [] []).stk) ?_ |>.symm
  intro k
  cases k with
  | inl k =>
      fin_cases k
      · simpa [xSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents] using
          (outer_state_empty S 0 (by decide) (by decide)).symm
      · simpa [xSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents] using
          (outer_state_empty S 1 (by decide) (by decide)).symm
      · simpa [xSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents] using
          (outer_state_empty S 2 (by decide) (by decide)).symm
  | inr k =>
      rcases outer_state_shape S with ⟨h0,h1,hs,ho⟩
      fin_cases k <;>
        simp [xSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents, h0, hs, ho]

private theorem x_program_eq (l : BitMachineBankCodec.ParserLabel 3) :
    program (xLabel l) =
      BitMachineStackEmbedding.stmt xSlots xLabel id id
        (some (adminLabel .afterX)) (BitMachineBankCodec.parser 3 l) := rfl

noncomputable def xState (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) : Config :=
  BitMachineStackEmbedding.cfg xSlots (outerState S).stk xLabel id
    (some (adminLabel .afterX))
    (BitMachineBankCodec.parserCfg none (some true) X [] [] [])

theorem parse_x (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 (S 0) = some X) :
    ∃ t ≤ 7*((S 0).length+1), run t (xStart S) = xState S X := by
  exact parser_embed_success 3 xSlots xLabel (adminLabel .afterX)
    x_program_eq (outerState S).stk (S 0) X hd

theorem x_state_at (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3)
    (k : BitMachineBankCodec.Stack 3) :
    (xState S X).stk (xSlots k) =
      (BitMachineBankCodec.parserCfg none (some true) X [] [] []).stk k := by
  simp [xState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_at, BitMachineInline.cfg]

theorem x_state_outside (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) (j : Fin 14)
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj2 : j ≠ 2)
    (hj12 : j ≠ 12) :
    (xState S X).stk (.inl j) = (outerState S).stk (.inl j) := by
  have hout : ¬ ∃ k : BitMachineBankCodec.Stack 3,
      xSlots k = (.inl j : Stack) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k =>
        fin_cases k
        · exact hj0 (Sum.inl.inj hk).symm
        · exact hj1 (Sum.inl.inj hk).symm
        · exact hj2 (Sum.inl.inj hk).symm
    | inr k =>
        fin_cases k
        · exact hj12 (Sum.inl.inj hk).symm
        · cases hk
        · cases hk
  simp [xState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_outside _ _ _ _ hout]

theorem x_state_y_source (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) :
    (xState S X).stk (.inl 13) = S 1 := by
  rw [x_state_outside S X 13 (by decide) (by decide)
    (by decide) (by decide)]
  exact (outer_state_shape S).2.1

noncomputable def yStart (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) : Config :=
  BitMachineStackEmbedding.cfg ySlots (xState S X).stk yLabel id
    (some (adminLabel .afterY))
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) (S 1) [] [])

theorem x_admin (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) :
    advance program (xState S X) =
      ⟨some (yLabel (.scan 0)), none, (xState S X).stk⟩ := by
  change advance program
    (⟨some (adminLabel .afterX), some true, (xState S X).stk⟩ : Config) = _
  simp [advance, TM2.step, TM2.stepAux, program, adminLabel, yLabel]

theorem x_to_y_start (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) :
    advance program (xState S X) = yStart S X := by
  rw [x_admin]
  unfold yStart BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply (BitMachineStackEmbedding.bank_eq_self ySlots
    (xState S X).stk
    (BitMachineBankCodec.parserCfg (some (.scan 0)) none
      (fun _ => []) (S 1) [] []).stk) ?_ |>.symm
  intro k
  cases k with
  | inl k =>
      fin_cases k
      · simp [ySlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents,
          x_state_outside S X 6 (by decide) (by decide)
            (by decide) (by decide),
          outer_state_empty S 6 (by decide) (by decide)]
      · simp [ySlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents,
          x_state_outside S X 7 (by decide) (by decide)
            (by decide) (by decide),
          outer_state_empty S 7 (by decide) (by decide)]
      · simp [ySlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents,
          x_state_outside S X 8 (by decide) (by decide)
            (by decide) (by decide),
          outer_state_empty S 8 (by decide) (by decide)]
  | inr k =>
      fin_cases k
      · simpa [ySlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents] using (x_state_y_source S X).symm
      · simpa [ySlots, xSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents] using
          (x_state_at S X (.inr 1)).symm
      · simpa [ySlots, xSlots, BitMachineBankCodec.parserCfg,
          BitMachineBankCodec.contents] using
          (x_state_at S X (.inr 2)).symm

private theorem y_program_eq (l : BitMachineBankCodec.ParserLabel 3) :
    program (yLabel l) =
      BitMachineStackEmbedding.stmt ySlots yLabel id id
        (some (adminLabel .afterY)) (BitMachineBankCodec.parser 3 l) := rfl

noncomputable def yState (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) : Config :=
  BitMachineStackEmbedding.cfg ySlots (xState S X).stk yLabel id
    (some (adminLabel .afterY))
    (BitMachineBankCodec.parserCfg none (some true) Y [] [] [])

theorem parse_y (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3)
    (hd : BitMachineBankCodec.decode 3 (S 1) = some Y) :
    ∃ t ≤ 7*((S 1).length+1), run t (yStart S X) = yState S X Y := by
  exact parser_embed_success 3 ySlots yLabel (adminLabel .afterY)
    y_program_eq (xState S X).stk (S 1) Y hd

theorem x_state_word (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) (j : Fin 14) :
    (xState S X).stk (.inl j) =
      if j = 0 then X 0 else if j = 1 then X 1 else
      if j = 2 then X 2 else if j = 13 then S 1 else [] := by
  by_cases h0 : j = 0
  · subst j
    simpa [xSlots, BitMachineBankCodec.parserCfg,
      BitMachineBankCodec.contents] using x_state_at S X (.inl 0)
  by_cases h1 : j = 1
  · subst j
    simpa [xSlots, BitMachineBankCodec.parserCfg,
      BitMachineBankCodec.contents] using x_state_at S X (.inl 1)
  by_cases h2 : j = 2
  · subst j
    simpa [xSlots, BitMachineBankCodec.parserCfg,
      BitMachineBankCodec.contents] using x_state_at S X (.inl 2)
  by_cases h13 : j = 13
  · subst j
    simp [h0,h1,h2, x_state_y_source]
  by_cases h12 : j = 12
  · subst j
    simpa [h0,h1,h2,h13, xSlots,
      BitMachineBankCodec.parserCfg,
      BitMachineBankCodec.contents] using x_state_at S X (.inr 0)
  rw [x_state_outside S X j h0 h1 h2 h12]
  rw [outer_state_empty S j h12 h13]
  simp [h0,h1,h2,h13]

theorem y_state_at (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3)
    (k : BitMachineBankCodec.Stack 3) :
    (yState S X Y).stk (ySlots k) =
      (BitMachineBankCodec.parserCfg none (some true) Y [] [] []).stk k := by
  simp [yState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_at, BitMachineInline.cfg]

theorem y_state_outside (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) (j : Fin 14)
    (hj6 : j ≠ 6) (hj7 : j ≠ 7) (hj8 : j ≠ 8)
    (hj13 : j ≠ 13) :
    (yState S X Y).stk (.inl j) = (xState S X).stk (.inl j) := by
  have hout : ¬ ∃ k : BitMachineBankCodec.Stack 3,
      ySlots k = (.inl j : Stack) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k =>
        fin_cases k
        · exact hj6 (Sum.inl.inj hk).symm
        · exact hj7 (Sum.inl.inj hk).symm
        · exact hj8 (Sum.inl.inj hk).symm
    | inr k =>
        fin_cases k
        · exact hj13 (Sum.inl.inj hk).symm
        · cases hk
        · cases hk
  simp [yState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_outside _ _ _ _ hout]

def stagingBank (X Y : BitMachineBankCodec.Bank 3) :
    BitMachineBankCodec.Bank 12 :=
  fun i =>
    if i = 0 then X 0 else if i = 1 then X 1 else
    if i = 2 then X 2 else if i = 6 then Y 0 else
    if i = 7 then Y 1 else if i = 8 then Y 2 else []

theorem y_state_stage (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) (i : Fin 12) :
    (yState S X Y).stk (.inl (⟨i.val, by omega⟩ : Fin 14)) =
      stagingBank X Y i := by
  by_cases h6 : i.val = 6
  · have hi : i = 6 := Fin.ext h6
    subst i
    simpa [stagingBank, ySlots, BitMachineBankCodec.parserCfg,
      BitMachineBankCodec.contents] using y_state_at S X Y (.inl 0)
  by_cases h7 : i.val = 7
  · have hi : i = 7 := Fin.ext h7
    subst i
    simpa [stagingBank, ySlots, BitMachineBankCodec.parserCfg,
      BitMachineBankCodec.contents] using y_state_at S X Y (.inl 1)
  by_cases h8 : i.val = 8
  · have hi : i = 8 := Fin.ext h8
    subst i
    simpa [stagingBank, ySlots, BitMachineBankCodec.parserCfg,
      BitMachineBankCodec.contents] using y_state_at S X Y (.inl 2)
  have hj6 : (⟨i.val, by omega⟩ : Fin 14) ≠ 6 := by exact fun h => h6 (by simpa using congrArg Fin.val h)
  have hj7 : (⟨i.val, by omega⟩ : Fin 14) ≠ 7 := by exact fun h => h7 (by simpa using congrArg Fin.val h)
  have hj8 : (⟨i.val, by omega⟩ : Fin 14) ≠ 8 := by exact fun h => h8 (by simpa using congrArg Fin.val h)
  have hj13 : (⟨i.val, by omega⟩ : Fin 14) ≠ 13 := by intro h; have := congrArg Fin.val h; simp at this; omega
  rw [y_state_outside S X Y _ hj6 hj7 hj8 hj13, x_state_word]
  fin_cases i <;> simp_all [stagingBank]

theorem x_state_aux_zero (S : BitMachineBankCodec.Bank 2)
    (X : BitMachineBankCodec.Bank 3) :
    (xState S X).stk (.inr 0) = [] := by
  have hout : ¬ ∃ k : BitMachineBankCodec.Stack 3,
      xSlots k = (.inr 0 : Stack) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k => cases hk
    | inr k => fin_cases k <;> simp [xSlots] at hk
  have houter := outer_state_at S (.inr 0)
  simp [xState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_outside _ _ _ _ hout,
    outerSlots, BitMachineBankCodec.parserCfg,
    BitMachineBankCodec.contents] at houter ⊢
  exact houter

theorem y_state_aux_zero (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) :
    (yState S X Y).stk (.inr 0) = [] := by
  have hout : ¬ ∃ k : BitMachineBankCodec.Stack 3,
      ySlots k = (.inr 0 : Stack) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k => cases hk
    | inr k => fin_cases k <;> simp [ySlots] at hk
  simp [yState, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg,
    BitMachineStackEmbedding.bank_outside _ _ _ _ hout,
    x_state_aux_zero]

theorem y_state_aux (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) :
    (yState S X Y).stk (.inr 0) = [] ∧
    (yState S X Y).stk (.inr 1) = [] ∧
    (yState S X Y).stk (.inr 2) = [] := by
  have h1 := y_state_at S X Y (.inr 1)
  have h2 := y_state_at S X Y (.inr 2)
  simpa [ySlots, BitMachineBankCodec.parserCfg,
    BitMachineBankCodec.contents] using
    And.intro (y_state_aux_zero S X Y) (And.intro h1 h2)

noncomputable def serStart (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) : Config :=
  BitMachineStackEmbedding.cfg serSlots (yState S X Y).stk serLabel id none
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (stagingBank X Y) [] [] [])

theorem y_admin (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) :
    advance program (yState S X Y) =
      ⟨some (serLabel (.emit 0)), none, (yState S X Y).stk⟩ := by
  change advance program
    (⟨some (adminLabel .afterY), some true, (yState S X Y).stk⟩ : Config) = _
  simp [advance, TM2.step, TM2.stepAux, program, adminLabel, serLabel]

theorem y_to_ser_start (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) :
    advance program (yState S X Y) = serStart S X Y := by
  rw [y_admin]
  unfold serStart BitMachineStackEmbedding.cfg
    BitMachineStackEmbedding.stackCfg BitMachineInline.cfg
  congr 1
  apply (BitMachineStackEmbedding.bank_eq_self serSlots
    (yState S X Y).stk
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (stagingBank X Y) [] [] []).stk) ?_ |>.symm
  intro k
  cases k with
  | inl k =>
      simpa [serSlots, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents] using (y_state_stage S X Y k).symm
  | inr k =>
      rcases y_state_aux S X Y with ⟨h0,h1,h2⟩
      fin_cases k <;> simp [serSlots, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents, h0,h1,h2]

private theorem ser_program_eq (l : BitMachineBankSerialize.Label 12) :
    program (serLabel l) =
      BitMachineStackEmbedding.stmt serSlots serLabel id id none
        (BitMachineBankSerialize.program 12 l) := rfl

theorem serialize_stage (S : BitMachineBankCodec.Bank 2)
    (X Y : BitMachineBankCodec.Bank 3) :
    ∃ t ≤ 2*(BitMachineBankSerialize.encode
        (List.ofFn (stagingBank X Y))).length+2,
      let c := run t (serStart S X Y)
      c.l = none ∧ c.stk (.inr 2) =
        BitMachineBankSerialize.encode (List.ofFn (stagingBank X Y)) := by
  obtain ⟨t,T,ht,hs⟩ :=
    BitMachineBankSerialize.serialize (stagingBank X Y) [] []
  have hh := congrArg (fun c => c.l) hs
  change _ = none at hh
  obtain ⟨u,hu,hr⟩ := BitMachineStackEmbedding.outputs serSlots
    (yState S X Y).stk serLabel id id (by intro v; rfl) none
    (BitMachineBankSerialize.program 12) program ser_program_eq
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (stagingBank X Y) [] [] []) t
    (by simpa only [BitMachineBankSerialize.run] using hh)
  refine ⟨u,hu.trans ht,?_⟩
  change _ ∧ _
  unfold BitMachineBankSerialize.run at hs
  rw [hs] at hr
  change run u (serStart S X Y) = _ at hr
  rw [hr]
  constructor
  · rfl
  · simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
    rw [← show serSlots (.inr 2) = (.inr 2 : Stack) by rfl,
      BitMachineStackEmbedding.bank_at]
    simp [BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents]

def flatBank (x y : CurrentAdditive.CodeDCodec.RawRat) :
    BitMachineBankCodec.Bank 12 :=
  fun i =>
    if i = 0 then (if x.negative then [true] else []) else
    if i = 1 then x.numerator else
    if i = 2 then x.denominator else
    if i = 6 then (if y.negative then [true] else []) else
    if i = 7 then y.numerator else
    if i = 8 then y.denominator else []

def flatBytes (x y : CurrentAdditive.CodeDCodec.RawRat) : List Bool :=
  BitMachineBankCodec.encode (flatBank x y)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inr 0 : Stack) (.inr 2) (outerLabel (.scan 0)) none program

end EthInapproximability.CurrentPaper.RationalProductNestedFlat
