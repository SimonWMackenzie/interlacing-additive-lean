import CurrentAdditive.CodeDPairProductTargetV2
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineRawSequence

namespace CurrentAdditive.RawRatPairAssembler

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open CodeDCodec CodeDPairProductTargetV2

abbrev Stack (N : Nat) := Fin 7 ⊕ Fin N
abbrev Bank (N : Nat) := Stack N → List Bool

def initialBank {N : Nat} (x y : List Bool) (foreign : Fin N → List Bool) :
    Bank N :=
  Sum.elim ![x,y,[],[],[],[],[]] foreign

def firstBank {N : Nat} (x y : List Bool) (foreign : Fin N → List Bool) :
    Bank N :=
  Sum.elim ![x,y,x,[],[],[],[]] foreign

def secondBank {N : Nat} (x y : List Bool) (foreign : Fin N → List Bool) :
    Bank N :=
  Sum.elim ![x,y,x,y,[],[],[]] foreign

def finalBank {N : Nat} (x y : List Bool) (foreign : Fin N → List Bool)
    (output : List Bool) : Bank N :=
  Sum.elim ![x,y,[],[],[],[],output] foreign

def copyXSlots (N : Nat) : Fin 3 ↪ Stack N where
  toFun i := .inl (![0,2,4] i)
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def copyYSlots (N : Nat) : Fin 3 ↪ Stack N where
  toFun i := .inl (![1,3,4] i)
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def serSlots (N : Nat) : BitMachineBankSerialize.Stack 2 ↪ Stack N where
  toFun
    | .inl i => .inl (![2,3] i)
    | .inr i => .inl (![4,5,6] i)
  inj' := by
    intro a b h
    cases a with
    | inl a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp_all
        | inr b => fin_cases a <;> fin_cases b <;> simp_all
    | inr a =>
        cases b with
        | inl b => fin_cases a <;> fin_cases b <;> simp_all
        | inr b => fin_cases a <;> fin_cases b <;> simp_all

def copyXProgram (N : Nat) : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Stack N => Bool) BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stmt (copyXSlots N) id id id none
    (BitMachineCopy.program l)

def copyYProgram (N : Nat) : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Stack N => Bool) BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stmt (copyYSlots N) id id id none
    (BitMachineCopy.program l)

def serProgram (N : Nat) : BitMachineBankSerialize.Label 2 →
    TM2.Stmt (fun _ : Stack N => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool) :=
  fun l => BitMachineStackEmbedding.stmt (serSlots N) id id id none
    (BitMachineBankSerialize.program 2 l)

def copiesProgram (N : Nat) :=
  BitMachineRawSequence.program (copyXProgram N) (copyYProgram N)
    BitMachineCopy.Label.scan none none

def program (N : Nat) :=
  BitMachineRawSequence.program (copiesProgram N) (serProgram N)
    (BitMachineBankSerialize.Label.emit 0) (none,none) none

theorem copyX_start {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    BitMachineStackEmbedding.cfg (copyXSlots N)
      (initialBank x y foreign) id id none
      (BitMachineCopy.cfg (some .scan) none x [] []) =
    ⟨some .scan, none, initialBank x y foreign⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;>
    simp [copyXSlots, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, initialBank]

theorem copyX_end {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    BitMachineStackEmbedding.cfg (copyXSlots N)
      (initialBank x y foreign) id id none
      (BitMachineCopy.cfg none none x x []) =
    ⟨none, none, firstBank x y foreign⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  funext j
  by_cases h : ∃ k : Fin 3, copyXSlots N k = j
  · obtain ⟨k,rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases k <;>
      simp [copyXSlots, BitMachineCopy.cfg,
        BitMachineCopy.stackContents, firstBank]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]
    cases j with
    | inl j =>
        have h0 : j ≠ 0 := by
          intro he; subst j; exact h ⟨0,rfl⟩
        have h2 : j ≠ 2 := by
          intro he; subst j; exact h ⟨1,rfl⟩
        have h4 : j ≠ 4 := by
          intro he; subst j; exact h ⟨2,rfl⟩
        fin_cases j <;> simp_all [initialBank, firstBank]
    | inr j => rfl

theorem copyX_run {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    ∃ t ≤ 2*x.length+2,
      ((advance (copyXProgram N))^[t])
        (⟨some BitMachineCopy.Label.scan, none,
          initialBank x y foreign⟩ :
          TM2.Cfg (fun _ : Stack N => Bool) _ _) =
        ⟨none, none, firstBank x y foreign⟩ := by
  have hc := BitMachineCopy.run_correct none x []
  simp only [List.append_nil] at hc
  have hh : ((advance BitMachineCopy.program)^[2*x.length+2]
      (BitMachineCopy.cfg (some .scan) none x [] [])).l = none := by
    rw [← BitMachineCopy.run, hc]
    rfl
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs
    (copyXSlots N) (initialBank x y foreign) id id id
    (by intro v; rfl) none BitMachineCopy.program
    (copyXProgram N) (by intro l; rfl)
    (BitMachineCopy.cfg (some .scan) none x [] [])
    (2*x.length+2) hh
  refine ⟨t,ht,?_⟩
  rw [copyX_start, ← BitMachineCopy.run, hc, copyX_end] at hr
  exact hr

theorem copyY_start {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    BitMachineStackEmbedding.cfg (copyYSlots N)
      (firstBank x y foreign) id id none
      (BitMachineCopy.cfg (some .scan) none y [] []) =
    ⟨some .scan, none, firstBank x y foreign⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;>
    simp [copyYSlots, BitMachineCopy.cfg,
      BitMachineCopy.stackContents, firstBank]

theorem copyY_end {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    BitMachineStackEmbedding.cfg (copyYSlots N)
      (firstBank x y foreign) id id none
      (BitMachineCopy.cfg none none y y []) =
    ⟨none, none, secondBank x y foreign⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  funext j
  by_cases h : ∃ k : Fin 3, copyYSlots N k = j
  · obtain ⟨k,rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    fin_cases k <;>
      simp [copyYSlots, BitMachineCopy.cfg,
        BitMachineCopy.stackContents, secondBank]
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]
    cases j with
    | inl j =>
        have h1 : j ≠ 1 := by
          intro he; subst j; exact h ⟨0,rfl⟩
        have h3 : j ≠ 3 := by
          intro he; subst j; exact h ⟨1,rfl⟩
        have h4 : j ≠ 4 := by
          intro he; subst j; exact h ⟨2,rfl⟩
        fin_cases j <;> simp_all [firstBank, secondBank]
    | inr j => rfl

theorem copyY_run {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    ∃ t ≤ 2*y.length+2,
      ((advance (copyYProgram N))^[t])
        (⟨some BitMachineCopy.Label.scan, none,
          firstBank x y foreign⟩ :
          TM2.Cfg (fun _ : Stack N => Bool) _ _) =
        ⟨none, none, secondBank x y foreign⟩ := by
  have hc := BitMachineCopy.run_correct none y []
  simp only [List.append_nil] at hc
  have hh : ((advance BitMachineCopy.program)^[2*y.length+2]
      (BitMachineCopy.cfg (some .scan) none y [] [])).l = none := by
    rw [← BitMachineCopy.run, hc]
    rfl
  obtain ⟨t,ht,hr⟩ := BitMachineStackEmbedding.outputs
    (copyYSlots N) (firstBank x y foreign) id id id
    (by intro v; rfl) none BitMachineCopy.program
    (copyYProgram N) (by intro l; rfl)
    (BitMachineCopy.cfg (some .scan) none y [] [])
    (2*y.length+2) hh
  refine ⟨t,ht,?_⟩
  rw [copyY_start, ← BitMachineCopy.run, hc, copyY_end] at hr
  exact hr

def pairWord (x y : List Bool) : List Bool :=
  BitMachineBankSerialize.encode [x,y]

theorem pairWord_exact (x y : RawRat) :
    pairWord (encodeRawRat x) (encodeRawRat y) = pairBytes x y := by
  unfold pairWord pairBytes
  rw [BitMachineBankCodec.encode_eq_list]
  rfl

def selected (x y : List Bool) : BitMachineBankSerialize.Bank 2 :=
  ![x,y]

theorem ser_start {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    BitMachineStackEmbedding.cfg (serSlots N)
      (secondBank x y foreign) id id none
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (selected x y) [] [] []) =
    ⟨some (BitMachineBankSerialize.Label.emit 0), none,
      secondBank x y foreign⟩ := by
  unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
    BitMachineInline.cfg
  congr 1
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  cases k with
  | inl k =>
      fin_cases k <;>
        simp [serSlots, selected, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, secondBank]
  | inr k =>
      fin_cases k <;>
        simp [serSlots, selected, BitMachineBankSerialize.cfg,
          BitMachineBankSerialize.contents, secondBank]

theorem ser_run {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    ∃ t ≤ 2*(pairWord x y).length+2,
      ∃ S' : BitMachineBankSerialize.Bank 2,
      ((advance (serProgram N))^[t])
        (⟨some (BitMachineBankSerialize.Label.emit 0), none,
          secondBank x y foreign⟩ :
          TM2.Cfg (fun _ : Stack N => Bool) _ _) =
        BitMachineStackEmbedding.cfg (serSlots N)
          (secondBank x y foreign) id id none
          (BitMachineBankSerialize.cfg none none S' [] []
            (pairWord x y)) := by
  obtain ⟨t,S',ht,hr⟩ :=
    BitMachineBankSerialize.serialize (selected x y) [] []
  have hp : BitMachineBankSerialize.encode (List.ofFn (selected x y)) =
      pairWord x y := by rfl
  rw [hp] at ht hr
  simp only [List.append_nil] at hr
  have hh : ((advance (BitMachineBankSerialize.program 2))^[t]
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (selected x y) [] [] [])).l = none := by
    rw [← BitMachineBankSerialize.run, hr]
    rfl
  obtain ⟨u,hu,he⟩ := BitMachineStackEmbedding.outputs
    (serSlots N) (secondBank x y foreign) id id id
    (by intro v; rfl) none (BitMachineBankSerialize.program 2)
    (serProgram N) (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (selected x y) [] [] []) t hh
  refine ⟨u,hu.trans ht,S',?_⟩
  rw [ser_start, ← BitMachineBankSerialize.run, hr] at he
  exact he

theorem copies_run {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    ∃ t ≤ 2*x.length+2*y.length+5,
      ((advance (copiesProgram N))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            BitMachineCopy.Label.scan), (none,none),
          initialBank x y foreign⟩ :
          TM2.Cfg (fun _ : Stack N => Bool) _ _) =
        ⟨none, (none,none), secondBank x y foreign⟩ := by
  obtain ⟨a,ha,hx⟩ := copyX_run x y foreign
  obtain ⟨b,hb,hy⟩ := copyY_run x y foreign
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (copyXProgram N) (copyYProgram N)
    BitMachineCopy.Label.scan BitMachineCopy.Label.scan
    none none none none
    (initialBank x y foreign) (firstBank x y foreign)
    (secondBank x y foreign) a b hx hy
  exact ⟨t,by omega,by simpa only [copiesProgram] using hr⟩

theorem pairWord_length (x y : List Bool) :
    (pairWord x y).length = 2*(x.length+y.length)+2 := by
  simp [pairWord, BitMachineBankSerialize.encode,
    EncodedCommunication.field_length]
  omega

noncomputable def completedBank {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) : Bank N :=
  BitMachineStackEmbedding.bank (serSlots N) (secondBank x y foreign)
    (BitMachineBankSerialize.cfg none none S' [] [] (pairWord x y)).stk

theorem assembly_run {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    ∃ t ≤ 6*(x.length+y.length+2),
      ∃ S' : BitMachineBankSerialize.Bank 2,
      ((advance (program N))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),none), initialBank x y foreign⟩ :
          TM2.Cfg (fun _ : Stack N => Bool) _ _) =
        ⟨none, ((none,none),none), completedBank x y foreign S'⟩ := by
  obtain ⟨a,ha,hcopy⟩ := copies_run x y foreign
  obtain ⟨b,hb,S',hser⟩ := ser_run x y foreign
  have hser' : ((advance (serProgram N))^[b])
      (⟨some (BitMachineBankSerialize.Label.emit 0), none,
        secondBank x y foreign⟩ :
        TM2.Cfg (fun _ : Stack N => Bool) _ _) =
      ⟨none, none, completedBank x y foreign S'⟩ := by
    simpa [completedBank, BitMachineStackEmbedding.cfg,
      BitMachineInline.cfg] using hser
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    (copiesProgram N) (serProgram N)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (BitMachineBankSerialize.Label.emit 0)
    (none,none) (none,none) none none
    (initialBank x y foreign) (secondBank x y foreign)
    (completedBank x y foreign S') a b hcopy hser'
  have hp := pairWord_length x y
  refine ⟨t,by omega,S',?_⟩
  simpa only [program] using hr

theorem completed_sourceX {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    completedBank x y foreign S' (.inl 0) = x := by
  have h : ¬ ∃ k : BitMachineBankSerialize.Stack 2,
      serSlots N k = (.inl 0 : Stack N) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k => fin_cases k <;> simp [serSlots] at hk
    | inr k => fin_cases k <;> simp [serSlots] at hk
  rw [completedBank, BitMachineStackEmbedding.bank_outside _ _ _ _ h]
  rfl

theorem completed_sourceY {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    completedBank x y foreign S' (.inl 1) = y := by
  have h : ¬ ∃ k : BitMachineBankSerialize.Stack 2,
      serSlots N k = (.inl 1 : Stack N) := by
    rintro ⟨k,hk⟩
    cases k with
    | inl k => fin_cases k <;> simp [serSlots] at hk
    | inr k => fin_cases k <;> simp [serSlots] at hk
  rw [completedBank, BitMachineStackEmbedding.bank_outside _ _ _ _ h]
  rfl

theorem completed_foreign {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) (j : Fin N) :
    completedBank x y foreign S' (.inr j) = foreign j := by
  have h : ¬ ∃ k : BitMachineBankSerialize.Stack 2,
      serSlots N k = (.inr j : Stack N) := by
    rintro ⟨k,hk⟩
    cases k <;> cases hk
  rw [completedBank, BitMachineStackEmbedding.bank_outside _ _ _ _ h]
  rfl

theorem completed_output {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool)
    (S' : BitMachineBankSerialize.Bank 2) :
    completedBank x y foreign S' (.inl 6) = pairWord x y := by
  have hk : serSlots N (.inr 2) = (.inl 6 : Stack N) := rfl
  rw [← hk, completedBank, BitMachineStackEmbedding.bank_at]
  rfl

theorem assembly_outputs {N : Nat} (x y : List Bool)
    (foreign : Fin N → List Bool) :
    ∃ t ≤ 6*(x.length+y.length+2),
      let c := ((advance (program N))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),none), initialBank x y foreign⟩ :
          TM2.Cfg (fun _ : Stack N => Bool) _ _)
      c.l = none ∧ c.stk (.inl 6) = pairWord x y ∧
      c.stk (.inl 0) = x ∧ c.stk (.inl 1) = y ∧
      (∀ j : Fin N, c.stk (.inr j) = foreign j) := by
  obtain ⟨t,ht,S',hr⟩ := assembly_run x y foreign
  refine ⟨t,ht,?_⟩
  dsimp only
  rw [hr]
  exact ⟨rfl, completed_output x y foreign S',
    completed_sourceX x y foreign S',
    completed_sourceY x y foreign S',
    completed_foreign x y foreign S'⟩

theorem assembly_pairBytes {N : Nat} (x y : RawRat)
    (foreign : Fin N → List Bool) :
    ∃ t ≤ 6*((encodeRawRat x).length+(encodeRawRat y).length+2),
      let c := ((advance (program N))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none,none),none),
          initialBank (encodeRawRat x) (encodeRawRat y) foreign⟩ :
          TM2.Cfg (fun _ : Stack N => Bool) _ _)
      c.l = none ∧ c.stk (.inl 6) = pairBytes x y ∧
      c.stk (.inl 0) = encodeRawRat x ∧
      c.stk (.inl 1) = encodeRawRat y ∧
      (∀ j : Fin N, c.stk (.inr j) = foreign j) := by
  simpa only [pairWord_exact] using
    (assembly_outputs (encodeRawRat x) (encodeRawRat y) foreign)

#print axioms assembly_outputs
#print axioms assembly_pairBytes

end CurrentAdditive.RawRatPairAssembler
