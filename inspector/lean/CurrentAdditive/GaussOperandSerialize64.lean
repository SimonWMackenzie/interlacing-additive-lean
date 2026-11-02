import CurrentAdditive.GaussFourOperands64
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Embedded Bank12 arithmetic request serializer on the Fin64 four-operand
workspace. Slots 24..28 carry the five live fields; 0..6 are empty fields.
The literal encoded request is written to bank 23. -/

namespace CurrentAdditive.GaussOperandSerialize64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def fieldSlot : Fin 12 → Stack :=
  ![28, 24, 25, 26, 27, 0, 1, 2, 3, 4, 5, 6]

def extraSlot : Fin 3 → Stack := ![21, 22, 23]

def wordBank (flag : Bool) (current column row pivot : List Bool) :
    Fin 12 → List Bool :=
  fun i => if i = 0 then [flag] else if i = 1 then current else
    if i = 2 then column else if i = 3 then row else
    if i = 4 then pivot else []

def packet (flag : Bool) (current column row pivot : List Bool) :
    List Bool :=
  BitMachineBankSerialize.encode (List.ofFn
    (wordBank flag current column row pivot))

def slot : (Fin 12 ⊕ Fin 3) ↪ Stack where
  toFun
    | .inl i => fieldSlot i
    | .inr i => extraSlot i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        fin_cases a <;> fin_cases b <;>
          simp_all [fieldSlot]
      | inr b =>
        fin_cases a <;> fin_cases b <;>
          simp_all [fieldSlot, extraSlot]
    | inr a =>
      cases b with
      | inl b =>
        fin_cases a <;> fin_cases b <;>
          simp_all [fieldSlot, extraSlot]
      | inr b =>
        fin_cases a <;> fin_cases b <;>
          simp_all [extraSlot]

abbrev Label := BitMachineBankSerialize.Label 12
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def program (l : Label) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt slot id id id none
    (BitMachineBankSerialize.program 12 l)

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

theorem physical_packet (flag : Bool)
    (current column row pivot : List Bool)
    (S : Stack → List Bool)
    (hwords : ∀ i : Fin 12,
      S (fieldSlot i) = wordBank flag current column row pivot i)
    (hsource : S 21 = []) (htemp : S 22 = [])
    (houtput : S 23 = []) :
    ∃ t ≤ 2 * (packet flag current column row pivot).length + 2,
      (run t ⟨some (.emit 0), none, S⟩).l = none ∧
      (run t ⟨some (.emit 0), none, S⟩).stk 23 =
        packet flag current column row pivot ∧
      (run t ⟨some (.emit 0), none, S⟩).stk 8 = S 8 := by
  let B := wordBank flag current column row pivot
  let cfgLocal := BitMachineBankSerialize.cfg
    (some (.emit 0)) none B [] [] []
  have hready : ∀ k : Fin 12 ⊕ Fin 3,
      cfgLocal.stk k = S (slot k) := by
    intro k
    cases k with
    | inl i =>
      change B i = S (fieldSlot i)
      exact (hwords i).symm
    | inr i =>
      fin_cases i <;> simp [cfgLocal, BitMachineBankSerialize.cfg,
        BitMachineBankSerialize.contents, slot, extraSlot,
        hsource, htemp, houtput]
  have hbank : BitMachineStackEmbedding.bank slot S cfgLocal.stk = S :=
    BitMachineStackEmbedding.bank_eq_self slot S cfgLocal.stk hready
  obtain ⟨u, U, hu, hlocal⟩ :=
    BitMachineBankSerialize.serialize B ([] : List Bool) ([] : List Bool)
  have hlocalHalt :
      ((advance (BitMachineBankSerialize.program 12))^[u]) cfgLocal =
        BitMachineBankSerialize.cfg none none U [] []
          (packet flag current column row pivot) := by
    simpa [BitMachineBankSerialize.run, cfgLocal, packet, B] using hlocal
  obtain ⟨t, ht, hEmbed⟩ := BitMachineStackEmbedding.outputs
    slot S id id id (by intro x; rfl) none
    (BitMachineBankSerialize.program 12) program
    (by intro l; rfl) cfgLocal u (by rw [hlocalHalt]; rfl)
  have hInit : BitMachineStackEmbedding.cfg slot S id id none cfgLocal =
      (⟨some (.emit 0), none, S⟩ : Config) := by
    change (⟨some (.emit 0), none,
      BitMachineStackEmbedding.bank slot S cfgLocal.stk⟩ : Config) = _
    rw [hbank]
  have hFinal :
      run t ⟨some (.emit 0), none, S⟩ =
        BitMachineStackEmbedding.cfg slot S id id none
          (BitMachineBankSerialize.cfg none none U [] []
            (packet flag current column row pivot)) := by
    rw [← hInit]
    simpa [run, program, hlocalHalt] using hEmbed
  refine ⟨t, by simpa [packet, B] using ht.trans hu,
    ?_, ?_, ?_⟩
  · rw [hFinal]
    rfl
  · rw [hFinal]
    change (BitMachineStackEmbedding.bank slot S
      (BitMachineBankSerialize.cfg none none U [] []
        (packet flag current column row pivot)).stk) (slot (.inr 2)) = _
    rw [BitMachineStackEmbedding.bank_at]
    rfl
  · rw [hFinal]
    have h8 : ¬ ∃ k : Fin 12 ⊕ Fin 3, slot k = (8 : Stack) := by
      intro ⟨k, hk⟩
      cases k with
      | inl i => fin_cases i <;> simp_all [slot, fieldSlot]
      | inr i => fin_cases i <;> simp_all [slot, extraSlot]
    exact BitMachineStackEmbedding.bank_outside slot S _ 8 h8

#print axioms physical_packet

theorem prepared_words (flag : Bool)
    (current column row pivot : List Bool)
    (S : Stack → List Bool)
    (hflag : S 28 = [flag])
    (hcurrent : S 24 = current) (hcolumn : S 25 = column)
    (hrow : S 26 = row) (hpivot : S 27 = pivot)
    (hempty : ∀ j : Stack, j.val < 7 → S j = []) :
    ∀ i : Fin 12,
      S (fieldSlot i) = wordBank flag current column row pivot i := by
  intro i
  have h0 : S 0 = [] := hempty 0 (by decide)
  have h1 : S 1 = [] := hempty 1 (by decide)
  have h2 : S 2 = [] := hempty 2 (by decide)
  have h3 : S 3 = [] := hempty 3 (by decide)
  have h4 : S 4 = [] := hempty 4 (by decide)
  have h5 : S 5 = [] := hempty 5 (by decide)
  have h6 : S 6 = [] := hempty 6 (by decide)
  fin_cases i <;> simp [fieldSlot, wordBank, hflag,
    hcurrent, hcolumn, hrow, hpivot, h0, h1, h2, h3, h4, h5, h6]

#print axioms prepared_words

end CurrentAdditive.GaussOperandSerialize64
