import EthInapproximability.CurrentPaper.SamplerWriterSecondSequence

/-!
# First exact sampler call on the enlarged writer bank

The two extra stacks retain the second call's raw degree word and unary
length. This file begins the actual sequential composition. Its initial
bank is literal and computable, with neither family payload prefilled.
-/

namespace EthInapproximability.CurrentPaper.SamplerWriterPhysicalSequence

open Turing BitMachineEncoding
open SamplerWriterPayloadFrame

abbrev Stack := SamplerWriterSecondInit.Stack

def writerSlots : WriterStack ↪ Stack :=
  ⟨Sum.inl, by intro x y h; exact Sum.inl.inj h⟩

def firstSlots : SamplerMachineFieldTable.Stack ↪ Stack :=
  SamplerWriterPayloadFrame.firstSlots.trans writerSlots

def secondSlots : SamplerMachineFieldTable.Stack ↪ Stack :=
  SamplerWriterPayloadFrame.secondSlots.trans writerSlots

def reverseSlots : SamplerMachineBlockReverse.Stack ↪ Stack :=
  SamplerWriterPayloadFrame.reverseSlots.trans writerSlots

private theorem bank_sum {K : Type*} [DecidableEq K] (ι : K ↪ WriterStack)
    (F : WriterStack → List Bool) (E : Fin 2 → List Bool) (S : K → List Bool) :
    BitMachineStackEmbedding.bank (ι.trans writerSlots) (Sum.elim F E) S =
      Sum.elim (BitMachineStackEmbedding.bank ι F S) E := by
  funext j
  cases j with
  | inl j =>
      by_cases h : ∃ k, ι k = j
      · obtain ⟨k, rfl⟩ := h
        rw [← show (ι.trans writerSlots) k = .inl (ι k) from rfl,
          BitMachineStackEmbedding.bank_at]
        exact (BitMachineStackEmbedding.bank_at ι F S k).symm
      · have hh : ¬ ∃ k, (ι.trans writerSlots) k = Sum.inl j := by
          intro ⟨k, hk⟩
          exact h ⟨k, Sum.inl.inj hk⟩
        rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hh]
        exact (BitMachineStackEmbedding.bank_outside ι F S j h).symm
  | inr j =>
      have hh : ¬ ∃ k, (ι.trans writerSlots) k = Sum.inr j := by
        intro ⟨k, hk⟩
        cases hk
      rw [BitMachineStackEmbedding.bank_outside _ _ _ _ hh]
      rfl

def extraInput (secondDegree : List Bool) (secondLength : ℕ) : Fin 2 → List Bool :=
  ![secondDegree, List.replicate secondLength true]

def base (a d N₁ N₂ n : ℕ) (source secondDegree : List Bool)
    (secondLength : ℕ) : Stack → List Bool :=
  Sum.elim (blankFrame a d N₁ N₂ n source)
    (extraInput secondDegree secondLength)

def initial (a d N₁ N₂ n : ℕ) (source firstDegree secondDegree : List Bool)
    (firstLength secondLength : ℕ) : Stack → List Bool :=
  Sum.elim (firstRawInput a d N₁ N₂ n source firstDegree firstLength)
    (extraInput secondDegree secondLength)

theorem initial_eq_embedded (a d N₁ N₂ n : ℕ)
    (source firstDegree secondDegree : List Bool)
    (firstLength secondLength : ℕ) :
    initial a d N₁ N₂ n source firstDegree secondDegree firstLength secondLength =
      BitMachineStackEmbedding.bank firstSlots
        (base a d N₁ N₂ n source secondDegree secondLength)
        (SamplerMachineFieldTable.input firstDegree firstLength).stk := by
  unfold initial base firstSlots
  rw [bank_sum]
  congr 1
  exact firstRawInput_eq_bank a d N₁ N₂ n source firstDegree firstLength

def firstProgram (l : SamplerMachineFieldTable.Label) :
    TM2.Stmt (fun _ : Stack => Bool)
      SamplerMachineFieldTable.Label SamplerMachineFieldTable.Control :=
  BitMachineStackEmbedding.stmt firstSlots id id id none
    (SamplerMachineFieldTable.program l)

def afterFirst (a d N₁ N₂ n : ℕ) (source secondDegree : List Bool)
    (secondLength firstDegree firstLength : ℕ) : Stack → List Bool :=
  Sum.elim
    (Function.update
      (Function.update
        (Function.update (blankFrame a d N₁ N₂ n source)
          lengthCell (List.replicate firstLength true))
        modulusCell
        (SamplerMachine.encodeWord
          (ExecutableSmallBiasSampler.chosenWord firstDegree)))
      firstCell (SamplerSeedEnumeration.counterTraceTable firstDegree firstLength))
    (extraInput secondDegree secondLength)

theorem afterFirst_eq_embedded (a d N₁ N₂ n : ℕ)
    (source secondDegree : List Bool) (secondLength firstDegree firstLength : ℕ) :
    afterFirst a d N₁ N₂ n source secondDegree secondLength firstDegree firstLength =
      BitMachineStackEmbedding.bank firstSlots
        (base a d N₁ N₂ n source secondDegree secondLength)
        (completed firstDegree firstLength).stk := by
  unfold afterFirst base firstSlots
  rw [bank_sum]
  congr 1
  exact (first_completed_bank a d N₁ N₂ n firstDegree firstLength source).symm

theorem run_first (a d N₁ N₂ n : ℕ)
    (source firstDegree secondDegree : List Bool)
    (firstLength secondLength : ℕ) :
    ∃ t ≤ SamplerMachineFieldTable.timeBound firstDegree.length firstLength,
      ((advance firstProgram)^[t])
        (⟨(SamplerMachineFieldTable.input firstDegree firstLength).l,
          (SamplerMachineFieldTable.input firstDegree firstLength).var,
          initial a d N₁ N₂ n source firstDegree secondDegree
            firstLength secondLength⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SamplerMachineFieldTable.Label SamplerMachineFieldTable.Control) =
        ⟨none, .inr SamplerMachineTable.initial,
          afterFirst a d N₁ N₂ n source secondDegree secondLength
            firstDegree.length firstLength⟩ := by
  obtain ⟨u, hu, hr⟩ := SamplerMachineFieldTable.run_fieldTable firstDegree firstLength
  have hh : (((advance SamplerMachineFieldTable.program)^[u])
      (SamplerMachineFieldTable.input firstDegree firstLength)).l = none := by
    rw [← SamplerMachineFieldTable.run, hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs firstSlots
    (base a d N₁ N₂ n source secondDegree secondLength)
    id id id (by intro v; rfl) none SamplerMachineFieldTable.program
    firstProgram (by intro l; rfl)
    (SamplerMachineFieldTable.input firstDegree firstLength) u hh
  rw [← SamplerMachineFieldTable.run, hr] at he
  change ((advance firstProgram)^[t])
      (BitMachineStackEmbedding.cfg firstSlots
        (base a d N₁ N₂ n source secondDegree secondLength) id id none
        (SamplerMachineFieldTable.input firstDegree firstLength)) =
      BitMachineStackEmbedding.cfg firstSlots
        (base a d N₁ N₂ n source secondDegree secondLength) id id none
        (completed firstDegree.length firstLength) at he
  refine ⟨t, ht.trans hu, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg, BitMachineInline.cfg,
    initial_eq_embedded, afterFirst_eq_embedded] using he

theorem run_middle (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) :
    ∃ t ≤
      ((afterFirst a d N₁ N₂ n source secondDegree secondLength
        firstDegree firstLength) SamplerWriterSecondInit.degreeCell).length +
      ((afterFirst a d N₁ N₂ n source secondDegree secondLength
        firstDegree firstLength) SamplerWriterSecondInit.lengthCell).length + 4 +
      (2 * secondDegree.length + 2) +
      (2 * (List.replicate secondLength true).length + 2) +
      (2 * (List.replicate a true).length + 2) + 3,
      ((advance SamplerWriterSecondSequence.program)^[t])
        (⟨some (.inl (.inl (.inl 0))),
          (((((), none), none), none), none),
          afterFirst a d N₁ N₂ n source secondDegree secondLength
            firstDegree firstLength⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SamplerWriterSecondSequence.Label SamplerWriterSecondSequence.Control) =
        ⟨none, (((((), none), none), none), none),
          SamplerWriterSecondSequence.finalBank
            (afterFirst a d N₁ N₂ n source secondDegree secondLength
              firstDegree firstLength)
            secondDegree (List.replicate secondLength true)
            (List.replicate a true)⟩ := by
  let S := afterFirst a d N₁ N₂ n source secondDegree secondLength
    firstDegree firstLength
  have hd : S SamplerWriterSecondInit.nextDegree = secondDegree := by rfl
  have hl : S SamplerWriterSecondInit.nextLength =
      List.replicate secondLength true := by rfl
  have hw : S (.inl (.inl (.inl (.inl 24)))) = List.replicate a true := by rfl
  have h37 : S (.inl (.inl (.inl (.inl 37)))) = [] := by rfl
  have h38 : S (.inl (.inl (.inl (.inl 38)))) = [] := by rfl
  have h39 : S (.inl (.inl (.inl (.inl 39)))) = [] := by rfl
  have h32 : S (.inl reverseWidthCell) = [] := by rfl
  exact SamplerWriterSecondSequence.run_sequence S secondDegree
    (List.replicate secondLength true) (List.replicate a true)
    hd hl hw h37 h38 h39 h32

def afterMiddle (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) : Stack → List Bool :=
  SamplerWriterSecondSequence.finalBank
    (afterFirst a d N₁ N₂ n source secondDegree secondLength
      firstDegree firstLength)
    secondDegree (List.replicate secondLength true) (List.replicate a true)

theorem afterMiddle_secondInput (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) :
    BitMachineStackEmbedding.bank secondSlots
      (afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
        source secondDegree)
      (SamplerMachineFieldTable.input secondDegree secondLength).stk =
      afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
        source secondDegree := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> rfl

def secondProgram (l : SamplerMachineFieldTable.Label) :
    TM2.Stmt (fun _ : Stack => Bool)
      SamplerMachineFieldTable.Label SamplerMachineFieldTable.Control :=
  BitMachineStackEmbedding.stmt secondSlots id id id none
    (SamplerMachineFieldTable.program l)

private theorem inline_field_id (q : SamplerMachineFieldTable.Config) :
    BitMachineInline.cfg id id none q = q := by
  cases q with
  | mk l v S => cases l <;> rfl

def afterSecond (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) : Stack → List Bool :=
  Function.update
    (Function.update
      (afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
        source secondDegree)
      (.inl modulusCell)
      (SamplerMachine.encodeWord
        (ExecutableSmallBiasSampler.chosenWord secondDegree.length)))
    (.inl tableCell)
    (SamplerSeedEnumeration.counterTraceTable secondDegree.length secondLength)

theorem afterSecond_eq_embedded (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) :
    afterSecond a d N₁ N₂ n firstDegree firstLength secondLength
      source secondDegree =
      BitMachineStackEmbedding.bank secondSlots
        (afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
          source secondDegree)
        (completed secondDegree.length secondLength).stk := by
  have hlocal : (completed secondDegree.length secondLength).stk =
      Function.update
        (Function.update
          (SamplerMachineFieldTable.input secondDegree secondLength).stk
          SamplerMachineTable.modulus
          (SamplerMachine.encodeWord
            (ExecutableSmallBiasSampler.chosenWord secondDegree.length)))
        SamplerMachineTable.output
        (SamplerSeedEnumeration.counterTraceTable secondDegree.length secondLength) := by
    funext k
    fin_cases k <;> rfl
  rw [hlocal, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, afterMiddle_secondInput]
  rfl

theorem run_second (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) :
    ∃ t ≤ SamplerMachineFieldTable.timeBound secondDegree.length secondLength,
      ((advance secondProgram)^[t])
        (⟨(SamplerMachineFieldTable.input secondDegree secondLength).l,
          (SamplerMachineFieldTable.input secondDegree secondLength).var,
          afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
            source secondDegree⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SamplerMachineFieldTable.Label SamplerMachineFieldTable.Control) =
        ⟨none, .inr SamplerMachineTable.initial,
          afterSecond a d N₁ N₂ n firstDegree firstLength secondLength
            source secondDegree⟩ := by
  obtain ⟨u, hu, hr⟩ := SamplerMachineFieldTable.run_fieldTable
    secondDegree secondLength
  have hh : (((advance SamplerMachineFieldTable.program)^[u])
      (SamplerMachineFieldTable.input secondDegree secondLength)).l = none := by
    rw [← SamplerMachineFieldTable.run, hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs secondSlots
    (afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
      source secondDegree)
    id id id (by intro v; rfl) none SamplerMachineFieldTable.program
    secondProgram (by intro l; rfl)
    (SamplerMachineFieldTable.input secondDegree secondLength) u hh
  rw [← SamplerMachineFieldTable.run, hr] at he
  change ((advance secondProgram)^[t])
      (BitMachineStackEmbedding.cfg secondSlots
        (afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
          source secondDegree) id id none
        (SamplerMachineFieldTable.input secondDegree secondLength)) =
      BitMachineStackEmbedding.cfg secondSlots
        (afterMiddle a d N₁ N₂ n firstDegree firstLength secondLength
          source secondDegree) id id none
        (completed secondDegree.length secondLength) at he
  refine ⟨t, ht.trans hu, ?_⟩
  simp only [BitMachineStackEmbedding.cfg, inline_field_id,
    BitMachineStackEmbedding.stackCfg] at he
  rw [afterMiddle_secondInput] at he
  simpa only [afterSecond_eq_embedded] using he

def reverseProgram (l : SamplerMachineBlockReverse.Label) :
    TM2.Stmt (fun _ : Stack => Bool)
      SamplerMachineBlockReverse.Label SamplerMachineBlockReverse.Control :=
  BitMachineStackEmbedding.stmt reverseSlots id id id none
    (SamplerMachineBlockReverse.program l)

private theorem inline_reverse_id (q : SamplerMachineBlockReverse.Config) :
    BitMachineInline.cfg id id none q = q := by
  cases q with
  | mk l v S => cases l <;> rfl

def reverseInput (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) : SamplerMachineBlockReverse.Config :=
  SamplerMachineBlockReverse.cfg (some .check)
    SamplerMachineBlockReverse.initial
    (SamplerSeedEnumeration.counterTraceTable secondDegree.length secondLength)
    (List.replicate a true) [] [] [] []

theorem afterSecond_reverseInput (a d N₁ N₂ n firstDegree firstLength secondLength : ℕ)
    (source secondDegree : List Bool) :
    BitMachineStackEmbedding.bank reverseSlots
      (afterSecond a d N₁ N₂ n firstDegree firstLength secondLength
        source secondDegree)
      (reverseInput a d N₁ N₂ n firstDegree firstLength secondLength
        source secondDegree).stk =
      afterSecond a d N₁ N₂ n firstDegree firstLength secondLength
        source secondDegree := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  fin_cases k <;> rfl

def afterReverse (a t₁ t₂ d N₁ N₂ n firstDegree firstLength : ℕ)
    (source secondDegree : List Bool) (v : Fin n → Fin d → Bool) :
    Stack → List Bool :=
  Function.update
    (Function.update
      (afterSecond a d N₁ N₂ n firstDegree firstLength (d * a)
        source secondDegree)
      (.inl tableCell) [])
    (.inl secondCell)
    (MatrixMaterialization.storeBits
      (ExecutableSmallBiasSampler.exactFirstFamily a t₁ d)
      (ExecutableSmallBiasSampler.exactSecondFamily a t₂ d) v).second

theorem run_reverse (a t₁ t₂ d N₁ N₂ n firstDegree firstLength : ℕ)
    (ha : 0 < a) (source secondDegree : List Bool)
    (hdegree : secondDegree.length = SmallBiasSampler.fieldExponent (d * a)
      (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂))
    (v : Fin n → Fin d → Bool) :
    ∃ t ≤ (SamplerExactPayloadArrays.secondBlocks a t₂ d).length *
        SamplerMachineBlockReverse.blockStep a +
        ((SamplerExactPayloadArrays.secondBlocks a t₂ d).reverse.flatten).length + 2,
      ((advance reverseProgram)^[t])
        (⟨(reverseInput a d N₁ N₂ n firstDegree firstLength (d * a)
            source secondDegree).l,
          (reverseInput a d N₁ N₂ n firstDegree firstLength (d * a)
            source secondDegree).var,
          afterSecond a d N₁ N₂ n firstDegree firstLength (d * a)
            source secondDegree⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            SamplerMachineBlockReverse.Label SamplerMachineBlockReverse.Control) =
        ⟨none, SamplerMachineBlockReverse.initial,
          afterReverse a t₁ t₂ d N₁ N₂ n firstDegree firstLength
            source secondDegree v⟩ := by
  let c := reverseInput a d N₁ N₂ n firstDegree firstLength (d * a)
    source secondDegree
  have hc : c = SamplerMachineBlockReverse.cfg (some .check)
      SamplerMachineBlockReverse.initial
      (SamplerSeedEnumeration.counterTraceTable
        (SmallBiasSampler.fieldExponent (d * a)
          (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂)) (d * a))
      (List.replicate a true) [] [] [] [] := by
    simp [c, reverseInput, hdegree]
  have hr := SamplerExactPayloadArrays.run_secondPayload a t₁ t₂ d n ha v
  let steps := (SamplerExactPayloadArrays.secondBlocks a t₂ d).length *
    SamplerMachineBlockReverse.blockStep a +
    ((SamplerExactPayloadArrays.secondBlocks a t₂ d).reverse.flatten).length + 2
  have hh : (((advance SamplerMachineBlockReverse.program)^[steps]) c).l = none := by
    change (SamplerMachineBlockReverse.run steps c).l = none
    rw [hc, hr]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs reverseSlots
    (afterSecond a d N₁ N₂ n firstDegree firstLength (d * a)
      source secondDegree)
    id id id (by intro x; rfl) none SamplerMachineBlockReverse.program
    reverseProgram (by intro l; rfl) c steps hh
  have hf :
      (SamplerMachineBlockReverse.cfg none SamplerMachineBlockReverse.initial
        [] (List.replicate a true) [] [] []
        (MatrixMaterialization.storeBits
          (ExecutableSmallBiasSampler.exactFirstFamily a t₁ d)
          (ExecutableSmallBiasSampler.exactSecondFamily a t₂ d) v).second).stk =
      Function.update (Function.update c.stk 0 []) 5
        (MatrixMaterialization.storeBits
          (ExecutableSmallBiasSampler.exactFirstFamily a t₁ d)
          (ExecutableSmallBiasSampler.exactSecondFamily a t₂ d) v).second := by
    funext k
    fin_cases k <;> rfl
  have he' : ((advance reverseProgram)^[t]
      (BitMachineStackEmbedding.stackCfg reverseSlots
        (afterSecond a d N₁ N₂ n firstDegree firstLength (d * a)
          source secondDegree) c)) =
      BitMachineStackEmbedding.stackCfg reverseSlots
        (afterSecond a d N₁ N₂ n firstDegree firstLength (d * a)
          source secondDegree)
        (SamplerMachineBlockReverse.run steps c) := by
    simpa only [BitMachineStackEmbedding.cfg,
      inline_reverse_id,
      SamplerMachineBlockReverse.run] using he
  have hr' : SamplerMachineBlockReverse.run steps c =
      SamplerMachineBlockReverse.cfg none SamplerMachineBlockReverse.initial
        [] (List.replicate a true) [] [] []
        (MatrixMaterialization.storeBits
          (ExecutableSmallBiasSampler.exactFirstFamily a t₁ d)
          (ExecutableSmallBiasSampler.exactSecondFamily a t₂ d) v).second := by
    rw [hc]
    exact hr
  rw [hr'] at he'
  refine ⟨t, ht, ?_⟩
  simp only [BitMachineStackEmbedding.stackCfg] at he'
  rw [afterSecond_reverseInput] at he'
  rw [hf, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update,
    afterSecond_reverseInput] at he'
  simpa only [reverse_input_slot, reverse_output_slot, afterReverse] using he'

end EthInapproximability.CurrentPaper.SamplerWriterPhysicalSequence
