import EthInapproximability.CurrentPaper.SamplerExactPayloadArrays
import EthInapproximability.CurrentPaper.MatrixScalarWriterFrame

/-!
# Physical sampler stack slots in the exact-NP writer bank

The first sampler stores C1 at writer cell 28. The second uses spare cells
33--50 (leaving cell 32 free for unary `a`) and leaves C1 untouched; its
table output at cell 49 is then read by
the fixed block-reversal controller, whose output is writer cell 29. Source
cell 30 is foreign to all sampler phases and is preserved.
-/

namespace EthInapproximability.CurrentPaper.SamplerWriterPayloadFrame

open Turing BitMachineEncoding

abbrev WriterStack := MatrixScalarWriterFrame.WriterStack

def tableFin : SamplerMachineFieldTable.Stack ≃ Fin 18 :=
  SamplerMachineFieldTable.sumUnitFin
    (SamplerMachineFieldTable.sumUnitFin
      ((Equiv.sumCongr SamplerMachineFieldTable.rowFin (Equiv.refl (Fin 2))).trans
        finSumFinEquiv))

def spareCell (j : Fin 18) : WriterStack :=
  .inl (.inl (.inl ⟨32 + j.val, by omega⟩))

def firstSlot (k : SamplerMachineFieldTable.Stack) : WriterStack :=
  if k = SamplerMachineTable.output then .inl (.inl (.inl 28))
  else spareCell (tableFin k)

def secondSlot (k : SamplerMachineFieldTable.Stack) : WriterStack :=
  if tableFin k = 0 then .inl (.inl (.inl 50))
  else spareCell (tableFin k)

def firstSlots : SamplerMachineFieldTable.Stack ↪ WriterStack :=
  ⟨firstSlot, by
    intro x y h
    by_cases hx : x = SamplerMachineTable.output
    · subst x
      by_cases hy : y = SamplerMachineTable.output
      · subst y; rfl
      · simp only [firstSlot, if_pos, if_neg hy, spareCell] at h
        have hv := congrArg Fin.val (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h)))
        simp at hv
        omega
    · by_cases hy : y = SamplerMachineTable.output
      · subst y
        simp only [firstSlot, if_pos, if_neg hx, spareCell] at h
        have hv := congrArg Fin.val (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h)))
        simp at hv
        omega
      · simp only [firstSlot, hx, hy, spareCell] at h
        have he : tableFin x = tableFin y := by
          apply Fin.ext
          exact Nat.add_left_cancel (Fin.mk.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj h))))
        exact tableFin.injective he⟩

def secondSlots : SamplerMachineFieldTable.Stack ↪ WriterStack :=
  ⟨secondSlot, by decide⟩

def reverseSlot : SamplerMachineBlockReverse.Stack → WriterStack
  | 0 => secondSlot SamplerMachineTable.output
  | 1 => .inl (.inl (.inl 32))
  | 2 => .inl (.inl (.inl 33))
  | 3 => .inl (.inl (.inl 34))
  | 4 => .inl (.inl (.inl 35))
  | _ => .inl (.inl (.inl 29))

def reverseSlots : SamplerMachineBlockReverse.Stack ↪ WriterStack :=
  ⟨reverseSlot, by decide⟩

def firstCell : WriterStack := .inl (.inl (.inl 28))
def secondCell : WriterStack := .inl (.inl (.inl 29))
def sourceCell : WriterStack := .inl (.inl (.inl 30))
def modulusCell : WriterStack := .inl (.inl (.inl 36))
def lengthCell : WriterStack := .inl (.inl (.inl 47))
def tableCell : WriterStack := .inl (.inl (.inl 49))
def reverseWidthCell : WriterStack := .inl (.inl (.inl 32))

theorem first_output_slot : firstSlots SamplerMachineTable.output = firstCell := by decide
theorem second_output_slot : secondSlots SamplerMachineTable.output = tableCell := by decide
theorem first_modulus_slot : firstSlots SamplerMachineTable.modulus = modulusCell := by decide
theorem second_modulus_slot : secondSlots SamplerMachineTable.modulus = modulusCell := by decide
theorem first_length_slot : firstSlots SamplerMachineTable.lengthSource = lengthCell := by decide
theorem second_length_slot : secondSlots SamplerMachineTable.lengthSource = lengthCell := by decide
theorem reverse_input_slot : reverseSlots 0 = tableCell := by decide
theorem reverse_width_slot : reverseSlots 1 = reverseWidthCell := by decide
theorem reverse_output_slot : reverseSlots 5 = secondCell := by decide

theorem first_avoids_source : ∀ k, firstSlots k ≠ sourceCell := by decide
theorem second_avoids_source : ∀ k, secondSlots k ≠ sourceCell := by decide
theorem reverse_avoids_source : ∀ k, reverseSlots k ≠ sourceCell := by decide
theorem second_avoids_first : ∀ k, secondSlots k ≠ firstCell := by decide
theorem second_avoids_width : ∀ k, secondSlots k ≠ reverseWidthCell := by decide
theorem reverse_avoids_first : ∀ k, reverseSlots k ≠ firstCell := by decide

def blankData (source : List Bool) : MatrixMaterialization.ExactBitData :=
  ⟨[], [], source⟩

def blankFrame (a d N₁ N₂ n : ℕ) (source : List Bool) : WriterStack → List Bool :=
  MatrixScalarWriterFrame.rawInput a d N₁ N₂ n (blankData source)

def firstRawInput (a d N₁ N₂ n : ℕ) (source bits : List Bool) (L : ℕ) :
    WriterStack → List Bool :=
  Function.update
    (Function.update (blankFrame a d N₁ N₂ n source)
      lengthCell (List.replicate L true)) modulusCell bits

private theorem blank_firstSlots (a d N₁ N₂ n : ℕ) (source : List Bool)
    (k : SamplerMachineFieldTable.Stack) :
    blankFrame a d N₁ N₂ n source (firstSlots k) = [] := by
  fin_cases k <;> rfl

private theorem field_input_stk (bits : List Bool) (L : ℕ) :
    (SamplerMachineFieldTable.input bits L).stk =
      Function.update
        (Function.update (fun _ : SamplerMachineFieldTable.Stack => [])
          SamplerMachineTable.lengthSource (List.replicate L true))
        SamplerMachineTable.modulus bits := by
  funext k
  fin_cases k <;> rfl

theorem firstRawInput_eq_bank (a d N₁ N₂ n : ℕ) (source bits : List Bool) (L : ℕ) :
    firstRawInput a d N₁ N₂ n source bits L =
      BitMachineStackEmbedding.bank firstSlots (blankFrame a d N₁ N₂ n source)
        (SamplerMachineFieldTable.input bits L).stk := by
  rw [field_input_stk, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update]
  have he : BitMachineStackEmbedding.bank firstSlots
      (blankFrame a d N₁ N₂ n source)
      (fun _ : SamplerMachineFieldTable.Stack => []) =
      blankFrame a d N₁ N₂ n source := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    exact (blank_firstSlots a d N₁ N₂ n source k).symm
  rw [he, first_length_slot, first_modulus_slot]
  rfl

def firstStart (a d N₁ N₂ n : ℕ) (source bits : List Bool) (L : ℕ) :
    TM2.Cfg (fun _ : WriterStack => Bool)
      SamplerMachineFieldTable.Label SamplerMachineFieldTable.Control :=
  ⟨(SamplerMachineFieldTable.input bits L).l,
    (SamplerMachineFieldTable.input bits L).var,
    firstRawInput a d N₁ N₂ n source bits L⟩

theorem firstStart_eq_embedded (a d N₁ N₂ n : ℕ)
    (source bits : List Bool) (L : ℕ) :
    firstStart a d N₁ N₂ n source bits L =
      BitMachineStackEmbedding.stackCfg firstSlots
        (blankFrame a d N₁ N₂ n source)
        (SamplerMachineFieldTable.input bits L) := by
  simp only [firstStart, BitMachineStackEmbedding.stackCfg]
  congr 1
  exact firstRawInput_eq_bank a d N₁ N₂ n source bits L

def completed (degree L : ℕ) : SamplerMachineFieldTable.Config :=
  ⟨none, .inr SamplerMachineTable.initial,
    (SamplerMachineTable.cfg none SamplerMachineTable.initial
      (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord degree)) []
      (List.replicate L true) [] []
      (SamplerSeedEnumeration.counterTraceTable degree L)).stk⟩

private theorem completed_stk (degree L : ℕ) :
    (completed degree L).stk =
      Function.update
        (Function.update
          (Function.update (fun _ : SamplerMachineFieldTable.Stack => [])
            SamplerMachineTable.lengthSource (List.replicate L true))
          SamplerMachineTable.modulus
          (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord degree)))
        SamplerMachineTable.output
        (SamplerSeedEnumeration.counterTraceTable degree L) := by
  funext k
  fin_cases k <;> rfl

theorem first_completed_bank (a d N₁ N₂ n degree L : ℕ)
    (source : List Bool) :
    BitMachineStackEmbedding.bank firstSlots (blankFrame a d N₁ N₂ n source)
      (completed degree L).stk =
      Function.update
        (Function.update
          (Function.update (blankFrame a d N₁ N₂ n source)
            lengthCell (List.replicate L true))
          modulusCell
          (SamplerMachine.encodeWord (ExecutableSmallBiasSampler.chosenWord degree)))
        firstCell (SamplerSeedEnumeration.counterTraceTable degree L) := by
  rw [completed_stk]
  simp only [BitMachineStackEmbedding.bank_update, first_length_slot,
    first_modulus_slot, first_output_slot]
  have he : BitMachineStackEmbedding.bank firstSlots
      (blankFrame a d N₁ N₂ n source)
      (fun _ : SamplerMachineFieldTable.Stack => []) =
      blankFrame a d N₁ N₂ n source := by
    apply BitMachineStackEmbedding.bank_eq_self
    intro k
    exact (blank_firstSlots a d N₁ N₂ n source k).symm
  rw [he]

def fieldProgram (ι : SamplerMachineFieldTable.Stack ↪ WriterStack)
    (l : SamplerMachineFieldTable.Label) :
    TM2.Stmt (fun _ : WriterStack => Bool)
      SamplerMachineFieldTable.Label SamplerMachineFieldTable.Control :=
  BitMachineStackEmbedding.stmt ι id id id none (SamplerMachineFieldTable.program l)

theorem field_run (ι : SamplerMachineFieldTable.Stack ↪ WriterStack)
    (foreign : WriterStack → List Bool) (bits : List Bool) (L : ℕ) :
    ∃ t ≤ SamplerMachineFieldTable.timeBound bits.length L,
      ((advance (fieldProgram ι))^[t])
        (BitMachineStackEmbedding.stackCfg ι foreign
          (SamplerMachineFieldTable.input bits L)) =
        BitMachineStackEmbedding.stackCfg ι foreign
          ⟨none, .inr SamplerMachineTable.initial,
            (SamplerMachineTable.cfg none SamplerMachineTable.initial
              (SamplerMachine.encodeWord
                (ExecutableSmallBiasSampler.chosenWord bits.length)) []
              (List.replicate L true) [] []
              (SamplerSeedEnumeration.counterTraceTable bits.length L)).stk⟩ := by
  obtain ⟨u, hu, hr⟩ := SamplerMachineFieldTable.run_fieldTable bits L
  have hh : (((advance SamplerMachineFieldTable.program)^[u])
      (SamplerMachineFieldTable.input bits L)).l = none := by
    rw [← SamplerMachineFieldTable.run, hr]
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs ι foreign
    id id id (by intro v; rfl) none
    SamplerMachineFieldTable.program (fieldProgram ι)
    (by intro l; rfl) (SamplerMachineFieldTable.input bits L) u hh
  rw [← SamplerMachineFieldTable.run, hr] at he
  exact ⟨t, ht.trans hu, by simpa only [BitMachineStackEmbedding.cfg,
    BitMachineInline.cfg] using he⟩

theorem first_run_payload (a t₁ t₂ d n : ℕ)
    (v : Fin n → Fin d → Bool) (foreign : WriterStack → List Bool) :
    ∃ u ≤ SamplerMachineFieldTable.timeBound
        (SmallBiasSampler.fieldExponent (ExactConstruction.prefixLength a + 3)
          (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁))
        (ExactConstruction.prefixLength a + 3),
      (((advance (fieldProgram firstSlots))^[u])
        (BitMachineStackEmbedding.stackCfg firstSlots foreign
          (SamplerMachineFieldTable.input
            (List.replicate
              (SmallBiasSampler.fieldExponent (ExactConstruction.prefixLength a + 3)
                (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁)) false)
            (ExactConstruction.prefixLength a + 3)))).stk firstCell =
        (MatrixMaterialization.storeBits
          (ExecutableSmallBiasSampler.exactFirstFamily a t₁ d)
          (ExecutableSmallBiasSampler.exactSecondFamily a t₂ d) v).first := by
  obtain ⟨u, hu, hr⟩ := field_run firstSlots foreign
    (List.replicate
      (SmallBiasSampler.fieldExponent (ExactConstruction.prefixLength a + 3)
        (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁)) false)
    (ExactConstruction.prefixLength a + 3)
  refine ⟨u, by simpa using hu, ?_⟩
  rw [hr, ← first_output_slot]
  change BitMachineStackEmbedding.bank firstSlots foreign _
    (firstSlots SamplerMachineTable.output) = _
  rw [BitMachineStackEmbedding.bank_at]
  change SamplerSeedEnumeration.counterTraceTable
    (List.replicate
      (SmallBiasSampler.fieldExponent (ExactConstruction.prefixLength a + 3)
        (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁)) false).length
    (ExactConstruction.prefixLength a + 3) = _
  simpa only [List.length_replicate] using
    SamplerExactPayloadArrays.firstTrace_stored a t₁ t₂ d n v

theorem second_table_run (a t d : ℕ) (foreign : WriterStack → List Bool) :
    ∃ u ≤ SamplerMachineFieldTable.timeBound
        (SmallBiasSampler.fieldExponent (d * a)
          (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t)) (d * a),
      (((advance (fieldProgram secondSlots))^[u])
        (BitMachineStackEmbedding.stackCfg secondSlots foreign
          (SamplerMachineFieldTable.input
            (List.replicate
              (SmallBiasSampler.fieldExponent (d * a)
                (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t)) false)
            (d * a)))).stk tableCell =
        SamplerSeedEnumeration.counterTraceTable
          (SmallBiasSampler.fieldExponent (d * a)
            (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t)) (d * a) := by
  obtain ⟨u, hu, hr⟩ := field_run secondSlots foreign
    (List.replicate
      (SmallBiasSampler.fieldExponent (d * a)
        (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t)) false) (d * a)
  refine ⟨u, by simpa using hu, ?_⟩
  rw [hr, ← second_output_slot]
  change BitMachineStackEmbedding.bank secondSlots foreign _
    (secondSlots SamplerMachineTable.output) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp only [List.length_replicate]
  rfl

def reverseProgram (l : SamplerMachineBlockReverse.Label) :
    TM2.Stmt (fun _ : WriterStack => Bool)
      SamplerMachineBlockReverse.Label SamplerMachineBlockReverse.Control :=
  BitMachineStackEmbedding.stmt reverseSlots id id id none
    (SamplerMachineBlockReverse.program l)

private theorem inlineCfg_id (q : SamplerMachineBlockReverse.Config) :
    BitMachineInline.cfg id id none q = q := by
  cases q with
  | mk l v S => cases l <;> rfl

theorem reverse_run_payload (a t₁ t₂ d n : ℕ) (ha : 0 < a)
    (v : Fin n → Fin d → Bool) (foreign : WriterStack → List Bool) :
    ∃ u ≤ (SamplerExactPayloadArrays.secondBlocks a t₂ d).length *
        SamplerMachineBlockReverse.blockStep a +
        ((SamplerExactPayloadArrays.secondBlocks a t₂ d).reverse.flatten).length + 2,
      (((advance reverseProgram)^[u])
        (BitMachineStackEmbedding.stackCfg reverseSlots foreign
          (SamplerMachineBlockReverse.cfg (some .check)
            SamplerMachineBlockReverse.initial
            (SamplerSeedEnumeration.counterTraceTable
              (SmallBiasSampler.fieldExponent (d * a)
                (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂)) (d * a))
            (List.replicate a true) [] [] [] []))).stk secondCell =
        (MatrixMaterialization.storeBits
          (ExecutableSmallBiasSampler.exactFirstFamily a t₁ d)
          (ExecutableSmallBiasSampler.exactSecondFamily a t₂ d) v).second := by
  let steps := (SamplerExactPayloadArrays.secondBlocks a t₂ d).length *
      SamplerMachineBlockReverse.blockStep a +
      ((SamplerExactPayloadArrays.secondBlocks a t₂ d).reverse.flatten).length + 2
  let c := SamplerMachineBlockReverse.cfg (some .check)
    SamplerMachineBlockReverse.initial
    (SamplerSeedEnumeration.counterTraceTable
      (SmallBiasSampler.fieldExponent (d * a)
        (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂)) (d * a))
    (List.replicate a true) [] [] [] []
  have hr := SamplerExactPayloadArrays.run_secondPayload a t₁ t₂ d n ha v
  have hh : (((advance SamplerMachineBlockReverse.program)^[steps]) c).l = none := by
    change (SamplerMachineBlockReverse.run steps c).l = none
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs reverseSlots foreign
    id id id (by intro x; rfl) none
    SamplerMachineBlockReverse.program reverseProgram (by intro l; rfl)
    c steps hh
  refine ⟨u, hu, ?_⟩
  have he' : ((advance reverseProgram)^[u]
      (BitMachineStackEmbedding.stackCfg reverseSlots foreign c)) =
      BitMachineStackEmbedding.stackCfg reverseSlots foreign
        (SamplerMachineBlockReverse.run steps c) := by
    simpa only [BitMachineStackEmbedding.cfg, inlineCfg_id,
      SamplerMachineBlockReverse.run] using he
  rw [hr] at he'
  change ((advance reverseProgram)^[u]
    (BitMachineStackEmbedding.stackCfg reverseSlots foreign c)).stk secondCell = _
  rw [he', ← reverse_output_slot]
  change BitMachineStackEmbedding.bank reverseSlots foreign _
    (reverseSlots 5) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

end EthInapproximability.CurrentPaper.SamplerWriterPayloadFrame
