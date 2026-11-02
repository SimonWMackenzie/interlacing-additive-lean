import CurrentAdditive.GaussAdaptPrepare64
import CurrentAdditive.GaussOperandSerialize64
import CurrentAdditive.GaussSerializeClears

/-! Full-stack form of the frozen operand serializer on its existing Fin64 ABI. -/

namespace CurrentAdditive.GaussAdaptSerialize64

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Stack := Fin 64

noncomputable def finalBank (S : Stack → List Bool)
    (output : List Bool) (U : BitMachineBankSerialize.Bank 12) :
    Stack → List Bool :=
  BitMachineStackEmbedding.bank GaussOperandSerialize64.slot S
    (BitMachineBankSerialize.cfg none none U [] [] output).stk

theorem full_run (flag : Bool)
    (current column row pivot : List Bool)
    (S : Stack → List Bool)
    (hwords : ∀ i : Fin 12,
      S (GaussOperandSerialize64.fieldSlot i) =
        GaussOperandSerialize64.wordBank flag current column row pivot i)
    (h21 : S 21 = []) (h22 : S 22 = []) (h23 : S 23 = []) :
    ∃ t ≤ 2 * (GaussOperandSerialize64.packet flag
        current column row pivot).length + 2,
      ((advance GaussOperandSerialize64.program)^[t])
        (⟨some (.emit 0), none, S⟩ : GaussOperandSerialize64.Config) =
      ⟨none, none,
        finalBank S (GaussOperandSerialize64.packet flag
          current column row pivot) (fun _ => [])⟩ := by
  let B := GaussOperandSerialize64.wordBank flag current column row pivot
  let cLocal := BitMachineBankSerialize.cfg
    (some (.emit 0)) none B [] [] []
  have hready : ∀ k : Fin 12 ⊕ Fin 3,
      cLocal.stk k = S (GaussOperandSerialize64.slot k) := by
    intro k
    cases k with
    | inl i =>
        change B i = S (GaussOperandSerialize64.fieldSlot i)
        exact (hwords i).symm
    | inr i =>
        fin_cases i <;>
          simp [cLocal, BitMachineBankSerialize.cfg,
            BitMachineBankSerialize.contents,
            GaussOperandSerialize64.slot,
            GaussOperandSerialize64.extraSlot,
            h21, h22, h23]
  have hbank : BitMachineStackEmbedding.bank
      GaussOperandSerialize64.slot S cLocal.stk = S :=
    BitMachineStackEmbedding.bank_eq_self
      GaussOperandSerialize64.slot S cLocal.stk hready
  obtain ⟨t, ht, hLocal⟩ :=
    GaussSerializeClears.serialize_empty B
      ([] : List Bool) ([] : List Bool)
  have hLocal' :
      ((advance (BitMachineBankSerialize.program 12))^[t]) cLocal =
        BitMachineBankSerialize.cfg none none (fun _ => []) [] []
          (GaussOperandSerialize64.packet flag current column row pivot) := by
    simpa [BitMachineBankSerialize.run, cLocal,
      GaussOperandSerialize64.packet, B] using hLocal
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    GaussOperandSerialize64.slot S id id id (by intro x; rfl) none
    (BitMachineBankSerialize.program 12) GaussOperandSerialize64.program
    (by intro l; rfl) cLocal t (by rw [hLocal']; rfl)
  have hInit : BitMachineStackEmbedding.cfg
      GaussOperandSerialize64.slot S id id none cLocal =
      (⟨some (.emit 0), none, S⟩ : GaussOperandSerialize64.Config) := by
    change (⟨some (.emit 0), none,
      BitMachineStackEmbedding.bank GaussOperandSerialize64.slot
        S cLocal.stk⟩ : GaussOperandSerialize64.Config) = _
    rw [hbank]
  have hFinal :
      ((advance GaussOperandSerialize64.program)^[u])
        (⟨some (.emit 0), none, S⟩ : GaussOperandSerialize64.Config) =
      ⟨none, none,
        finalBank S (GaussOperandSerialize64.packet flag
          current column row pivot) (fun _ => [])⟩ := by
    rw [← hInit]
    simpa [GaussOperandSerialize64.program,
      hLocal', finalBank,
      BitMachineStackEmbedding.cfg,
      BitMachineInline.cfg] using he
  refine ⟨u, hu.trans ?_, hFinal⟩
  simpa [GaussOperandSerialize64.packet, B] using ht

theorem output_at_23 (S : Stack → List Bool)
    (output : List Bool) (U : BitMachineBankSerialize.Bank 12) :
    finalBank S output U 23 = output := by
  change (BitMachineStackEmbedding.bank GaussOperandSerialize64.slot S
    (BitMachineBankSerialize.cfg none none U [] [] output).stk)
      (GaussOperandSerialize64.slot (.inr 2)) = output
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem field_at (S : Stack → List Bool)
    (output : List Bool) (U : BitMachineBankSerialize.Bank 12)
    (i : Fin 12) :
    finalBank S output U (GaussOperandSerialize64.fieldSlot i) = U i := by
  change (BitMachineStackEmbedding.bank GaussOperandSerialize64.slot S
    (BitMachineBankSerialize.cfg none none U [] [] output).stk)
      (GaussOperandSerialize64.slot (.inl i)) = U i
  rw [BitMachineStackEmbedding.bank_at]
  rfl

theorem scratch_at (S : Stack → List Bool)
    (output : List Bool) (U : BitMachineBankSerialize.Bank 12)
    (i : Fin 3) (hi : i ≠ 2) :
    finalBank S output U (GaussOperandSerialize64.extraSlot i) = [] := by
  fin_cases i
  · change (BitMachineStackEmbedding.bank GaussOperandSerialize64.slot S
      (BitMachineBankSerialize.cfg none none U [] [] output).stk)
        (GaussOperandSerialize64.slot (.inr 0)) = []
    rw [BitMachineStackEmbedding.bank_at]
    rfl
  · change (BitMachineStackEmbedding.bank GaussOperandSerialize64.slot S
      (BitMachineBankSerialize.cfg none none U [] [] output).stk)
        (GaussOperandSerialize64.slot (.inr 1)) = []
    rw [BitMachineStackEmbedding.bank_at]
    rfl
  · exact False.elim (hi rfl)

theorem foreign_at (S : Stack → List Bool)
    (output : List Bool) (U : BitMachineBankSerialize.Bank 12)
    (k : Stack) (hk : ¬ ∃ i, GaussOperandSerialize64.slot i = k) :
    finalBank S output U k = S k :=
  BitMachineStackEmbedding.bank_outside
    GaussOperandSerialize64.slot S _ k hk

#print axioms full_run
#print axioms output_at_23
#print axioms foreign_at

end CurrentAdditive.GaussAdaptSerialize64
