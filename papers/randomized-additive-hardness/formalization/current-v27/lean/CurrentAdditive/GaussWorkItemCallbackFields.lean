import CurrentAdditive.GaussWorkItemDisposableCleanup

/-! Bank-level facts for repeatedly calling the physical work-item producer.
The serializer consumes only copies of B, f, and j; the retained context is
pointwise unchanged. -/

namespace CurrentAdditive.GaussWorkItemCallbackFields

open EthInapproximability.CurrentPaper
open BitMachineStackEmbedding
open BitMachineEncoding
open Turing Turing.TM2

abbrev Bank := GaussWorkItemCallback.Bank

noncomputable def afterCopies (S : Bank → List Bool) (matrix free index : List Bool) :
    Bank → List Bool :=
  Function.update
    (Function.update (Function.update S ⟨9, by omega⟩ matrix)
      ⟨10, by omega⟩ free)
    ⟨11, by omega⟩ index

noncomputable def afterItem (S : Bank → List Bool) (matrix free index raw : List Bool)
    (W : BitMachineBankSerialize.Bank 3) : Bank → List Bool :=
  (stackCfg GaussWorkItemContextSerialize.copiedSlot
    (afterCopies S matrix free index)
    (BitMachineBankSerialize.cfg none none W [] [] raw)).stk

theorem preserved (S : Bank → List Bool)
    (matrix free index raw : List Bool)
    (W : BitMachineBankSerialize.Bank 3)
    (z : Bank)
    (hz : z ≠ ⟨6, by omega⟩ ∧ z ≠ ⟨7, by omega⟩ ∧
      z ≠ ⟨8, by omega⟩ ∧ z ≠ ⟨9, by omega⟩ ∧
      z ≠ ⟨10, by omega⟩ ∧ z ≠ ⟨11, by omega⟩) :
    afterItem S matrix free index raw W z = S z := by
  have hout : ¬ ∃ x : BitMachineBankSerialize.Stack 3,
      GaussWorkItemContextSerialize.copiedSlot x = z := by
    rintro ⟨x, hx⟩
    rcases x with x | x <;> fin_cases x <;>
      simp [GaussWorkItemContextSerialize.copiedSlot] at hx <;>
      simp_all
  rw [afterItem]
  change (bank GaussWorkItemContextSerialize.copiedSlot
    (afterCopies S matrix free index)
    (BitMachineBankSerialize.cfg none none W [] [] raw).stk) z = _
  rw [bank_outside _ _ _ z hout]
  simp [afterCopies, hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2]

theorem output (S : Bank → List Bool)
    (matrix free index raw : List Bool)
    (W : BitMachineBankSerialize.Bank 3) :
    afterItem S matrix free index raw W ⟨8, by omega⟩ = raw := by
  change (bank GaussWorkItemContextSerialize.copiedSlot
    (afterCopies S matrix free index)
    (BitMachineBankSerialize.cfg none none W [] [] raw).stk)
      (GaussWorkItemContextSerialize.copiedSlot (.inr (2 : Fin 3))) = raw
  rw [bank_at]
  rfl

theorem preserved_high (S : Bank → List Bool)
    (matrix free index raw : List Bool)
    (W : BitMachineBankSerialize.Bank 3)
    (z : Bank) (hz : 12 ≤ z.val) :
    afterItem S matrix free index raw W z = S z := by
  apply preserved S matrix free index raw W z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega

theorem source_empty (S : Bank → List Bool)
    (matrix free index raw : List Bool)
    (W : BitMachineBankSerialize.Bank 3) :
    afterItem S matrix free index raw W ⟨6, by omega⟩ = [] ∧
    afterItem S matrix free index raw W ⟨7, by omega⟩ = [] := by
  constructor
  · change (bank GaussWorkItemContextSerialize.copiedSlot
      (afterCopies S matrix free index)
      (BitMachineBankSerialize.cfg none none W [] [] raw).stk)
        (GaussWorkItemContextSerialize.copiedSlot (.inr (0 : Fin 3))) = []
    rw [bank_at]
    rfl
  · change (bank GaussWorkItemContextSerialize.copiedSlot
      (afterCopies S matrix free index)
      (BitMachineBankSerialize.cfg none none W [] [] raw).stk)
        (GaussWorkItemContextSerialize.copiedSlot (.inr (1 : Fin 3))) = []
    rw [bank_at]
    rfl

theorem physical_item_full {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (hj : S ⟨5, by omega⟩ = List.replicate j.val true)
    (h6 : S ⟨6, by omega⟩ = [])
    (h7 : S ⟨7, by omega⟩ = [])
    (h8 : S ⟨8, by omega⟩ = [])
    (h9 : S ⟨9, by omega⟩ = [])
    (h10 : S ⟨10, by omega⟩ = [])
    (h11 : S ⟨11, by omega⟩ = [])
    (h12 : S ⟨12, by omega⟩ = []) :
    ∃ (t : Nat) (W : BitMachineBankSerialize.Bank 3),
      t ≤ (2 * (GaussPhysical.encodeTypedMatrix B).length + 2) +
        (2 * f.val + 2) + (2 * j.val + 2) + 2 +
        (2 * (GaussWorkItemContextSerialize.workPacket B f j).length + 2) + 1 ∧
      ((advance GaussWorkItemCallback.program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none, none), none), none), S⟩ :
          Turing.TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, (((none, none), none), none),
          afterItem S (GaussPhysical.encodeTypedMatrix B)
            (List.replicate f.val true) (List.replicate j.val true)
            (GaussWorkItemContextSerialize.workPacket B f j) W⟩ := by
  obtain ⟨t, W, ht, hr⟩ :=
    GaussWorkItemCallback.physical_item B f j S []
      hmat hf hj h6 h7 h8 h9 h10 h11 h12
  refine ⟨t, W, ht, ?_⟩
  simpa [afterItem, afterCopies] using hr

#print axioms preserved
#print axioms output
#print axioms preserved_high
#print axioms source_empty
#print axioms physical_item_full

end CurrentAdditive.GaussWorkItemCallbackFields
