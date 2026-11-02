import CurrentAdditive.GaussStateMatrixContext
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! One physical Bank3 work-item serialization on the ambient post-Gauss
bank.  The fixed local serializer is embedded on six designated cells; all
other cells, including the original state and unary width, are preserved.
The matrix/index/free copies used here are disposable; preparing them afresh
and iterating over every index remains the outer-loop obligation. -/

namespace CurrentAdditive.GaussWorkItemContextSerialize

open Turing Turing.TM2 EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding

abbrev Bank := GaussStateMatrixContext.Bank
abbrev Local := BitMachineBankSerialize.Stack 3

def workBank {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) : BitMachineBankCodec.Bank 3 :=
  ![GaussPhysical.encodeTypedMatrix B,
    List.replicate j.val true, List.replicate f.val true]

def workPacket {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) : List Bool :=
  BitMachineBankCodec.encode (workBank B f j)

def slot : Local ↪ Bank where
  toFun
    | .inl i => if i = 0 then ⟨4, by omega⟩ else
        if i = 1 then ⟨5, by omega⟩ else ⟨1, by omega⟩
    | .inr i => if i = 0 then ⟨6, by omega⟩ else
        if i = 1 then ⟨7, by omega⟩ else ⟨8, by omega⟩
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;>
      fin_cases a <;> fin_cases b <;>
      simp_all

def program (l : BitMachineBankSerialize.Label 3) :=
  stackStmt slot (BitMachineBankSerialize.program 3 l)

theorem prepared_bank_eq {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool) (output : List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hj : S ⟨5, by omega⟩ = List.replicate j.val true)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (hsrc : S ⟨6, by omega⟩ = [])
    (hsaved : S ⟨7, by omega⟩ = [])
    (hout : S ⟨8, by omega⟩ = output) :
    bank slot S
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (workBank B f j) [] [] output).stk = S := by
  apply bank_eq_self
  intro x
  rcases x with x | x <;> fin_cases x <;>
    simp [slot, BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents, workBank,
      hmat, hj, hf, hsrc, hsaved, hout]

theorem physical_one_item {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool) (output : List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hj : S ⟨5, by omega⟩ = List.replicate j.val true)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (hsrc : S ⟨6, by omega⟩ = [])
    (hsaved : S ⟨7, by omega⟩ = [])
    (hout : S ⟨8, by omega⟩ = output) :
    ∃ (t : Nat) (W : BitMachineBankSerialize.Bank 3),
      t ≤ 2 * (workPacket B f j).length + 2 ∧
      ((advance program)^[t])
        (⟨some (.emit 0), none, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        stackCfg slot S
          (BitMachineBankSerialize.cfg none none W [] []
            (workPacket B f j ++ output)) := by
  obtain ⟨t, W, ht, hr⟩ :=
    (show ∃ (t : Nat) (W : BitMachineBankSerialize.Bank 3),
      t ≤ 2 * (workPacket B f j).length + 2 ∧
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (workBank B f j) [] [] output) =
        BitMachineBankSerialize.cfg none none W [] []
          (workPacket B f j ++ output) from by
      simpa only [workPacket, BitMachineBankCodec.encode_eq_list,
        BitMachineBankSerialize.encode] using
        BitMachineBankSerialize.serialize (workBank B f j) [] output)
  let c := BitMachineBankSerialize.cfg (some (.emit 0)) none
    (workBank B f j) [] [] output
  have he := BitMachineStackRun.run slot S
    (BitMachineBankSerialize.program 3) c t
  change ((advance program)^[t]) (stackCfg slot S c) =
    stackCfg slot S (BitMachineBankSerialize.run t c) at he
  rw [hr] at he
  have hstart : stackCfg slot S c =
      (⟨some (.emit 0), none, S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) := by
    unfold stackCfg
    congr 1
    exact prepared_bank_eq B f j S output
      hmat hj hf hsrc hsaved hout
  rw [hstart] at he
  exact ⟨t, W, ht, he⟩

theorem state_outside :
    ¬ ∃ x : Local, slot x = (⟨0, by omega⟩ : Bank) := by
  rintro ⟨x, h⟩
  rcases x with x | x <;> fin_cases x <;> simp [slot] at h

theorem width_outside :
    ¬ ∃ x : Local, slot x = (⟨3, by omega⟩ : Bank) := by
  rintro ⟨x, h⟩
  rcases x with x | x <;> fin_cases x <;> simp [slot] at h

theorem physical_one_item_fields {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool) (output : List Bool)
    (hmat : S ⟨4, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hj : S ⟨5, by omega⟩ = List.replicate j.val true)
    (hf : S ⟨1, by omega⟩ = List.replicate f.val true)
    (hsrc : S ⟨6, by omega⟩ = [])
    (hsaved : S ⟨7, by omega⟩ = [])
    (hout : S ⟨8, by omega⟩ = output) :
    ∃ t ≤ 2 * (workPacket B f j).length + 2,
      let c := ((advance program)^[t])
        (⟨some (.emit 0), none, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _)
      c.l = none ∧
      c.stk ⟨8, by omega⟩ = workPacket B f j ++ output ∧
      c.stk ⟨0, by omega⟩ = S ⟨0, by omega⟩ ∧
      c.stk ⟨3, by omega⟩ = S ⟨3, by omega⟩ := by
  obtain ⟨t, W, ht, hr⟩ :=
    physical_one_item B f j S output hmat hj hf hsrc hsaved hout
  refine ⟨t, ht, ?_⟩
  rw [hr]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · change (bank slot S
      (BitMachineBankSerialize.cfg none none W [] []
        (workPacket B f j ++ output)).stk)
        (slot (.inr (2 : Fin 3))) = _
    rw [bank_at]
    rfl
  · change (bank slot S
      (BitMachineBankSerialize.cfg none none W [] []
        (workPacket B f j ++ output)).stk) ⟨0, by omega⟩ = _
    exact bank_outside slot S _ _ state_outside
  · change (bank slot S
      (BitMachineBankSerialize.cfg none none W [] []
        (workPacket B f j ++ output)).stk) ⟨3, by omega⟩ = _
    exact bank_outside slot S _ _ width_outside

def copiedSlot : Local ↪ Bank where
  toFun
    | .inl i => if i = 0 then ⟨9, by omega⟩ else
        if i = 1 then ⟨11, by omega⟩ else ⟨10, by omega⟩
    | .inr i => if i = 0 then ⟨6, by omega⟩ else
        if i = 1 then ⟨7, by omega⟩ else ⟨8, by omega⟩
  inj' := by
    intro a b h
    rcases a with a | a <;> rcases b with b | b <;>
      fin_cases a <;> fin_cases b <;>
      simp_all

def copiedProgram (l : BitMachineBankSerialize.Label 3) :=
  stackStmt copiedSlot (BitMachineBankSerialize.program 3 l)

theorem copied_prepared_bank_eq {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool) (output : List Bool)
    (hmat : S ⟨9, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hj : S ⟨11, by omega⟩ = List.replicate j.val true)
    (hf : S ⟨10, by omega⟩ = List.replicate f.val true)
    (hsrc : S ⟨6, by omega⟩ = [])
    (hsaved : S ⟨7, by omega⟩ = [])
    (hout : S ⟨8, by omega⟩ = output) :
    bank copiedSlot S
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (workBank B f j) [] [] output).stk = S := by
  apply bank_eq_self
  intro x
  rcases x with x | x <;> fin_cases x <;>
    simp [copiedSlot, BitMachineBankSerialize.cfg,
      BitMachineBankSerialize.contents, workBank,
      hmat, hj, hf, hsrc, hsaved, hout]

theorem physical_one_item_copied {m k : Nat}
    (B : Fin m → Fin k → ℚ) (f j : Fin k)
    (S : Bank → List Bool) (output : List Bool)
    (hmat : S ⟨9, by omega⟩ = GaussPhysical.encodeTypedMatrix B)
    (hj : S ⟨11, by omega⟩ = List.replicate j.val true)
    (hf : S ⟨10, by omega⟩ = List.replicate f.val true)
    (hsrc : S ⟨6, by omega⟩ = [])
    (hsaved : S ⟨7, by omega⟩ = [])
    (hout : S ⟨8, by omega⟩ = output) :
    ∃ (t : Nat) (W : BitMachineBankSerialize.Bank 3),
      t ≤ 2 * (workPacket B f j).length + 2 ∧
      ((advance copiedProgram)^[t])
        (⟨some (.emit 0), none, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        stackCfg copiedSlot S
          (BitMachineBankSerialize.cfg none none W [] []
            (workPacket B f j ++ output)) := by
  obtain ⟨t, W, ht, hr⟩ :=
    (show ∃ (t : Nat) (W : BitMachineBankSerialize.Bank 3),
      t ≤ 2 * (workPacket B f j).length + 2 ∧
      BitMachineBankSerialize.run t
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (workBank B f j) [] [] output) =
        BitMachineBankSerialize.cfg none none W [] []
          (workPacket B f j ++ output) from by
      simpa only [workPacket, BitMachineBankCodec.encode_eq_list,
        BitMachineBankSerialize.encode] using
        BitMachineBankSerialize.serialize (workBank B f j) [] output)
  let c := BitMachineBankSerialize.cfg (some (.emit 0)) none
    (workBank B f j) [] [] output
  have he := BitMachineStackRun.run copiedSlot S
    (BitMachineBankSerialize.program 3) c t
  change ((advance copiedProgram)^[t]) (stackCfg copiedSlot S c) =
    stackCfg copiedSlot S (BitMachineBankSerialize.run t c) at he
  rw [hr] at he
  have hstart : stackCfg copiedSlot S c =
      (⟨some (.emit 0), none, S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) := by
    unfold stackCfg
    congr 1
    exact copied_prepared_bank_eq B f j S output
      hmat hj hf hsrc hsaved hout
  rw [hstart] at he
  exact ⟨t, W, ht, he⟩

#print axioms physical_one_item
#print axioms physical_one_item_fields
#print axioms physical_one_item_copied

end CurrentAdditive.GaussWorkItemContextSerialize
