import CurrentAdditive.CodeDPairProductTargetV2
import CurrentAdditive.CodeDPairSerializerClear
import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
A literal finite-stack callback fragment for the nested append enumeration.
Given separate encoded RawRat words on banks 7 and 5, it writes the
exact two-field product request to request bank 4, before an existing output
suffix.  The source list, index, alphabet context and loop fuel remain on
banks 8, 10, 12 and 13.  This is one physical pair emission; list traversal
and extraction of the RawRat fields from entry records are separate work.
-/

namespace CurrentAdditive.CodeDPairWeights15

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.CodeDCodec
open Turing BitMachineEncoding

abbrev Stack := Fin 15
abbrev Label := BitMachineBankSerialize.Label 2 ⊕ Unit
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : BitMachineBankSerialize.Stack 2 ↪ Stack where
  toFun
    | .inl i => ![7, 5] i
    | .inr i => ![14, 11, 4] i
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

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (BitMachineBankSerialize.program 2 l)
  | .inr () => .halt

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

def pairBank (x y : RawRat) : BitMachineBankSerialize.Bank 2 :=
  fun i => if i = 0 then encodeRawRat x else encodeRawRat y

noncomputable def frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 2 => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

theorem pairBank_bytes (x y : RawRat) :
    BitMachineBankSerialize.encode (List.ofFn (pairBank x y)) =
      CodeDPairProductTargetV2.pairBytes x y := by
  unfold CodeDPairProductTargetV2.pairBytes
  rw [BitMachineBankCodec.encode_eq_list]
  rfl

theorem emit_pair (x y : RawRat) (foreign : Stack → List Bool)
    (suffix : List Bool) :
    ∃ t ≤ 2*(CodeDPairProductTargetV2.pairBytes x y).length+2,
      ∃ S' : BitMachineBankSerialize.Bank 2,
        run t (frame foreign
          (BitMachineBankSerialize.cfg (some (.emit 0)) none
            (pairBank x y) [] [] suffix)) =
          frame foreign
            (BitMachineBankSerialize.cfg none none S' [] []
              (CodeDPairProductTargetV2.pairBytes x y ++ suffix)) := by
  obtain ⟨t, S', ht, hr⟩ :=
    BitMachineBankSerialize.serialize (pairBank x y) [] suffix
  have hh : (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (pairBank x y) [] [] suffix)).l = none := by
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl)
    (some (.inr ())) (BitMachineBankSerialize.program 2) program
    (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (pairBank x y) [] [] suffix) t hh
  refine ⟨u, ?_, S', ?_⟩
  · rw [pairBank_bytes] at ht
    omega
  · change run u (frame foreign _) =
      frame foreign (BitMachineBankSerialize.run t _) at he
    rw [hr] at he
    simpa only [pairBank_bytes] using he

theorem emit_pair_cleared (x y : RawRat) (foreign : Stack → List Bool) :
    ∃ t ≤ 2*(CodeDPairProductTargetV2.pairBytes x y).length+2,
      run t (frame foreign
        (BitMachineBankSerialize.cfg (some (.emit 0)) none
          (pairBank x y) [] [] [])) =
      frame foreign
        (BitMachineBankSerialize.cfg none none
          (CodeDPairSerializerClear.cleared (pairBank x y)) [] []
          (CodeDPairProductTargetV2.pairBytes x y)) := by
  let xb := encodeRawRat x
  let yb := encodeRawRat y
  let t := xb.length + 1 + (yb.length + 1) +
    ((EncodedCommunication.field xb ++ EncodedCommunication.field yb).length + 2)
  have hb : CodeDPairProductTargetV2.pairBytes x y =
      EncodedCommunication.field xb ++ EncodedCommunication.field yb := by
    rw [← pairBank_bytes]
    simpa [xb, yb, pairBank, CodeDPairSerializerClear.words] using
      (CodeDPairSerializerClear.serialized_words xb yb)
  have hr : BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (pairBank x y) [] [] []) =
      BitMachineBankSerialize.cfg none none
        (CodeDPairSerializerClear.cleared (pairBank x y)) [] []
        (CodeDPairProductTargetV2.pairBytes x y) := by
    change BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (CodeDPairSerializerClear.words xb yb) [] [] []) =
      BitMachineBankSerialize.cfg none none
        (CodeDPairSerializerClear.cleared
          (CodeDPairSerializerClear.words xb yb)) [] [] _
    rw [hb]
    exact CodeDPairSerializerClear.serialize_cleared xb yb
  have hh : (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (pairBank x y) [] [] [])).l = none := by rw [hr]; rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl)
    (some (.inr ())) (BitMachineBankSerialize.program 2) program
    (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (pairBank x y) [] [] []) t hh
  refine ⟨u, ?_, ?_⟩
  · have hx := EncodedCommunication.field_length xb
    have hy := EncodedCommunication.field_length yb
    rw [hb]
    simp only [List.length_append] at *
    dsimp only [t] at hu
    simp only [List.length_append] at hu
    omega
  · change run u (frame foreign _) =
      frame foreign (BitMachineBankSerialize.run t _) at he
    rw [hr] at he
    exact he

theorem foreign_preserved (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 2 => Bool)
      (BitMachineBankSerialize.Label 2) (Option Bool)) :
    (frame foreign c).stk 8 = foreign 8 ∧
    (frame foreign c).stk 10 = foreign 10 ∧
    (frame foreign c).stk 12 = foreign 12 ∧
    (frame foreign c).stk 13 = foreign 13 := by
  constructor
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    cases k with
    | inl k => fin_cases k <;> cases hk
    | inr k => fin_cases k <;> cases hk
  constructor
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    cases k with
    | inl k => fin_cases k <;> cases hk
    | inr k => fin_cases k <;> cases hk
  constructor
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    cases k with
    | inl k => fin_cases k <;> cases hk
    | inr k => fin_cases k <;> cases hk
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    cases k with
    | inl k => fin_cases k <;> cases hk
    | inr k => fin_cases k <;> cases hk

#print axioms emit_pair
#print axioms emit_pair_cleared
#print axioms foreign_preserved

end CurrentAdditive.CodeDPairWeights15
