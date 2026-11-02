import EthInapproximability.CurrentPaper.BitMachineBankSerialize
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Frame a two-field product request as one item of a V2 list.
Input bank 4 holds the request bytes; output bank 5 receives one outer field.
All unrelated context banks, including the accumulated output on bank 9,
are preserved by the literal embedded serializer. -/

namespace CurrentAdditive.CodeDFramePair15

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankSerialize
open Turing BitMachineEncoding EncodedCommunication

abbrev Stack := Fin 15
abbrev Label := BitMachineBankSerialize.Label 1 ⊕ Unit
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : BitMachineBankSerialize.Stack 1 ↪ Stack where
  toFun
    | .inl i => ![4] i
    | .inr i => ![14, 11, 5] i
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
      (some (.inr ())) (BitMachineBankSerialize.program 1 l)
  | .inr () => .halt

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

def oneBank (request : List Bool) : BitMachineBankSerialize.Bank 1 :=
  fun _ => request

noncomputable def frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 1 => Bool)
      (BitMachineBankSerialize.Label 1) (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

theorem oneBank_bytes (request : List Bool) :
    BitMachineBankSerialize.encode (List.ofFn (oneBank request)) =
      field request := by
  simp [oneBank, BitMachineBankSerialize.encode]

theorem emit_field (request : List Bool) (foreign : Stack → List Bool)
    (suffix : List Bool) :
    ∃ t ≤ 2*(field request).length+2,
      ∃ S' : BitMachineBankSerialize.Bank 1,
        run t (frame foreign
          (BitMachineBankSerialize.cfg (some (.emit 0)) none
            (oneBank request) [] [] suffix)) =
          frame foreign
            (BitMachineBankSerialize.cfg none none S' [] []
              (field request ++ suffix)) := by
  obtain ⟨t, S', ht, hr⟩ :=
    BitMachineBankSerialize.serialize (oneBank request) [] suffix
  have hh : (BitMachineBankSerialize.run t
      (BitMachineBankSerialize.cfg (some (.emit 0)) none
        (oneBank request) [] [] suffix)).l = none := by
    rw [hr]
    rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl)
    (some (.inr ())) (BitMachineBankSerialize.program 1) program
    (by intro l; rfl)
    (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (oneBank request) [] [] suffix) t hh
  refine ⟨u, ?_, S', ?_⟩
  · rw [oneBank_bytes] at ht
    omega
  · change run u (frame foreign _) =
      frame foreign (BitMachineBankSerialize.run t _) at he
    rw [hr] at he
    simpa only [oneBank_bytes] using he

theorem accumulated_output_preserved (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 1 => Bool)
      (BitMachineBankSerialize.Label 1) (Option Bool)) :
    (frame foreign c).stk 9 = foreign 9 := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨k, hk⟩
  cases k with
  | inl k => fin_cases k <;> cases hk
  | inr k => fin_cases k <;> cases hk

#print axioms emit_field
#print axioms accumulated_output_preserved

end CurrentAdditive.CodeDFramePair15
