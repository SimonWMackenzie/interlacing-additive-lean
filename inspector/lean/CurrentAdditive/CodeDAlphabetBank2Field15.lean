import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Physical Bank2 parsing inside the fifteen-stack append callback.  The
selected record is consumed from bank 6; its first and second payload fields
are staged on banks 0 and 5.  Output bank 9 and the scheduler context banks
are untouched. -/

namespace CurrentAdditive.CodeDAlphabetBank2Field15

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open Turing BitMachineEncoding

abbrev Stack := Fin 15
abbrev Label := ParserLabel 2 ⊕ Unit
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : BitMachineBankCodec.Stack 2 ↪ Stack where
  toFun
    | .inl i => ![0, 5] i
    | .inr i => ![6, 14, 11] i
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
      (some (.inr ())) (parser 2 l)
  | .inr () => .load (fun _ => none) .halt

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 2 => Bool)
      (ParserLabel 2) Control) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

theorem parse_record (bank : Bank 2) (foreign : Stack → List Bool)
    (output : List Bool) :
    ∃ t ≤ 5*((encode bank).length+1),
      run t (frame foreign
        (parserCfg (K := 2) (some (.scan 0)) none (fun _ => [])
          (encode bank) [] output)) =
      frame foreign (parserCfg none (some true) bank [] [] output) := by
  obtain ⟨t, ht, hp⟩ := parser_correct 2 (encode bank) output
  have hd : decode 2 (encode bank) = some bank := decode_encode bank
  rw [hd] at hp
  change parserRun t (parserCfg (K := 2) (some (.scan 0)) none (fun _ => [])
    (encode bank) [] output) = parserCfg none (some true) bank [] [] output at hp
  have hh : (parserRun t
      (parserCfg (K := 2) (some (.scan 0)) none (fun _ => [])
        (encode bank) [] output)).l = none := by rw [hp]; rfl
  obtain ⟨u, hu, he⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl)
    (some (.inr ())) (parser 2) program (by intro l; rfl)
    (parserCfg (K := 2) (some (.scan 0)) none (fun _ => [])
      (encode bank) [] output) t hh
  refine ⟨u, ?_, ?_⟩
  · omega
  · change run u (frame foreign _) = frame foreign (parserRun t _) at he
    rw [hp] at he
    exact he

theorem staged_fields (bank : Bank 2) (foreign : Stack → List Bool)
    (output : List Bool) :
    (frame foreign (parserCfg none (some true) bank [] [] output)).stk 0 = bank 0 ∧
    (frame foreign (parserCfg none (some true) bank [] [] output)).stk 5 = bank 1 ∧
    (frame foreign (parserCfg none (some true) bank [] [] output)).stk 9 = foreign 9 := by
  constructor
  · exact BitMachineStackEmbedding.bank_at locate foreign _ (.inl 0)
  constructor
  · exact BitMachineStackEmbedding.bank_at locate foreign _ (.inl 1)
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    cases k with
    | inl k => fin_cases k <;> cases hk
    | inr k => fin_cases k <;> cases hk

#print axioms parse_record
#print axioms staged_fields

end CurrentAdditive.CodeDAlphabetBank2Field15
