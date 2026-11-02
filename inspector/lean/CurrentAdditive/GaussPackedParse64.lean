import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! A fixed physical parser for packed matrix, row, and column words. -/

namespace CurrentAdditive.GaussPackedParse64

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open Turing BitMachineEncoding

abbrev Stack := Fin 64
abbrev Label := ParserLabel 3 ⊕ Unit
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : BitMachineBankCodec.Stack 3 ↪ Stack where
  toFun
    | .inl i => ![8, 15, 16] i
    | .inr i => ![61, 62, 60] i
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
      none (parser 3 l)
  | .inr () => .load (fun _ => none) .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 3 => Bool)
      (ParserLabel 3) Control) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    none c

theorem parse_encoded (bank : BitMachineBankCodec.Bank 3)
    (foreign : Stack → List Bool) :
    ∃ t ≤ 7 * ((encode bank).length + 1),
      run t (frame foreign
        (parserCfg (K := 3) (some (.scan 0)) none (fun _ => [])
          (encode bank) [] [])) =
      frame foreign (parserCfg none (some true) bank [] [] []) := by
  obtain ⟨t, ht, hp⟩ := parser_correct 3 (encode bank) []
  simp only [decode_encode, ParsePost] at hp
  have hh : (parserRun t (parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) (encode bank) [] [])).l = none := by
    rw [hp]
    rfl
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl) none
    (parser 3) program (by intro l; rfl)
    (parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) (encode bank) [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run u (frame foreign _) = frame foreign (parserRun t _) at hr
  rw [hp] at hr
  exact hr

theorem parse_halts_all (input : List Bool)
    (foreign : Stack → List Bool) :
    ∃ t ≤ 7 * (input.length + 1),
      (run t (frame foreign
        (parserCfg (K := 3) (some (.scan 0)) none (fun _ => [])
          input [] []))).l = none := by
  obtain ⟨t, ht, hp⟩ := parser_correct 3 input []
  have hh : (parserRun t (parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) input [] [])).l = none := by
    cases hd : decode 3 input with
    | none =>
        simp only [ParsePost, hd] at hp
        exact hp.1
    | some bank =>
        simp only [ParsePost, hd] at hp
        rw [hp]
        rfl
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl) none
    (parser 3) program (by intro l; rfl)
    (parserCfg (K := 3) (some (.scan 0)) none
      (fun _ => []) input [] []) t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run u (frame foreign _) = frame foreign (parserRun t _) at hr
  rw [hr]
  simp only [frame, BitMachineStackEmbedding.cfg,
    BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg]
  rw [hh]

theorem parsed_field (bank : BitMachineBankCodec.Bank 3)
    (foreign : Stack → List Bool) (p : Fin 3) :
    (frame foreign (parserCfg none (some true) bank [] [] [])).stk
      (locate (.inl p)) = bank p := by
  exact BitMachineStackEmbedding.bank_at locate foreign _ (.inl p)

#print axioms parse_encoded
#print axioms parse_halts_all
#print axioms parsed_field

end CurrentAdditive.GaussPackedParse64
