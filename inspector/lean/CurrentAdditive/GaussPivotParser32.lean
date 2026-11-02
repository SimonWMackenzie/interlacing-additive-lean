import CurrentAdditive.GaussControlTrace
import EthInapproximability.CurrentPaper.BitMachineBankCodec
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
Physical parsing of the raw four-field Gauss state packet. The fixed Bank4
parser consumes the packet on bank 30 and installs its fields in banks 16--19.
Bank 28 is outside the parser embedding and can retain the original input.
-/

namespace CurrentAdditive.GaussPivotParser32

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open Turing BitMachineEncoding

abbrev Stack := Fin 32
abbrev Label := ParserLabel 4 ⊕ Unit
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : BitMachineBankCodec.Stack 4 ↪ Stack where
  toFun
    | .inl i => ⟨i.val + 16, by omega⟩
    | .inr i => ![30, 31, 29] i
  inj' := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        have hv := congrArg (fun z : Stack => z.val) h
        simp at hv
        exact congrArg Sum.inl (Fin.ext (by omega))
      | inr b =>
        fin_cases b <;> have hv := congrArg (fun z : Stack => z.val) h <;>
          simp at hv <;> omega
    | inr a =>
      cases b with
      | inl b =>
        fin_cases a <;> have hv := congrArg (fun z : Stack => z.val) h <;>
          simp at hv <;> omega
      | inr b => fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (parser 4 l)
  | .inr () => .load (fun _ => none) .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 4 => Bool)
      (ParserLabel 4) Control) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

theorem parse_state {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (foreign : Stack → List Bool) :
    ∃ t ≤ 9 * ((CurrentAdditive.GaussControlTrace.statePacket s).length + 1),
      run t (frame foreign
        (parserCfg (K := 4) (some (.scan 0)) none (fun _ => [])
          (CurrentAdditive.GaussControlTrace.statePacket s) [] [])) =
      frame foreign (parserCfg none (some true)
        (CurrentAdditive.GaussControlTrace.stateBank s) [] [] []) := by
  let bank := CurrentAdditive.GaussControlTrace.stateBank s
  obtain ⟨t, ht, hp⟩ := parser_correct 4
    (CurrentAdditive.GaussControlTrace.statePacket s) []
  have hd : decode 4 (CurrentAdditive.GaussControlTrace.statePacket s) =
      some bank := by
    simp [CurrentAdditive.GaussControlTrace.statePacket, bank]
  rw [hd] at hp
  change parserRun t (parserCfg (K := 4) (some (.scan 0)) none
    (fun _ => []) (CurrentAdditive.GaussControlTrace.statePacket s) [] []) =
    parserCfg none (some true) bank [] [] [] at hp
  have hh : (parserRun t (parserCfg (K := 4) (some (.scan 0)) none
      (fun _ => []) (CurrentAdditive.GaussControlTrace.statePacket s) [] [])).l = none := by
    rw [hp]
    rfl
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl) (some (.inr ()))
    (parser 4) program (by intro l; rfl)
    (parserCfg (K := 4) (some (.scan 0)) none
      (fun _ => []) (CurrentAdditive.GaussControlTrace.statePacket s) [] [])
    t hh
  refine ⟨u, hu.trans ht, ?_⟩
  change run u (frame foreign _) = frame foreign (parserRun t _) at hr
  rw [hp] at hr
  exact hr

theorem parsed_field {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (foreign : Stack → List Bool) (p : Fin 4) :
    (frame foreign (parserCfg none (some true)
      (CurrentAdditive.GaussControlTrace.stateBank s) [] [] [])).stk
      (⟨p.val + 16, by omega⟩ : Stack) =
    CurrentAdditive.GaussControlTrace.stateBank s p := by
  exact BitMachineStackEmbedding.bank_at locate foreign _ (.inl p)

theorem parsed_ambient {m k : Nat}
    (s : CurrentAdditive.GaussControlTrace.State m k)
    (foreign : Stack → List Bool) (j : Stack)
    (hj : j ≠ 16 ∧ j ≠ 17 ∧ j ≠ 18 ∧ j ≠ 19 ∧
      j ≠ 29 ∧ j ≠ 30 ∧ j ≠ 31) :
    (frame foreign (parserCfg none (some true)
      (CurrentAdditive.GaussControlTrace.stateBank s) [] [] [])).stk j =
    foreign j := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨q, hq⟩
  cases q with
  | inl q => fin_cases q <;> simp [locate] at hq <;> simp_all
  | inr q => fin_cases q <;> simp [locate] at hq <;> simp_all

#print axioms parse_state
#print axioms parsed_field
#print axioms parsed_ambient

end CurrentAdditive.GaussPivotParser32
