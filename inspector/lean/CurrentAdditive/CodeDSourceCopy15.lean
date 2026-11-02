import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! Copy the retained source entry from context bank 12 into scratch bank 3,
preserving context and output.  The copy is literal and costs two scans. -/

namespace CurrentAdditive.CodeDSourceCopy15

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 15
abbrev Label := BitMachineCopy.Label ⊕ Unit
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def locate : Fin 3 ↪ Stack where
  toFun i := ![12, 3, 14] i
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt locate Sum.inl id id
      (some (.inr ())) (BitMachineCopy.program l)
  | .inr () => .halt

def run (t : Nat) (c : Config) := ((advance program)^[t]) c

noncomputable def frame (foreign : Stack → List Bool)
    (c : TM2.Cfg (fun _ : Fin 3 => Bool)
      BitMachineCopy.Label (Option Bool)) : Config :=
  BitMachineStackEmbedding.cfg locate foreign Sum.inl id
    (some (.inr ())) c

theorem copy_source (record : List Bool) (foreign : Stack → List Bool) :
    ∃ t ≤ 2*record.length+2,
      run t (frame foreign (BitMachineCopy.cfg (some .scan) none record [] [])) =
        frame foreign (BitMachineCopy.cfg none none record record []) := by
  have hr := BitMachineCopy.run_correct none record []
  have hh : (BitMachineCopy.run (2*record.length+2)
      (BitMachineCopy.cfg (some .scan) none record [] [])).l = none := by
    rw [hr]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    locate foreign Sum.inl id id (by intro v; rfl)
    (some (.inr ())) BitMachineCopy.program program
    (by intro l; rfl) (BitMachineCopy.cfg (some .scan) none record [] [])
    (2*record.length+2) hh
  refine ⟨t, ht, ?_⟩
  change run t (frame foreign _) = frame foreign (BitMachineCopy.run _ _) at he
  rw [hr] at he
  simpa using he

theorem copied_banks (record : List Bool) (foreign : Stack → List Bool) :
    (frame foreign (BitMachineCopy.cfg none none record record [])).stk 12 = record ∧
    (frame foreign (BitMachineCopy.cfg none none record record [])).stk 3 = record ∧
    (frame foreign (BitMachineCopy.cfg none none record record [])).stk 9 = foreign 9 := by
  constructor
  · exact BitMachineStackEmbedding.bank_at locate foreign _ 0
  constructor
  · exact BitMachineStackEmbedding.bank_at locate foreign _ 1
  · apply BitMachineStackEmbedding.bank_outside
    rintro ⟨k, hk⟩
    fin_cases k <;> cases hk

#print axioms copy_source
#print axioms copied_banks

end CurrentAdditive.CodeDSourceCopy15
