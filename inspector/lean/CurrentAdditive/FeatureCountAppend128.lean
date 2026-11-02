import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-! A protected unary count update after one eligible old descriptor.
Bank 33 carries the unary alphabet length, bank 12 the running feature count,
and bank 35 is the only scratch location. -/

namespace CurrentAdditive.FeatureCountAppend128

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Turing

abbrev Stack := Fin 128
abbrev Label := BitMachineCopy.Label
abbrev Control := Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def slot : Fin 3 ↪ Stack where
  toFun
    | 0 => 33
    | 1 => 12
    | _ => 35
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def program (l : Label) :
    TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  BitMachineStackEmbedding.stmt slot id id id none
    (BitMachineCopy.program l)

def run (t : Nat) (c : Config) : Config :=
  ((advance program)^[t]) c

noncomputable def prepared (foreign : Stack → List Bool)
    (alphabetCount count : List Bool) : Config :=
  BitMachineStackEmbedding.cfg slot foreign id id none
    (BitMachineCopy.cfg (some .scan) none alphabetCount count [])

noncomputable def finished (foreign : Stack → List Bool)
    (alphabetCount count : List Bool) : Config :=
  BitMachineStackEmbedding.cfg slot foreign id id none
    (BitMachineCopy.cfg none none alphabetCount
      (alphabetCount ++ count) [])

theorem append_run (foreign : Stack → List Bool)
    (alphabetCount count : List Bool) :
    ∃ t ≤ 2*alphabetCount.length+2,
      run t (prepared foreign alphabetCount count) =
        finished foreign alphabetCount count := by
  have hlocal := BitMachineCopy.run_correct none alphabetCount count
  have hhalt :
      (((advance BitMachineCopy.program)^[2*alphabetCount.length+2])
        (BitMachineCopy.cfg (some .scan) none alphabetCount count [])).l =
      none := by
    rw [← BitMachineCopy.run, hlocal]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    slot foreign id id id (by intro; rfl) none
    BitMachineCopy.program program (by intro; rfl)
    (BitMachineCopy.cfg (some .scan) none alphabetCount count [])
    (2*alphabetCount.length+2) hhalt
  refine ⟨t, ht, ?_⟩
  rw [← BitMachineCopy.run, hlocal] at he
  exact he

theorem count_output (foreign : Stack → List Bool)
    (alphabetCount count : List Bool) :
    (finished foreign alphabetCount count).stk 12 =
      alphabetCount ++ count := by
  exact BitMachineStackEmbedding.bank_at slot foreign
    (BitMachineCopy.cfg none none alphabetCount
      (alphabetCount ++ count) []).stk 1

theorem alphabet_count_preserved (foreign : Stack → List Bool)
    (alphabetCount count : List Bool) :
    (finished foreign alphabetCount count).stk 33 = alphabetCount := by
  exact BitMachineStackEmbedding.bank_at slot foreign
    (BitMachineCopy.cfg none none alphabetCount
      (alphabetCount ++ count) []).stk 0

theorem foreign_preserved (foreign : Stack → List Bool)
    (alphabetCount count : List Bool) (k : Stack)
    (hk33 : k ≠ 33) (hk12 : k ≠ 12) (hk35 : k ≠ 35) :
    (finished foreign alphabetCount count).stk k = foreign k := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [slot] at hi <;> simp_all

theorem prepared_eq (S : Stack → List Bool)
    (alphabetCount count : List Bool)
    (h33 : S 33 = alphabetCount) (h12 : S 12 = count)
    (h35 : S 35 = []) :
    prepared S alphabetCount count =
      (⟨some .scan, none, S⟩ : Config) := by
  change (⟨some .scan, none,
      BitMachineStackEmbedding.bank slot S
        (BitMachineCopy.stackContents alphabetCount count [])⟩ :
      Config) = ⟨some .scan, none, S⟩
  congr 1
  · change BitMachineStackEmbedding.bank slot S
        (BitMachineCopy.stackContents alphabetCount count []) = S
    have hlocal : BitMachineCopy.stackContents alphabetCount count [] =
        fun k => S (slot k) := by
      funext k
      fin_cases k <;>
        simp [BitMachineCopy.stackContents, slot, h33, h12, h35]
    rw [hlocal]
    exact BitMachineStackEmbedding.bank_restrict slot S

theorem physical_count_update (S : Stack → List Bool)
    (alphabetCount count : List Bool)
    (h33 : S 33 = alphabetCount) (h12 : S 12 = count)
    (h35 : S 35 = []) :
    ∃ t ≤ 2*alphabetCount.length+2,
      let z := run t ⟨some .scan, none, S⟩
      z.l = none ∧ z.stk 12 = alphabetCount ++ count ∧
      z.stk 33 = alphabetCount ∧
      (∀ k : Stack, k ≠ 33 → k ≠ 12 → k ≠ 35 →
        z.stk k = S k) := by
  obtain ⟨t, ht, hr⟩ := append_run S alphabetCount count
  rw [prepared_eq S alphabetCount count h33 h12 h35] at hr
  refine ⟨t, ht, ?_, ?_, ?_, ?_⟩
  · exact congrArg TM2.Cfg.l hr
  · exact (congrArg (fun z => z.stk (12 : Stack)) hr).trans
      (count_output S alphabetCount count)
  · exact (congrArg (fun z => z.stk (33 : Stack)) hr).trans
      (alphabet_count_preserved S alphabetCount count)
  · intro k hk33 hk12 hk35
    exact (congrArg (fun z => z.stk k) hr).trans
      (foreign_preserved S alphabetCount count k hk33 hk12 hk35)

#print axioms append_run
#print axioms count_output
#print axioms alphabet_count_preserved
#print axioms foreign_preserved
#print axioms prepared_eq
#print axioms physical_count_update

end CurrentAdditive.FeatureCountAppend128
