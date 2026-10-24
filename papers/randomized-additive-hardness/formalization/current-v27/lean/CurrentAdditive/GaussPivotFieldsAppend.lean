import CurrentAdditive.GaussControlTrace
import CurrentAdditive.CodeDAppendAtEnd15

/-!
The physical append stage for the *body* of the ordered V2 pivot list.  The
existing fields occupy bank 9.  Bank 5 contains the already framed new pivot
pair, `natField pair.length ++ pair`.  The finite TM2 program copies both
words through its own scratch banks and leaves their exact concatenation on
bank 9.  The V2 count-header increment and final Bank4 packing are separate
stages; this theorem does not claim either of them.
-/

namespace CurrentAdditive.GaussPivotFieldsAppend

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.CodeDAppendAtEnd15
open CurrentAdditive.GaussControlTrace
open Turing BitMachineEncoding

def payload {m k : Nat} (p : Fin m × Fin k) : List Bool :=
  natField (pivotPacket p).length ++ pivotPacket p

def initialBank {m k : Nat} (foreign : Stack → List Bool)
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k) : Stack → List Bool :=
  CurrentAdditive.CodeDAppendAtEnd15.initialBank foreign
    (SourceListEncoding.fields (ps.map pivotPacket)) (payload p)

def appendClock {m k : Nat} (ps : List (Fin m × Fin k))
    (p : Fin m × Fin k) : Nat :=
  4 * (SourceListEncoding.fields (ps.map pivotPacket)).length +
    2 * (payload p).length + 6

private theorem fields_append_one (xs : List (List Bool))
    (p : List Bool) :
    SourceListEncoding.fields (xs ++ [p]) =
      SourceListEncoding.fields xs ++ natField p.length ++ p := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x xs ih =>
      simp only [List.cons_append, SourceListEncoding.fields]
      rw [ih]
      simp [List.append_assoc]

theorem physical_append {m k : Nat} (foreign : Stack → List Bool)
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (h11 : foreign 11 = []) (h14 : foreign 14 = []) :
    run (appendClock ps p)
      ⟨some .saveScan, ((), none), initialBank foreign ps p⟩ =
    ⟨some .done, ((), none),
      Function.update
        (Function.update (Function.update
          (initialBank foreign ps p) 9 []) 5 []) 9
        (SourceListEncoding.fields ((ps ++ [p]).map pivotPacket))⟩ := by
  have h := CurrentAdditive.CodeDAppendAtEnd15.append_run foreign
    (SourceListEncoding.fields (ps.map pivotPacket)) (payload p) h11 h14
  simpa [appendClock, initialBank, payload, List.map_append,
    fields_append_one, List.append_assoc] using h

theorem preserves_context {m k : Nat} (foreign : Stack → List Bool)
    (ps : List (Fin m × Fin k)) (p : Fin m × Fin k)
    (h11 : foreign 11 = []) (h14 : foreign 14 = [])
    (j : Stack) (hj : j ≠ 5 ∧ j ≠ 9 ∧ j ≠ 11 ∧ j ≠ 14) :
    (run (appendClock ps p)
      ⟨some .saveScan, ((), none), initialBank foreign ps p⟩).stk j =
    foreign j := by
  rw [physical_append foreign ps p h11 h14]
  simp [initialBank, CurrentAdditive.CodeDAppendAtEnd15.initialBank,
    hj.1, hj.2.1]

#print axioms physical_append
#print axioms preserves_context

end CurrentAdditive.GaussPivotFieldsAppend
