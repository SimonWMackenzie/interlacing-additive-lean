import CurrentAdditive.GaussPivotFieldsAppend
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-!
Physical completion of the V2 pivot-list packet from its two prepared parts.
The count field is printed by the inherited finite machine from the updated
unary row cursor, and the fixed Fin-15 append controller joins that field to
the complete body.  The caller must route the two resulting words to banks
9 and 5; this module does not silently treat the routing as a zero-cost step.
-/

namespace CurrentAdditive.GaussPivotPacketJoin

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.GaussControlTrace
open CurrentAdditive.CodeDAppendAtEnd15
open Turing BitMachineEncoding

def countUnary {m k : Nat} (ps : List (Fin m × Fin k)) : List Bool :=
  List.replicate ps.length true

def header {m k : Nat} (ps : List (Fin m × Fin k)) : List Bool :=
  natField ps.length

theorem physical_header {m k : Nat} (ps : List (Fin m × Fin k)) :
    (SourceListMachineWriter.framingMachine false).OutputsWithin
      (countUnary ps) (header ps)
      ((UnaryBinaryEncoding.coefficient + 7) *
          ((countUnary ps).length + 1)^2) := by
  simpa [countUnary, header, SourceListMachineWriter.result] using
    SourceListMachineWriter.outputs false (List.replicate ps.length true)

theorem header_from_cursor {m k : Nat} (s : State m k)
    (hcount : s.r = s.pivots.length) :
    (SourceListMachineWriter.framingMachine false).OutputsWithin
      (List.replicate s.r true) (natField s.pivots.length)
      ((UnaryBinaryEncoding.coefficient + 7) * (s.r + 1)^2) := by
  simpa [countUnary, header, hcount] using physical_header s.pivots

def body {m k : Nat} (ps : List (Fin m × Fin k)) : List Bool :=
  SourceListEncoding.fields (ps.map pivotPacket)

def joinBank {m k : Nat} (foreign : Stack → List Bool)
    (ps : List (Fin m × Fin k)) : Stack → List Bool :=
  CurrentAdditive.CodeDAppendAtEnd15.initialBank foreign
    (header ps) (body ps)

def joinClock {m k : Nat} (ps : List (Fin m × Fin k)) : Nat :=
  4 * (header ps).length + 2 * (body ps).length + 6

theorem physical_join {m k : Nat} (foreign : Stack → List Bool)
    (ps : List (Fin m × Fin k))
    (h11 : foreign 11 = []) (h14 : foreign 14 = []) :
    run (joinClock ps)
      ⟨some .saveScan, ((), none), joinBank foreign ps⟩ =
    ⟨some .done, ((), none),
      Function.update
        (Function.update
          (Function.update (joinBank foreign ps) 9 []) 5 []) 9
        (pivotsPacket ps)⟩ := by
  have h := CurrentAdditive.CodeDAppendAtEnd15.append_run foreign
    (header ps) (body ps) h11 h14
  simpa [joinClock, joinBank, header, body, pivotsPacket,
    SourceListEncoding.encode] using h

theorem physical_join_preserves_context {m k : Nat}
    (foreign : Stack → List Bool) (ps : List (Fin m × Fin k))
    (h11 : foreign 11 = []) (h14 : foreign 14 = [])
    (j : Stack) (hj : j ≠ 5 ∧ j ≠ 9 ∧ j ≠ 11 ∧ j ≠ 14) :
    (run (joinClock ps)
      ⟨some .saveScan, ((), none), joinBank foreign ps⟩).stk j =
      foreign j := by
  rw [physical_join foreign ps h11 h14]
  simp [joinBank, CurrentAdditive.CodeDAppendAtEnd15.initialBank,
    hj.1, hj.2.1]

#print axioms physical_header
#print axioms header_from_cursor
#print axioms physical_join
#print axioms physical_join_preserves_context

end CurrentAdditive.GaussPivotPacketJoin
