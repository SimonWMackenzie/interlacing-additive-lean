import CurrentAdditive.GaussWordGridTraversal
import CurrentAdditive.GaussTypedGetterBridge
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-! Exact byte identities for the two-level word traversal. These lemmas
identify the outputs that physical cell/row framing must produce; they do not
preload a count header or replace a physical framing run. -/

namespace CurrentAdditive.GaussNestedFraming64

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open GaussWordGridTraversal

def frameWord (word : List Bool) : List Bool :=
  SourceListMachineWriter.result true word

def headerWord (n : Nat) : List Bool :=
  SourceListMachineWriter.result false (List.replicate n true)

theorem headerWord_exact (n : Nat) : headerWord n = natField n := by
  simp [headerWord,SourceListMachineWriter.result]

theorem fields_eq_flatMap (words : List (List Bool)) :
    SourceListEncoding.fields words = words.flatMap frameWord := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      simp [SourceListEncoding.fields,frameWord,SourceListMachineWriter.result,ih,
        List.append_assoc]

def rawAt {m k : Nat} (B : Fin m → Fin k → ℚ) (x y : Nat) : List Bool :=
  if hx : x < m then
    if hy : y < k then CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B ⟨x,hx⟩ ⟨y,hy⟩))
    else []
  else []

def framedCell {m k : Nat} (B : Fin m → Fin k → ℚ) (x y : Nat) : List Bool :=
  frameWord (rawAt B x y)

def rowSpec {m k : Nat} (B : Fin m → Fin k → ℚ) (x : Nat) : List Bool :=
  if hx : x < m then
    SourceListEncoding.encode (GaussTypedGetterBridge.cellWords B ⟨x,hx⟩)
  else []

theorem rawAt_finite {m k : Nat} (B : Fin m → Fin k → ℚ)
    (i : Fin m) (j : Fin k) :
    rawAt B i.val j.val = CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j)) := by
  simp [rawAt,i.isLt,j.isLt]

theorem rowTraversal_exact {m k : Nat} (B : Fin m → Fin k → ℚ) (i : Fin m) :
    headerWord k ++ rowWord (framedCell B) i.val 0 k = rowSpec B i.val := by
  have h := rowWord_finite (framedCell B) i.val 0 k
    (fun j => frameWord (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j))))
    (by intro j; simpa [framedCell] using congrArg frameWord (rawAt_finite B i j))
  rw [h]
  simp [rowSpec,i.isLt,SourceListEncoding.encode,headerWord_exact,
    GaussTypedGetterBridge.cellWords,fields_eq_flatMap,List.flatMap_map,Function.comp_def]

theorem matrixTraversal_exact {m k : Nat} (B : Fin m → Fin k → ℚ) :
    headerWord m ++
      tableWord (fun x _ => frameWord (rowSpec B x)) 1 0 m =
      GaussPhysical.encodeTypedMatrix B := by
  have h := tableWord_finite (fun x _ => frameWord (rowSpec B x)) 1 0 m 1 rfl
    (fun i _ => frameWord (rowSpec B i.val)) (by intro i j; simp)
  rw [h,GaussTypedGetterBridge.encodeTypedMatrix_eq]
  simp [SourceListEncoding.encode,headerWord_exact,
    GaussTypedGetterBridge.rowWords,fields_eq_flatMap,List.flatMap_map,
    rowSpec,Function.comp_def,List.finRange_succ]

#print axioms rowTraversal_exact
#print axioms matrixTraversal_exact

end CurrentAdditive.GaussNestedFraming64
