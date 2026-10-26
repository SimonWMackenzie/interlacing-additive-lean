import CurrentAdditive.CodeDTargetV2
import CurrentAdditive.DynamicGetterOrdinary

/-! Ordered position labels are generated from a physical cursor, independently
of entry contents. The generic byte model also covers empty and malformed items. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
namespace CurrentAdditive.IndexedLawBytes
open EthInapproximability.CurrentPaper BitMachineBankCodec

def weightWord (word : List Bool) := BankFieldProjection.result (1 : Fin 2) word

def indexedWord (i : Nat) (word : List Bool) := encode ![i.bits,weightWord word]

def fieldsAt (xs : List (List Bool)) (i : Nat) :=
  (List.range i).flatMap (fun j => SourceListMachineWriter.result true (indexedWord j (xs[j]?.getD [])))

def state (xs : List (List Bool)) (i : Nat) :=
  encode ![SourceListEncoding.encode xs,List.replicate i true,fieldsAt xs i]

def outputItems (xs : List (List Bool)) :=
  (List.range xs.length).map (fun j => indexedWord j (xs[j]?.getD []))

def output (xs : List (List Bool)) := SourceListEncoding.encode (outputItems xs)

theorem fieldsAt_zero (xs : List (List Bool)) : fieldsAt xs 0=[] := rfl

theorem fieldsAt_succ (xs : List (List Bool)) (i : Nat) :
    fieldsAt xs (i+1)=fieldsAt xs i++SourceListMachineWriter.result true (indexedWord i (xs[i]?.getD [])) := by
  simp [fieldsAt,List.range_succ,List.flatMap_append]

theorem fieldsAt_succ_get (xs : List (List Bool)) (i : Nat) (hi : i<xs.length) :
    fieldsAt xs (i+1)=fieldsAt xs i++SourceListMachineWriter.result true (indexedWord i xs[i]) := by
  simpa [hi] using fieldsAt_succ xs i

theorem fieldsAt_final (xs : List (List Bool)) :
    fieldsAt xs xs.length=SourceListEncoding.fields (outputItems xs) := by
  have h (ys : List (List Bool)) :
      ys.flatMap (SourceListMachineWriter.result true)=SourceListEncoding.fields ys := by
    induction ys with
    | nil => rfl
    | cons y ys ih => simp [SourceListMachineWriter.result,SourceListEncoding.fields,ih]
  rw [← h,outputItems,List.flatMap_map]
  rfl

theorem outputItems_length (xs : List (List Bool)) : (outputItems xs).length=xs.length := by
  simp [outputItems]

end CurrentAdditive.IndexedLawBytes
