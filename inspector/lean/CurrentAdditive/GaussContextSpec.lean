import CurrentAdditive.GaussCellSpec
import CurrentAdditive.CodeDCodecV2

/-!
The exact context required by the physical Gauss clear-cell callback.  This
file specifies the indexed row-major work list and its V2 counted-list
encoding.  It does not assert that a machine has built the list.
-/

namespace CurrentAdditive.GaussListContext

open CurrentAdditive.CodeDCodec
open CurrentAdditive.GaussPhysical
open EthInapproximability.CurrentPaper

structure CellContext where
  pivotRow : Bool
  current : RawRat
  column : RawRat
  row : RawRat
  pivot : RawRat
  deriving DecidableEq

def packet (x : CellContext) : List Bool :=
  cellPacket x.pivotRow x.current x.column x.row x.pivot

def value (x : CellContext) : ℚ :=
  cellPacketValue x.pivotRow x.current x.column x.row x.pivot

def typedContext {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) : CellContext :=
  ⟨decide (i = r), rawOfRat (B i j), rawOfRat (B i c),
    rawOfRat (B r j), rawOfRat (B r c)⟩

def typedContexts {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) : List CellContext :=
  (List.finRange m).flatMap (fun i =>
    (List.finRange k).map (typedContext B r c i))

def encodedTypedContexts {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) : List Bool :=
  SourceListEncoding.encode ((typedContexts B r c).map packet)

theorem typedContext_value {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) (i : Fin m) (j : Fin k) :
    value (typedContext B r c i j) =
      CurrentAdditive.SequentialTotality.clearTyped B r c i j := by
  simp only [value, typedContext, cellPacketValue, rawOfRat_value]
  exact (clearTyped_cellFormula B r c i j).symm

theorem typedContexts_length {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) :
    (typedContexts B r c).length = m * k := by
  simp [typedContexts, List.length_flatMap]

theorem typedContexts_mem {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r : Fin m) (c : Fin k) (x : CellContext) :
    x ∈ typedContexts B r c ↔
      ∃ (i : Fin m) (j : Fin k), x = typedContext B r c i j := by
  simp [typedContexts, List.mem_flatMap, List.mem_map]
  aesop

@[simp] theorem decode_encodedTypedContexts {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k) :
    SourceListEncoding.decode (encodedTypedContexts B r c) =
      some ((typedContexts B r c).map packet) := by
  exact SourceListEncoding.decode_encode _

theorem typedContexts_output_values {m k : Nat}
    (B : Fin m → Fin k → ℚ) (r : Fin m) (c : Fin k) :
    (typedContexts B r c).map value =
      (List.finRange m).flatMap (fun i =>
        (List.finRange k).map
          (CurrentAdditive.SequentialTotality.clearTyped B r c i)) := by
  simp only [typedContexts, List.map_flatMap, List.map_map]
  congr 1
  funext i
  congr 1
  funext j
  exact typedContext_value B r c i j

#print axioms typedContext_value
#print axioms typedContexts_length
#print axioms typedContexts_mem
#print axioms typedContexts_output_values

end CurrentAdditive.GaussListContext
