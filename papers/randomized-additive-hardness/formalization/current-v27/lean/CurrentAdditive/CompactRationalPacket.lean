import CurrentAdditive.CompactRationalQuarticController
import CurrentAdditive.IndexedBaseLookup

/-! A single explicitly indexed finite matrix packet supplies its exact
rational row/column generator codes and its actual row-major entry lookup. -/

namespace Paper2.CompactRationalPacket

open Paper2.YaoMaterialization Paper2.RecursiveEntries
open Paper2.RecursiveLabelCodecScratch
open Paper2.CodedEntryEvaluatorScratch
open Paper2.CompactFinCodec

structure Packet (rows cols : ℕ) where
  table : SerializedTable rows cols
  rowLaw : PositiveRationalLaw (Fin rows)
  colLaw : PositiveRationalLaw (Fin cols)

def ofMatrix {rows cols : ℕ}
    (F : Fin rows → Fin cols → Bool)
    (μ : PositiveRationalLaw (Fin rows))
    (ν : PositiveRationalLaw (Fin cols)) : Packet rows cols where
  table := tabulate F
  rowLaw := μ
  colLaw := ν

def rowCode {rows cols : ℕ} (P : Packet rows cols) :
    Paper2.GeneratorCode.Code :=
  Paper2.CompactRationalRecursiveBase.rationalCode P.rowLaw

def colCode {rows cols : ℕ} (P : Packet rows cols) :
    Paper2.GeneratorCode.Code :=
  Paper2.CompactRationalRecursiveBase.rationalCode P.colLaw

def lookup {rows cols : ℕ} (P : Packet rows cols)
    (rowBits colBits : List Bool) : Option Bool := do
  let i ← decodeExact (codec rows) rowBits
  let j ← decodeExact (codec cols) colBits
  pure (P.table.matrix i j)

theorem lookup_encoded {rows cols : ℕ} (P : Packet rows cols)
    (i : Fin rows) (j : Fin cols) :
    lookup P ((codec rows).encode i) ((codec cols).encode j) =
      some (P.table.matrix i j) := by
  simp [lookup, decodeExact_encode]

theorem ofMatrix_lookup {rows cols : ℕ}
    (F : Fin rows → Fin cols → Bool)
    (μ : PositiveRationalLaw (Fin rows))
    (ν : PositiveRationalLaw (Fin cols))
    (i : Fin rows) (j : Fin cols) :
    lookup (ofMatrix F μ ν)
      ((codec rows).encode i) ((codec cols).encode j) = some (F i j) := by
  rw [lookup_encoded]
  exact congrArg some (tabulate_matrix F i j)

def recursiveLookup {nr nc : ℕ} {I : Type} {s q₁ q₂ w Q : ℕ}
    [NeZero s] (P : Packet nr nc)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin nr) (Fin nc) I s q₁ q₂ w Q)
    (ci : PrefixCodec I) (k : ℕ)
    (rowBits colBits : List Bool) : Option Bool :=
  codedEntry P.table.matrix activity ξ
    (codec nr) (codec nc) ci
    k rowBits colBits

theorem recursiveLookup_encoded {nr nc : ℕ} {I : Type}
    {s q₁ q₂ w Q : ℕ} [NeZero s]
    (P : Packet nr nc)
    (activity : I → Fin q₂ → Option (Fin s))
    (ξ : Tails (Fin nr) (Fin nc) I s q₁ q₂ w Q)
    (ci : PrefixCodec I) (k : ℕ)
    (x : Row (Fin nr) (Fin nc) I s q₁ q₂ w Q k)
    (y : Column (Fin nr) (Fin nc) I s q₁ q₂ w Q k) :
    recursiveLookup P activity ξ ci k
      ((carrierCodecs s q₁ q₂ w Q (codec nr) (codec nc) ci k).1.encode x)
      ((carrierCodecs s q₁ q₂ w Q (codec nr) (codec nc) ci k).2.encode y) =
      some (RecursiveEntries.matrix P.table.matrix activity ξ k x y) := by
  exact codedEntry_encoded P.table.matrix activity ξ
    (codec nr) (codec nc) ci k x y

#print axioms ofMatrix_lookup
#print axioms recursiveLookup_encoded

end Paper2.CompactRationalPacket
