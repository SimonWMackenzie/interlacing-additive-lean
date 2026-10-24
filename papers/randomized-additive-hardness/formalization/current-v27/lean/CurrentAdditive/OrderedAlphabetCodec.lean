import CurrentAdditive.ExecutableSources

/-! An explicit code for the *actual ordered* alphabet table.  Repeated table
entries stay repeated; a symbol is named by its first table position. -/

namespace CurrentAdditive.OrderedAlphabetCodec

open Paper2 CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.SequentialCode CurrentAdditive.SequentialSourceCode

variable {Y : Type} [Fintype Y] [DecidableEq Y]

def symbols (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) : List Y :=
  (table.entries.map Prod.fst).toList

def encode (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (y : Y) : Nat := (symbols μ table).idxOf y

def decode (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (n : Nat) : Option Y := (symbols μ table)[n]?

theorem encode_lt (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) (y : Y) :
    encode μ table y < table.entries.size := by
  simpa [encode, symbols] using List.idxOf_lt_length_of_mem (table.covers y)

theorem decode_encode (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) (y : Y) :
    decode μ table (encode μ table y) = some y := by
  simpa [decode, encode, symbols] using
    List.getElem?_idxOf (table.covers y)

theorem encode_injective (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) : Function.Injective (encode μ table) := by
  intro x y h
  exact (List.idxOf_inj (table.covers x)).mp h

def numericEntries (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) : Array (Nat × ℚ) :=
  table.entries.map (fun e => (encode μ table e.1, e.2))

theorem numericEntries_size (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    (numericEntries μ table).size = table.entries.size := by
  simp [numericEntries]

theorem numericEntries_at (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) (i : Fin table.entries.size) :
    (numericEntries μ table)[i.val]? =
      some (encode μ table table.entries[i].1, table.entries[i].2) := by
  simp [numericEntries]

theorem numericEntries_positive (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    SourcePositive (numericEntries μ table) := by
  simpa [SourcePositive, numericEntries, Array.all_map, Function.comp_def]
    using table.positive

#print axioms encode_injective
#print axioms decode_encode
#print axioms numericEntries_positive

end CurrentAdditive.OrderedAlphabetCodec
