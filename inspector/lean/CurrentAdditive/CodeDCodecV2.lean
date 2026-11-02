import CurrentAdditive.CodeDCodec
import EthInapproximability.CurrentPaper.SourceListEncoding

/-!
Physical-list ABI revision. The original marker-field `CodeDCodec` is frozen
for provenance. Here only variable-length arrays change to the inherited
`SourceListEncoding` count and length-prefix format, for which a physical
iterator already exists. Fixed Bank2/Bank3 records and the RawRat layout
remain the exact original codec.
-/

namespace CurrentAdditive.CodeDCodecV2

open EthInapproximability.CurrentPaper

def encodeItems (items : List (List Bool)) : List Bool :=
  SourceListEncoding.encode items

def decodeItems (input : List Bool) : Option (List (List Bool)) :=
  SourceListEncoding.decode input

@[simp] theorem decodeItems_encodeItems (items : List (List Bool)) :
    decodeItems (encodeItems items) = some items := by
  exact SourceListEncoding.decode_encode items

theorem encodeItems_length (items : List (List Bool)) :
    (encodeItems items).length ≤
      3 * SourceListEncoding.totalLength items + 3 * items.length + 1 := by
  exact SourceListEncoding.encode_length items

#print axioms decodeItems_encodeItems
#print axioms encodeItems_length

end CurrentAdditive.CodeDCodecV2
