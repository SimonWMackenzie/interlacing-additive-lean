import EthInapproximability.CurrentPaper.BitMachineBankSerialize

/-!
# Physical exact-instance header serialization from prepared binary fields

Source: frozen v8 `03-exact-hardness.tex` and the encoding fixed in
`EncodedCommunication.encodeInstance`. This fixed three-word Boolean-stack
program consumes canonical binary words for rows, columns and threshold, and
prepends their self-delimiting fields to a literal table already on the output
stack. Scalar computation, unary-to-binary conversion, and table construction
are separate stages.
-/

namespace EthInapproximability.CurrentPaper.MatrixInstanceEncoding

open Turing TM2.Stmt BitMachineEncoding EncodedCommunication BitMachineBankSerialize

abbrev Stack := BitMachineBankSerialize.Stack 3
abbrev Label := BitMachineBankSerialize.Label 3
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label (Option Bool)

/-- The three *prepared canonical binary* fields, in public encoding order. -/
def binaryBank (rows cols threshold : ℕ) : Bank 3 :=
  ![rows.bits, cols.bits, threshold.bits]

def initial (rows cols threshold : ℕ) (source table suffix : List Bool) : Config :=
  cfg (some (.emit 0)) none (binaryBank rows cols threshold)
    source [] (table ++ suffix)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label (Option Bool) :=
  BitMachineBankSerialize.program 3

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem bank_words (rows cols threshold : ℕ) :
    List.ofFn (binaryBank rows cols threshold) =
      [rows.bits, cols.bits, threshold.bits] := by
  rfl

theorem bank_encoding (rows cols threshold : ℕ) :
    BitMachineBankSerialize.encode
      (List.ofFn (binaryBank rows cols threshold)) =
      natField rows ++ natField cols ++ natField threshold := by
  rw [bank_words]
  simp [BitMachineBankSerialize.encode, natField]

/-- The literal output table and old suffix are retained. Only the three
header-word banks are consumed; the independent `source` bank survives exactly.
The bound charges every field marker, payload bit and final reversal. -/
theorem encode_run (rows cols threshold : ℕ)
    (source table suffix : List Bool) :
    ∃ (t : ℕ) (S' : Bank 3),
      t ≤ 2 * (natField rows ++ natField cols ++ natField threshold).length + 2 ∧
      run t (initial rows cols threshold source table suffix) =
        cfg none none S' source []
          (natField rows ++ natField cols ++ natField threshold ++ table ++ suffix) := by
  obtain ⟨t, S', ht, hr⟩ :=
    BitMachineBankSerialize.serialize (binaryBank rows cols threshold)
      source (table ++ suffix)
  refine ⟨t, S', ?_, ?_⟩
  · simpa only [bank_encoding] using ht
  · change BitMachineBankSerialize.run t
      (cfg (some (.emit 0)) none (binaryBank rows cols threshold)
        source [] (table ++ suffix)) = _
    rw [hr, bank_encoding]
    simp only [List.append_assoc]

/-- Exact match to the accepted encoded-instance word, with an arbitrary old
output suffix. This theorem does not assert that the instance is valid. -/
theorem encode_instance_run (i : Instance) (source suffix : List Bool) :
    ∃ (t : ℕ) (S' : Bank 3),
      t ≤ 2 * (encodeInstance i).length + 2 ∧
      run t (initial i.rows i.cols i.threshold source i.table suffix) =
        cfg none none S' source [] (encodeInstance i ++ suffix) := by
  obtain ⟨t, S', ht, hr⟩ :=
    encode_run i.rows i.cols i.threshold source i.table suffix
  refine ⟨t, S', ?_, ?_⟩
  · simp only [encodeInstance, List.length_append] at ht ⊢
    omega
  · simpa only [encodeInstance, List.append_assoc] using hr

end EthInapproximability.CurrentPaper.MatrixInstanceEncoding
