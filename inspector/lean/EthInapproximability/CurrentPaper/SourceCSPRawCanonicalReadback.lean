import EthInapproximability.CurrentPaper.SourceCSPCodec
import EthInapproximability.CurrentPaper.SourceCSPHeaderParse

/-! Literal canonical row bytes recovered from a successful raw parser. -/

namespace EthInapproximability.CurrentPaper.RawCanonicalReadback

/-- The raw row parser's success entails exact byte equality, not only an
equality of decoded row values. Numeric words are canonical because `readNat`
rejects noncanonical bit payloads. -/
theorem successful_rows_literal {n m a q : ℕ}
    (suffix : List Bool) (rows : Fin m → SourceCSPCodec.Row n a q)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    suffix = SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows := by
  have h := SourceCSPCodec.readFn_sound
    SourceCSPCodec.rowFields (SourceCSPCodec.readRow n a q)
    (fun h => SourceCSPCodec.readRow_sound h) hread
  simpa only [List.append_nil] using h.symm

/-- After a physical first-row reader consumes its head, the retained suffix
is exactly the canonical encoded tail of the same successfully parsed rows. -/
theorem first_rest_literal {n a q m : ℕ}
    (suffix rest : List Bool)
    (rows : Fin (m + 1) → SourceCSPCodec.Row n a q)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q)
      (m + 1) suffix = some (rows, []))
    (hphysical : suffix = SourceCSPCodec.rowFields (rows 0) ++ rest) :
    rest = SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin m => rows j.succ) := by
  have hcanonical := successful_rows_literal suffix rows hread
  rw [SourceCSPCodec.fnFields_succ] at hcanonical
  rw [hphysical] at hcanonical
  exact List.append_cancel_left hcanonical

/-- The exact typed-row vector occupies at least one bit per row in the
literal accepted suffix; the accepted row count is consequently bounded by
both retained suffix length and whole raw input length. -/
theorem successful_rows_length_bounds {n m q : ℕ}
    (input suffix : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hinput : input = SourceCSPHeaderParse.header n m 2 q ++ suffix)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n 2 q) m suffix =
      some (rows, [])) :
    m ≤ suffix.length ∧ m ≤ input.length := by
  have hrow : ∀ row : SourceCSPCodec.Row n 2 q,
      1 ≤ (SourceCSPCodec.rowFields row).length := by
    intro row
    have h := SourceCSPCodec.rowFields_length_lower row
    have hp : 1 ≤ q + 2 ^ q := by
      have hp' : 0 < 2 ^ q := pow_pos (by omega) _
      omega
    omega
  have hm := SourceCSPCodec.fnFields_length_lower
    SourceCSPCodec.rowFields 1 hrow rows
  have hs := successful_rows_literal suffix rows hread
  have hmS : m ≤ suffix.length := by
    rw [hs]
    simpa using hm
  constructor
  · exact hmS
  · have hlen : suffix.length ≤ input.length := by
      simp [hinput]
    exact hmS.trans hlen


end EthInapproximability.CurrentPaper.RawCanonicalReadback
