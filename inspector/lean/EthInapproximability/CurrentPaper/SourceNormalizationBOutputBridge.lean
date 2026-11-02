import EthInapproximability.CurrentPaper.SourceNormalizationNumericSource

/-! The actual BOT source output, not just a separately serialized raw graph. -/

namespace EthInapproximability.CurrentPaper.SourceNormalizationBOutputBridge

open SourceNormalizationNumeric SourceNormalizationNumericSource

theorem output_eq_serializeNormalized {k : ℕ}
    (B : EncodedETHSource.BOTReduction k)
    (f : EncodedCNF.Formula) (hf : f.Valid) (n : ℕ) :
    B.output f hf n =
      serializeNormalized
        (EncodedETHSource.rawGraph (B.reduce f) (B.valid f hf)) n := by
  rfl

theorem output_eq_numericGraph {k : ℕ}
    (B : EncodedETHSource.BOTReduction k)
    (f : EncodedCNF.Formula) (hf : f.Valid) (n : ℕ) :
    B.output f hf n = SourceNormalizationNumeric.numericGraph (B.reduce f) n := by
  rw [output_eq_serializeNormalized]
  exact serializeNormalized_raw (B.reduce f) (B.valid f hf) n

end EthInapproximability.CurrentPaper.SourceNormalizationBOutputBridge
