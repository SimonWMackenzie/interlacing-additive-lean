import EthInapproximability.CurrentPaper.MatrixWeightedOrderWriter
import EthInapproximability.CurrentPaper.Iteration

/-! Alignment of the arithmetic weighted decoders with the paper's numbering. -/

namespace EthInapproximability.CurrentPaper.MatrixTableInterlaceWeightedNumbering

open WeightedDuplication

variable {Ω Δ : Type} [Fintype Ω] [Fintype Δ]

noncomputable def columnNumbering (eΩ : Ω ≃ Fin (Fintype.card Ω))
    (eΔ : Δ ≃ Fin (Fintype.card Δ)) (S : ℕ) :
    Iteration.Numbering (Columns Ω Δ S) :=
  (Iteration.Numbering.weighted
    (Iteration.Numbering.columnSupport
      ⟨Fintype.card Ω,eΩ.symm⟩ ⟨Fintype.card Δ,eΔ.symm⟩)
    columnWeight).prod (Iteration.Numbering.fin S)

/- The equality between `MatrixWeightedArithmetic.typedColumn` and this
paper numbering is a genuine remaining decoder theorem, not definitional
equality. The physical weighted-writer bridge must retain its literal typed
decoder table until that equality is proved; no semantic cast is asserted here. -/

end EthInapproximability.CurrentPaper.MatrixTableInterlaceWeightedNumbering
