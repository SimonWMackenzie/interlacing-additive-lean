import CurrentAdditive.DeterministicETHEncodedTable

namespace CurrentAdditive.V42EncodedCostEvent
open Workspace.Types.CommComplexity
open EthInapproximability.CurrentPaper EncodedCommunication

/-- A semantic event on the very word emitted by the table printer. -/
def HasCost (C : ℕ) (word : List Bool) : Prop :=
  ∃ out, decodeInstance word=some out ∧
    D (ProtocolVerifier.tableGame out.rows out.cols out.table)=C

theorem hasCost_encode {m : ℕ} (hm : 0 < m) (B C : ℕ)
    (F : Fin m → Fin m → Bool) :
    HasCost C (encodeInstance ⟨m,m,B,MatrixMaterialization.rowMajor F⟩) ↔ D F=C := by
  have hdecode := decode_encode ⟨m,m,B,MatrixMaterialization.rowMajor F⟩
    ⟨hm,hm,MatrixMaterialization.rowMajor_length F⟩
  constructor
  · rintro ⟨out,hd,hcost⟩
    rw [hdecode] at hd
    cases Option.some.inj hd
    simpa only [DeterministicETHEncodedTable.tableGame_rowMajor] using hcost
  · intro hc
    refine ⟨⟨m,m,B,MatrixMaterialization.rowMajor F⟩,hdecode,?_⟩
    simpa only [DeterministicETHEncodedTable.tableGame_rowMajor] using hc

#print axioms hasCost_encode

end CurrentAdditive.V42EncodedCostEvent
