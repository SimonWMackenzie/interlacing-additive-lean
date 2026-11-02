import CurrentAdditive.V40DeterministicSourcePack
import CurrentAdditive.V40ActualSourceGap

/-! Same actual current finite table and public threshold for the full
literal CNF language. Polynomial reduction is asserted only after its
concrete physical graph constructor has been composed. -/
namespace CurrentAdditive.V40DeterministicFixedGap
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open EncodedCommunication EncodedComplexity EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite V39GeneratedConstruction V39CurrentSourceJoin
open Workspace.Types.CommComplexity
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def formula := V40DeterministicSourcePack.fixedFormula

def instanceWord (k : ℕ) (w : List Bool) : Instance :=
  let Φ:=formula w
  let R:=ethRun D B Φ k
  ⟨R.rows,R.cols,ethThreshold D B Φ k,MatrixMaterialization.rowMajor R.entry⟩

theorem valid (k : ℕ) (w : List Bool) : (instanceWord D B k w).Valid := by
  dsimp only [instanceWord]
  exact ⟨StoredMatrix.rows_pos _,StoredMatrix.cols_pos _,MatrixMaterialization.rowMajor_length _⟩

theorem table_eq (k : ℕ) (w : List Bool) :
    ProtocolVerifier.tableGame (instanceWord D B k w).rows (instanceWord D B k w).cols
      (instanceWord D B k w).table=(ethRun D B (formula w) k).entry := by
  funext i j
  simp only [instanceWord,ProtocolVerifier.tableGame,ProtocolVerifier.tableEntry,
    MatrixMaterialization.rowMajor_entry,Option.getD_some]

theorem gap (k : ℕ) (w : List Bool) :
    (w∈EncodedCNF.Language → Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame
      (instanceWord D B k w).rows (instanceWord D B k w).cols (instanceWord D B k w).table)≤
        (instanceWord D B k w).threshold) ∧
    (w∉EncodedCNF.Language → (instanceWord D B k w).threshold+k≤
      Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame (instanceWord D B k w).rows
        (instanceWord D B k w).cols (instanceWord D B k w).table)) := by
  rw [table_eq]
  have hs:=V40DeterministicSourcePack.fixed_front_sat_iff w
  exact ⟨fun hy => ethRun_yes D B (formula w) k (hs.2 hy),
    fun hn => (ethRun_no D B (formula w) k (fun hy => hn (hs.1 hy))).ge⟩

theorem encoded_membership (I : Instance) (hi : I.Valid) :
    encodeInstance I ∈ EncodedCommunication.Language ↔
      Workspace.Types.CommComplexity.D (ProtocolVerifier.tableGame I.rows I.cols I.table) ≤ I.threshold := by
  constructor
  · rintro ⟨J,hj,hcost⟩
    rw [decode_encode I hi] at hj
    cases Option.some.inj hj
    exact hcost
  · intro hc
    exact ⟨I,decode_encode I hi,hc⟩

/-- An honest intermediate reduction wrapper. The physical polynomial
compiler premise remains pending until the whole constructor is supplied. -/
theorem reduction_of_physical_polytime (k : ℕ) (hk : 1≤k)
    (hphysical : BitMachine.Polytime (fun w => encodeInstance (instanceWord D B k w))) :
    Reduces EncodedCNF.Language EncodedCommunication.Language := by
  refine ⟨fun w => encodeInstance (instanceWord D B k w),hphysical,?_⟩
  intro w
  rw [encoded_membership (instanceWord D B k w) (valid D B k w)]
  constructor
  · exact (gap D B k w).1
  · intro hcost
    by_contra hn
    have hno:=(gap D B k w).2 hn
    omega

#print axioms gap
#print axioms reduction_of_physical_polytime
end
end CurrentAdditive.V40DeterministicFixedGap
