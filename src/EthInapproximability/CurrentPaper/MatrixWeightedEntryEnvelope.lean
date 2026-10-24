import EthInapproximability.CurrentPaper.MatrixWeightedEntryCost
import EthInapproximability.CurrentPaper.MatrixWeightedEntrySemantic

/-!
# Explicit size bounds for the protected-entry controller

Source: frozen replacement v8, Appendix B, `thm:paper-materialization`.
The entry controller's `commonCost` is a maximum of charged stage sums,
not a maximum of unknown halting times. This file bounds the concrete
intermediate bank lengths and arithmetic costs used by those sums.
-/

namespace EthInapproximability.CurrentPaper.MatrixWeightedEntryEnvelope

open MatrixWeightedEntryController MatrixWeightedEntryCost

/-- A uniform unary-word bound, including supplied table and order payloads.
Products created inside the evaluator are charged separately below. -/
def inputScale (d : Input) (x y : ℕ) : ℕ :=
  1 + x + y + d.uniform + d.fullBoundary + d.fullDivisor +
  d.diagonalDivisor + d.nb + d.stagePrefixRows + d.rx + d.nv +
  d.rawWidth + d.wordBase + d.cy + d.s + d.binBase +
  d.rowBoundary₁ + d.rowBoundary₂ + d.rowBoundary₃ +
  d.rowDivisor₀ + d.rowDivisor₁ + d.rowDivisor₂ + d.rowDivisor₃ +
  d.rawBits.length + d.orderBits.length

def BankBound {ι : Type*} (S : ι → List Bool) (K : ℕ) : Prop :=
  ∀ i, (S i).length ≤ K

theorem bankBound_update {ι : Type*} [DecidableEq ι]
    (S : ι → List Bool) (K : ℕ) (i : ι) (v : List Bool)
    (hS : BankBound S K) (hv : v.length ≤ K) :
    BankBound (Function.update S i v) K := by
  intro j
  by_cases h : j = i
  · subst j
    simpa using hv
  · simpa [Function.update_of_ne h] using hS j

theorem bankBound_mono {ι : Type*} (S : ι → List Bool)
    {K L : ℕ} (h : BankBound S K) (hKL : K ≤ L) :
    BankBound S L := by
  intro i
  exact (h i).trans hKL

theorem bankBound_sumElim {α β : Type*}
    (S : α → List Bool) (T : β → List Bool) (K : ℕ)
    (hS : BankBound S K) (hT : BankBound T K) :
    BankBound (Sum.elim S T) K := by
  intro i
  cases i with
  | inl i => exact hS i
  | inr i => exact hT i

theorem bankBound_embedded {α β : Type*}
    (ι : α ↪ β)
    (S : β → List Bool) (T : α → List Bool) (K : ℕ)
    (hS : BankBound S K) (hT : BankBound T K) :
    BankBound (BitMachineStackEmbedding.bank ι S T) K := by
  classical
  intro k
  by_cases h : ∃ i, ι i = k
  · obtain ⟨i, rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    exact hT i
  · rw [BitMachineStackEmbedding.bank_outside ι S T k h]
    exact hS k

theorem bankBound_persistent (d : Input) (x y : ℕ) :
    BankBound (persistentBank d) (inputScale d x y) := by
  intro k
  fin_cases k <;> simp [persistentBank, inputScale] <;> omega

theorem bankBound_cellBank (d : Input) (x y : ℕ) :
    BankBound (cellBank d x y []) (inputScale d x y) := by
  apply bankBound_sumElim
  · exact bankBound_persistent d x y
  · intro k
    fin_cases k <;> simp [inputScale] <;> omega

theorem bankBound_columnSeed (S : Fin 64 → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv K : ℕ)
    (hS : BankBound S K) (ho : ordinal ≤ K)
    (hu : uniform ≤ K) (hb : boundary ≤ K)
    (hf : fullDiv ≤ K) (hd : diagonalDiv ≤ K) :
    BankBound (MatrixWeightedColumnController.seed S ordinal uniform
      boundary fullDiv diagonalDiv) K := by
  intro k
  simp only [MatrixWeightedColumnController.seed]
  split_ifs <;> simp_all [BankBound]

theorem bankBound_columnFull (S : Fin 64 → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv K : ℕ)
    (hS : BankBound S K) (ho : ordinal ≤ K)
    (hu : uniform ≤ K) (hb : boundary ≤ K)
    (hf : fullDiv ≤ K) (hd : diagonalDiv ≤ K) :
    BankBound (MatrixWeightedColumnController.afterFull S ordinal uniform
      boundary fullDiv diagonalDiv) K := by
  have hs := bankBound_columnSeed S ordinal uniform boundary fullDiv
    diagonalDiv K hS ho hu hb hf hd
  have hdiv : ordinal / uniform ≤ K :=
    (Nat.div_le_self _ _).trans ho
  have hcut :
      (if ordinal / uniform < boundary then ordinal / uniform
       else ordinal / uniform - boundary) ≤ K := by
    split_ifs <;> omega
  apply bankBound_update
  · apply bankBound_update
    · exact bankBound_update _ _ 2 _ hs (by simpa using hdiv)
    · simpa using hcut
  · simpa using (Nat.div_le_self (ordinal / uniform) fullDiv).trans hdiv

theorem bankBound_columnDiagonal (S : Fin 64 → List Bool)
    (ordinal uniform boundary fullDiv diagonalDiv K : ℕ)
    (hS : BankBound S K) (ho : ordinal ≤ K)
    (hu : uniform ≤ K) (hb : boundary ≤ K)
    (hf : fullDiv ≤ K) (hd : diagonalDiv ≤ K) :
    BankBound (MatrixWeightedColumnController.afterDiagonal S ordinal uniform
      boundary fullDiv diagonalDiv) K := by
  have hs := bankBound_columnSeed S ordinal uniform boundary fullDiv
    diagonalDiv K hS ho hu hb hf hd
  have hdiv : ordinal / uniform ≤ K :=
    (Nat.div_le_self _ _).trans ho
  have hcut :
      (if ordinal / uniform < boundary then ordinal / uniform
       else ordinal / uniform - boundary) ≤ K := by
    split_ifs <;> omega
  apply bankBound_update
  · apply bankBound_update
    · exact bankBound_update _ _ 2 _ hs (by simpa using hdiv)
    · simpa using hcut
  · have h : (ordinal / uniform - boundary) / diagonalDiv ≤ K :=
      (Nat.div_le_self _ _).trans (Nat.sub_le _ _ |>.trans hdiv)
    simpa using h

theorem bankBound_rowSeed (S : Fin 64 → List Bool)
    (row b₁ b₂ b₃ c₀ c₁ c₂ c₃ K : ℕ)
    (hS : BankBound S K) (hr : row ≤ K)
    (hb₁ : b₁ ≤ K) (hb₂ : b₂ ≤ K) (hb₃ : b₃ ≤ K)
    (hc₀ : c₀ ≤ K) (hc₁ : c₁ ≤ K)
    (hc₂ : c₂ ≤ K) (hc₃ : c₃ ≤ K) :
    BankBound (MatrixWeightedRowController.seed S row b₁ b₂ b₃
      c₀ c₁ c₂ c₃) K := by
  intro k
  simp only [MatrixWeightedRowController.seed]
  split_ifs <;> simp_all [BankBound]

theorem bankBound_rowCut1 (S : Fin 64 → List Bool)
    (row b₁ b₂ b₃ c₀ c₁ c₂ c₃ K : ℕ)
    (hS : BankBound S K) (hr : row ≤ K) (hK : 1 ≤ K)
    (hb₁ : b₁ ≤ K) (hb₂ : b₂ ≤ K) (hb₃ : b₃ ≤ K)
    (hc₀ : c₀ ≤ K) (hc₁ : c₁ ≤ K)
    (hc₂ : c₂ ≤ K) (hc₃ : c₃ ≤ K) :
    BankBound (MatrixWeightedRowController.afterCut1 S row b₁ b₂ b₃
      c₀ c₁ c₂ c₃) K := by
  have hseed := bankBound_rowSeed S row b₁ b₂ b₃ c₀ c₁ c₂ c₃ K
    hS hr hb₁ hb₂ hb₃ hc₀ hc₁ hc₂ hc₃
  have hcopy : BankBound
      (MatrixWeightedRowController.afterCopy S row b₁ b₂ b₃
        c₀ c₁ c₂ c₃) K := by
    apply bankBound_update
    · exact bankBound_update _ _ 63 _ hseed (by simp; omega)
    · simpa using hr
  apply bankBound_update
  · exact hcopy
  · simp only [List.length_replicate]
    split_ifs <;> omega

theorem bankBound_rowCut2 (S : Fin 64 → List Bool)
    (row b₁ b₂ b₃ c₀ c₁ c₂ c₃ K : ℕ)
    (hS : BankBound S K) (hr : row ≤ K) (hK : 1 ≤ K)
    (hb₁ : b₁ ≤ K) (hb₂ : b₂ ≤ K) (hb₃ : b₃ ≤ K)
    (hc₀ : c₀ ≤ K) (hc₁ : c₁ ≤ K)
    (hc₂ : c₂ ≤ K) (hc₃ : c₃ ≤ K) :
    BankBound (MatrixWeightedRowController.afterCut2 S row b₁ b₂ b₃
      c₀ c₁ c₂ c₃) K := by
  have hcut1 := bankBound_rowCut1 S row b₁ b₂ b₃ c₀ c₁ c₂ c₃ K
    hS hr hK hb₁ hb₂ hb₃ hc₀ hc₁ hc₂ hc₃
  apply bankBound_update
  · exact hcut1
  · simp only [List.length_replicate]
    split_ifs <;> omega

theorem bankBound_rowCut3 (S : Fin 64 → List Bool)
    (row b₁ b₂ b₃ c₀ c₁ c₂ c₃ K : ℕ)
    (hS : BankBound S K) (hr : row ≤ K) (hK : 1 ≤ K)
    (hb₁ : b₁ ≤ K) (hb₂ : b₂ ≤ K) (hb₃ : b₃ ≤ K)
    (hc₀ : c₀ ≤ K) (hc₁ : c₁ ≤ K)
    (hc₂ : c₂ ≤ K) (hc₃ : c₃ ≤ K) :
    BankBound (MatrixWeightedRowController.afterCut3 S row b₁ b₂ b₃
      c₀ c₁ c₂ c₃) K := by
  have hseed := bankBound_rowSeed S row b₁ b₂ b₃ c₀ c₁ c₂ c₃ K
    hS hr hb₁ hb₂ hb₃ hc₀ hc₁ hc₂ hc₃
  have hcopy : BankBound
      (MatrixWeightedRowController.afterCopy S row b₁ b₂ b₃
        c₀ c₁ c₂ c₃) K := by
    apply bankBound_update
    · exact bankBound_update _ _ 63 _ hseed (by simp; omega)
    · simpa using hr
  have hcut1 : BankBound
      (MatrixWeightedRowController.afterCut1 S row b₁ b₂ b₃
        c₀ c₁ c₂ c₃) K := by
    apply bankBound_update
    · exact hcopy
    · simp only [List.length_replicate]
      split_ifs <;> omega
  have hcut2 : BankBound
      (MatrixWeightedRowController.afterCut2 S row b₁ b₂ b₃
        c₀ c₁ c₂ c₃) K := by
    apply bankBound_update
    · exact hcut1
    · simp only [List.length_replicate]
      split_ifs <;> omega
  apply bankBound_update
  · exact hcut2
  · simp only [List.length_replicate]
    split_ifs <;> omega

theorem bankBound_fullCore (d : Input) (x y : ℕ) :
    BankBound (fullCore d x y) (inputScale d x y) := by
  have hp := bankBound_persistent d x y
  have hrow : BankBound (rowCopiedBank d y) (inputScale d x y) := by
    apply bankBound_update
    · exact hp
    · simp only [List.length_replicate]
      dsimp [inputScale]
      omega
  apply bankBound_columnFull
  · exact hrow
  all_goals simp [inputScale]
  all_goals omega

theorem bankBound_diagonalCore (d : Input) (x y : ℕ) :
    BankBound (diagonalCore d x y)
      (inputScale d x y + diagonalColumnValue d x) := by
  let K := inputScale d x y + diagonalColumnValue d x
  have hp : BankBound (persistentBank d) K :=
    bankBound_mono _ (bankBound_persistent d x y) (by omega)
  have hrow : BankBound (rowCopiedBank d y) K := by
    apply bankBound_update
    · exact hp
    · simp only [List.length_replicate]
      dsimp [K, inputScale]
      omega
  have hc : BankBound
      (MatrixWeightedColumnController.afterDiagonal (rowCopiedBank d y)
        x d.uniform d.fullBoundary d.fullDivisor d.diagonalDivisor) K := by
    apply bankBound_columnDiagonal
    · exact hrow
    all_goals simp [K, inputScale]
    all_goals omega
  apply bankBound_update
  · exact hc
  · simpa only [diagonalColumnValue, List.length_replicate]
      using (show diagonalColumnValue d x ≤ K by dsimp [K]; omega)

theorem bankBound_rowResults (d : Input) (S : Fin 64 → List Bool)
    (x y K : ℕ) (hS : BankBound S K)
    (hscale : inputScale d x y ≤ K) :
    BankBound (fullRowResult d S y) K ∧
    BankBound (templateRowResult d S y) K ∧
    BankBound (vertexRowResult d S y) K ∧
    BankBound (auxiliaryRowResult d S y) K := by
  have hy : y ≤ K := by dsimp [inputScale] at hscale; omega
  have hK : 1 ≤ K := by dsimp [inputScale] at hscale; omega
  have hb₁ : d.rowBoundary₁ ≤ K := by dsimp [inputScale] at hscale; omega
  have hb₂ : d.rowBoundary₂ ≤ K := by dsimp [inputScale] at hscale; omega
  have hb₃ : d.rowBoundary₃ ≤ K := by dsimp [inputScale] at hscale; omega
  have hc₀ : d.rowDivisor₀ ≤ K := by dsimp [inputScale] at hscale; omega
  have hc₁ : d.rowDivisor₁ ≤ K := by dsimp [inputScale] at hscale; omega
  have hc₂ : d.rowDivisor₂ ≤ K := by dsimp [inputScale] at hscale; omega
  have hc₃ : d.rowDivisor₃ ≤ K := by dsimp [inputScale] at hscale; omega
  have hcut1 := bankBound_rowCut1 S y d.rowBoundary₁ d.rowBoundary₂
    d.rowBoundary₃ d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂
    d.rowDivisor₃ K hS hy hK hb₁ hb₂ hb₃ hc₀ hc₁ hc₂ hc₃
  have hcut2 := bankBound_rowCut2 S y d.rowBoundary₁ d.rowBoundary₂
    d.rowBoundary₃ d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂
    d.rowDivisor₃ K hS hy hK hb₁ hb₂ hb₃ hc₀ hc₁ hc₂ hc₃
  have hcut3 := bankBound_rowCut3 S y d.rowBoundary₁ d.rowBoundary₂
    d.rowBoundary₃ d.rowDivisor₀ d.rowDivisor₁ d.rowDivisor₂
    d.rowDivisor₃ K hS hy hK hb₁ hb₂ hb₃ hc₀ hc₁ hc₂ hc₃
  have hfull : fullLabel d y ≤ K := by
    exact (Nat.div_le_self _ _).trans hy
  have htemplate : templateLabel d y ≤ K := by
    unfold templateLabel
    exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans hy)
  have hvertex : vertexLabel d y ≤ K := by
    unfold vertexLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans hy))
  have haux : auxiliaryLabel d y ≤ K := by
    unfold auxiliaryLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans
        ((Nat.sub_le _ _).trans hy)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bankBound_update _ _ 54 _ hcut1 (by simpa using hfull)
  · exact bankBound_update _ _ 54 _ hcut2 (by simpa using htemplate)
  · exact bankBound_update _ _ 54 _ hcut3 (by simpa using hvertex)
  · exact bankBound_update _ _ 54 _ hcut3 (by simpa using haux)

theorem bankBound_writerExtra (x y K : ℕ)
    (hx : x ≤ K) (hy : y ≤ K) :
    BankBound (writerExtra x y []) K := by
  intro i
  fin_cases i <;> simp [writerExtra] <;> omega

theorem bankBound_afterRowClear (S : Stack → List Bool) (K : ℕ)
    (hS : BankBound S K) : BankBound (afterRowClear S) K := by
  exact bankBound_update _ _ _ _
    (bankBound_update _ _ _ _ hS (by simp)) (by simp)

theorem bankBound_rowBanks (d : Input) (x y K : ℕ)
    (S : Fin 64 → List Bool) (hS : BankBound S K)
    (hscale : inputScale d x y ≤ K) :
    BankBound (Sum.elim (fullRowResult d S y) (writerExtra x y [])) K ∧
    BankBound (Sum.elim (templateRowResult d S y) (writerExtra x y [])) K ∧
    BankBound (Sum.elim (vertexRowResult d S y) (writerExtra x y [])) K ∧
    BankBound (Sum.elim (auxiliaryRowResult d S y) (writerExtra x y [])) K := by
  have hx : x ≤ K := by dsimp [inputScale] at hscale; omega
  have hy : y ≤ K := by dsimp [inputScale] at hscale; omega
  obtain ⟨h₀,h₁,h₂,h₃⟩ := bankBound_rowResults d S x y K hS hscale
  have he := bankBound_writerExtra x y K hx hy
  exact ⟨bankBound_sumElim _ _ _ h₀ he,
    bankBound_sumElim _ _ _ h₁ he,
    bankBound_sumElim _ _ _ h₂ he,
    bankBound_sumElim _ _ _ h₃ he⟩

theorem bankBound_directPre (K : ℕ) (S : Stack → List Bool) (label : ℕ)
    (hS : BankBound S K) (hl : label ≤ K) :
    BankBound
      (Function.update (afterRowClear S) (.inl 25)
        (List.replicate label true)) K := by
  exact bankBound_update _ _ _ _ (bankBound_afterRowClear S K hS)
    (by simpa using hl)

theorem bankBound_directPreLookups (d : Input) (x y : ℕ) :
    let K := inputScale d x y + diagonalColumnValue d x
    BankBound (fullFullPreLookup d x y) K ∧
    BankBound (fullTemplatePreLookup d x y) K ∧
    BankBound (diagonalFullPreLookup d x y) K ∧
    BankBound (diagonalTemplatePreLookup d x y) K := by
  let K := inputScale d x y + diagonalColumnValue d x
  have hscale : inputScale d x y ≤ K := by dsimp [K]; omega
  have hfull : BankBound (fullCore d x y) K :=
    bankBound_mono _ (bankBound_fullCore d x y) hscale
  have hdiag : BankBound (diagonalCore d x y) K :=
    bankBound_diagonalCore d x y
  obtain ⟨hf₀,hf₁,_,_⟩ := bankBound_rowBanks d x y K
    (fullCore d x y) hfull hscale
  obtain ⟨hd₀,hd₁,_,_⟩ := bankBound_rowBanks d x y K
    (diagonalCore d x y) hdiag hscale
  have hy : y ≤ K := by dsimp [K, inputScale]; omega
  have hl₀ : fullLabel d y ≤ K :=
    (Nat.div_le_self _ _).trans hy
  have hl₁ : templateLabel d y ≤ K := by
    unfold templateLabel
    exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans hy)
  exact ⟨bankBound_directPre K _ _ hf₀ hl₀,
    bankBound_directPre K _ _ hf₁ hl₁,
    bankBound_directPre K _ _ hd₀ hl₀,
    bankBound_directPre K _ _ hd₁ hl₁⟩

theorem bankBound_orderTerminal (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv + d.nb)) (label x y K : ℕ) (aux : Bool)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hl : label ≤ y)
    (hscale : inputScale d x y + (order j).val*d.rx ≤ K) :
    BankBound
      (MatrixWeightedRowOrderMachineRun.terminalBank label d.rx d.nv
        d.stagePrefixRows (MatrixWeightedRowOrderLookup.orderWord order)
        [] aux j.val (order j).val) K := by
  intro i
  have hj : j.val < d.nv + d.nb := j.isLt
  have hmod : label % d.rx ≤ y :=
    (Nat.mod_le _ _).trans hl
  have hdiv : label / d.rx ≤ y :=
    (Nat.div_le_self _ _).trans hl
  dsimp [inputScale] at hscale
  rw [horder] at hscale
  cases aux <;> fin_cases i <;>
    simp [MatrixWeightedRowOrderMachineRun.terminalBank] <;>
    omega

theorem bankBound_orderPreLookup (d : Input)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv + d.nb)) (label x y K : ℕ) (aux : Bool)
    (B : Stack → List Bool) (hB : BankBound B K)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hl : label ≤ y)
    (hscale : inputScale d x y + (order j).val*d.rx ≤ K) :
    BankBound (orderPreLookup d order j label aux B) K := by
  unfold orderPreLookup
  apply bankBound_embedded
  · exact hB
  · exact bankBound_orderTerminal d order j label x y K aux
      horder hl hscale

theorem bankBound_orderedPreLookups (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv + d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order) :
    let K := inputScale d x y + diagonalColumnValue d x +
      (order j).val*d.rx
    BankBound (fullVertexPreLookup d x y order j) K ∧
    BankBound (fullAuxiliaryPreLookup d x y order j) K ∧
    BankBound (diagonalVertexPreLookup d x y order j) K ∧
    BankBound (diagonalAuxiliaryPreLookup d x y order j) K := by
  let K := inputScale d x y + diagonalColumnValue d x +
    (order j).val*d.rx
  have hscale : inputScale d x y ≤ K := by dsimp [K]; omega
  have hterminal : inputScale d x y + (order j).val*d.rx ≤ K := by
    dsimp [K]
    omega
  have hfull : BankBound (fullCore d x y) K :=
    bankBound_mono _ (bankBound_fullCore d x y) hscale
  have hdiag : BankBound (diagonalCore d x y) K :=
    bankBound_mono _ (bankBound_diagonalCore d x y) (by dsimp [K]; omega)
  obtain ⟨_,_,hf₂,hf₃⟩ := bankBound_rowBanks d x y K
    (fullCore d x y) hfull hscale
  obtain ⟨_,_,hd₂,hd₃⟩ := bankBound_rowBanks d x y K
    (diagonalCore d x y) hdiag hscale
  have hy : y ≤ K := by dsimp [K, inputScale]; omega
  have hv : vertexLabel d y ≤ y := by
    unfold vertexLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have ha : auxiliaryLabel d y ≤ y := by
    unfold auxiliaryLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans
        (Nat.sub_le _ _)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact bankBound_orderPreLookup d order j (vertexLabel d y) x y K
      false _ (bankBound_afterRowClear _ K hf₂) horder hv hterminal
  · exact bankBound_orderPreLookup d order j (auxiliaryLabel d y) x y K
      true _ (bankBound_afterRowClear _ K hf₃) horder ha hterminal
  · exact bankBound_orderPreLookup d order j (vertexLabel d y) x y K
      false _ (bankBound_afterRowClear _ K hd₂) horder hv hterminal
  · exact bankBound_orderPreLookup d order j (auxiliaryLabel d y) x y K
      true _ (bankBound_afterRowClear _ K hd₃) horder ha hterminal

theorem workLength_le_bankBound (S : Stack → List Bool) (K : ℕ)
    (hS : BankBound S K) : workLength S ≤ 41*K :=
  workLength_le_max S K (fun i => hS (workSlot i))

theorem direct_workLengths_le (d : Input) (x y : ℕ) :
    let K := inputScale d x y + diagonalColumnValue d x
    workLength (fullFullPreLookup d x y) ≤ 41*K ∧
    workLength (fullTemplatePreLookup d x y) ≤ 41*K ∧
    workLength (diagonalFullPreLookup d x y) ≤ 41*K ∧
    workLength (diagonalTemplatePreLookup d x y) ≤ 41*K := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := bankBound_directPreLookups d x y
  exact ⟨workLength_le_bankBound _ _ h₀,
    workLength_le_bankBound _ _ h₁,
    workLength_le_bankBound _ _ h₂,
    workLength_le_bankBound _ _ h₃⟩

theorem ordered_workLengths_le (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv + d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order) :
    let K := inputScale d x y + diagonalColumnValue d x +
      (order j).val*d.rx
    workLength (fullVertexPreLookup d x y order j) ≤ 41*K ∧
    workLength (fullAuxiliaryPreLookup d x y order j) ≤ 41*K ∧
    workLength (diagonalVertexPreLookup d x y order j) ≤ 41*K ∧
    workLength (diagonalAuxiliaryPreLookup d x y order j) ≤ 41*K := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ :=
    bankBound_orderedPreLookups d x y order j horder
  exact ⟨workLength_le_bankBound _ _ h₀,
    workLength_le_bankBound _ _ h₁,
    workLength_le_bankBound _ _ h₂,
    workLength_le_bankBound _ _ h₃⟩

/-- A numerical scale for the diagonal machine's five unary inputs and its
two variable power words. The powers are proved to lie below the physical
raw-table width for the actual input, rather than treated as free constants. -/
def diagonalScale (code wordBase cy s binBase : ℕ) : ℕ :=
  1 + code + wordBase + cy + s + binBase +
    cy ^ (s+1) + binBase ^ s

theorem diagonalScale_pos (code wordBase cy s binBase : ℕ) :
    1 ≤ diagonalScale code wordBase cy s binBase := by
  dsimp [diagonalScale]
  omega

theorem powerBound_le_diagonalScale (base exp M : ℕ)
    (hM : 1 ≤ M) (hb : base ≤ M) (he : exp + 1 ≤ 2*M)
    (hp : base^exp + 1 ≤ 2*M) :
    MatrixWeightedPower.powerBound base exp ≤ 100*M^3 := by
  have h := MatrixWeightedPower.powerBound_polynomial base exp
  have hpoly : (exp+1) *
      (3 * (base^exp+1) * base + 5 * (base^exp+1) + 7) ≤
      (2*M) * (3*(2*M)*M + 5*(2*M)+7) := by
    gcongr
  have hM2 : M ≤ M^2 := by nlinarith [sq_nonneg (M:ℤ)]
  have hM3 : M^2 ≤ M^3 := by
    nlinarith [Nat.mul_le_mul_left (M^2) hM]
  have hlast : (2*M) * (3*(2*M)*M + 5*(2*M)+7) ≤ 100*M^3 := by
    nlinarith
  exact h.trans (hpoly.trans hlast)

theorem tailPowerBound_le_scale (code wordBase cy s binBase : ℕ) :
    MatrixWeightedPower.powerBound cy (s+1) ≤
      100*(diagonalScale code wordBase cy s binBase)^3 := by
  let M := diagonalScale code wordBase cy s binBase
  apply powerBound_le_diagonalScale
  · exact diagonalScale_pos _ _ _ _ _
  · dsimp [M, diagonalScale]; omega
  · dsimp [M, diagonalScale]; omega
  · dsimp [M, diagonalScale]; omega

theorem binPowerBound_le_scale (code wordBase cy s binBase : ℕ) :
    MatrixWeightedPower.powerBound binBase s ≤
      100*(diagonalScale code wordBase cy s binBase)^3 := by
  let M := diagonalScale code wordBase cy s binBase
  apply powerBound_le_diagonalScale
  · exact diagonalScale_pos _ _ _ _ _
  · dsimp [M, diagonalScale]; omega
  · dsimp [M, diagonalScale]; omega
  · dsimp [M, diagonalScale]; omega

theorem tailBound_le_scale (code wordBase cy s binBase : ℕ) :
    MatrixWeightedDiagonalMachine.tailBound code wordBase cy s ≤
      200*(diagonalScale code wordBase cy s binBase)^3 := by
  let M := diagonalScale code wordBase cy s binBase
  have hM : 1 ≤ M := diagonalScale_pos _ _ _ _ _
  have hM3 : M ≤ M^3 := by
    nlinarith [Nat.mul_le_mul_left (M^2) hM]
  have hd : code ≤ M := by dsimp [M, diagonalScale]; omega
  have hw : wordBase ≤ M := by dsimp [M, diagonalScale]; omega
  have hs : s ≤ M := by dsimp [M, diagonalScale]; omega
  have hcy : cy^(s+1) ≤ M := by dsimp [M, diagonalScale]; omega
  have hword : MatrixWeightedDiagonalMachine.word code wordBase ≤ M := by
    exact (Nat.mod_le _ _).trans hd
  have hpower := tailPowerBound_le_scale code wordBase cy s binBase
  change MatrixWeightedPower.powerBound cy (s+1) ≤ 100*M^3 at hpower
  have hdiv₀ := MatrixUnaryDivision.totalTime_bound code wordBase
  have hdiv₁ := MatrixUnaryDivision.totalTime_bound
    (MatrixWeightedDiagonalMachine.word code wordBase) (cy^(s+1))
  have hquot₀ := Nat.div_le_self code wordBase
  have hquot₁ := Nat.div_le_self
    (MatrixWeightedDiagonalMachine.word code wordBase) (cy^(s+1))
  dsimp [MatrixWeightedDiagonalMachine.tailBound,
    MatrixWeightedDiagonalMachine.tailPowerValue] at *
  change (2*code+2) +
    (1+MatrixUnaryDivision.totalTime code wordBase) +
    (code/wordBase+1) + (2*s+2) + 2 +
    MatrixWeightedPower.powerBound cy (s+1) + 1 +
    (2*MatrixWeightedDiagonalMachine.word code wordBase+2) + 1 +
    MatrixUnaryDivision.totalTime
      (MatrixWeightedDiagonalMachine.word code wordBase) (cy^(s+1)) +
    (MatrixWeightedDiagonalMachine.word code wordBase/(cy^(s+1))+1) +
    (cy^(s+1)+1) ≤ 200*M^3
  omega

theorem geomBound_le_scale (code wordBase cy s binBase : ℕ) :
    MatrixWeightedDiagonalMachine.geomBound binBase s ≤
      200*(diagonalScale code wordBase cy s binBase)^3 := by
  let M := diagonalScale code wordBase cy s binBase
  have hM : 1 ≤ M := diagonalScale_pos _ _ _ _ _
  have hM3 : M ≤ M^3 := by
    nlinarith [Nat.mul_le_mul_left (M^2) hM]
  have hs : s ≤ M := by dsimp [M, diagonalScale]; omega
  have hb : binBase ≤ M := by dsimp [M, diagonalScale]; omega
  have hp : binBase^s ≤ M := by dsimp [M, diagonalScale]; omega
  have hpower := binPowerBound_le_scale code wordBase cy s binBase
  change MatrixWeightedPower.powerBound binBase s ≤ 100*M^3 at hpower
  have hdiv := MatrixUnaryDivision.totalTime_bound
    (binBase^s-1) (binBase-1)
  have hmin₀ := Nat.min_le_left (binBase^s) 1
  have hmin₁ := Nat.min_le_left binBase 1
  have hrem := Nat.mod_le (binBase^s-1) (binBase-1)
  have hsub₀ := Nat.sub_le (binBase^s) 1
  have hsub₁ := Nat.sub_le binBase 1
  change MatrixWeightedDiagonalMachine.geomBound binBase s ≤ 200*M^3
  dsimp [MatrixWeightedDiagonalMachine.geomBound,
    MatrixWeightedDiagonalMachine.binPowerValue] at *
  omega

theorem preclearWords_le_scale (code wordBase cy s binBase : ℕ) :
    let M := diagonalScale code wordBase cy s binBase
    ∀ i : MatrixWeightedDiagonalMachine.Stack,
      MatrixWeightedDiagonalMachine.preclearWords code wordBase cy s
        binBase i ≤ 2*M^3 := by
  let M := diagonalScale code wordBase cy s binBase
  have hM : 1 ≤ M := diagonalScale_pos _ _ _ _ _
  have hM2 : M^2 ≤ M^3 := by
    nlinarith [Nat.mul_le_mul_left (M^2) hM]
  have hM1 : M ≤ M^2 := by nlinarith
  have hM3 : M ≤ M^3 := hM1.trans hM2
  have hd : code ≤ M := by dsimp [M, diagonalScale]; omega
  have hw : wordBase ≤ M := by dsimp [M, diagonalScale]; omega
  have hcy' : cy ≤ M := by dsimp [M, diagonalScale]; omega
  have hs : s ≤ M := by dsimp [M, diagonalScale]; omega
  have hb : binBase ≤ M := by dsimp [M, diagonalScale]; omega
  have htailPower : cy^(s+1) ≤ M := by dsimp [M, diagonalScale]; omega
  have hbinPower : binBase^s ≤ M := by dsimp [M, diagonalScale]; omega
  have hword : MatrixWeightedDiagonalMachine.word code wordBase ≤ M :=
    (Nat.mod_le _ _).trans hd
  have htail : MatrixWeightedDiagonalMachine.tail code wordBase cy s ≤ M :=
    (Nat.mod_le _ _).trans hword
  have hgeom : MatrixWeightedDiagonalMachine.geom binBase s ≤ M := by
    simp only [MatrixWeightedDiagonalMachine.geom,
      MatrixWeightedDiagonalMachine.binPowerValue]
    exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans hbinPower)
  have hproduct : code * MatrixWeightedDiagonalMachine.geom binBase s ≤
      2*M^3 := by
    have h := Nat.mul_le_mul hd hgeom
    nlinarith
  have hraw : MatrixWeightedDiagonalMachine.rawValue code wordBase cy s
      binBase ≤ 2*M^3 := by
    have h₁ := Nat.mul_le_mul htail hbinPower
    have h₂ := Nat.mul_le_mul hd hgeom
    dsimp [MatrixWeightedDiagonalMachine.rawValue,
      MatrixWeightedDiagonalMachine.binPowerValue]
    nlinarith
  change ∀ i : MatrixWeightedDiagonalMachine.Stack,
    MatrixWeightedDiagonalMachine.preclearWords code wordBase cy s
      binBase i ≤ 2*M^3
  dsimp only [M] at *
  intro i
  fin_cases i <;>
    simp [MatrixWeightedDiagonalMachine.preclearWords,
      MatrixWeightedDiagonalMachine.geomWords,
      MatrixWeightedDiagonalMachine.binPowerValue] <;>
    omega

theorem clearTime_le_scale (code wordBase cy s binBase : ℕ) :
    let M := diagonalScale code wordBase cy s binBase
    MatrixWeightedDiagonalMachine.clearTime
      (MatrixWeightedDiagonalMachine.preclearWords code wordBase cy s
        binBase) 17 ≤ 17*(2*M^3+1) := by
  let M := diagonalScale code wordBase cy s binBase
  have hword := preclearWords_le_scale code wordBase cy s binBase
  unfold MatrixWeightedDiagonalMachine.clearTime
  calc
    ∑ j ∈ Finset.range 17,
        (MatrixWeightedDiagonalMachine.preclearWords code wordBase cy s
          binBase (MatrixWeightedDiagonalMachine.slotNat j) + 1)
        ≤ ∑ _j ∈ Finset.range 17, (2*M^3+1) := by
          apply Finset.sum_le_sum
          intro j _
          exact Nat.add_le_add_right (hword _) 1
    _ = 17*(2*M^3+1) := by simp

theorem finalBound_le_scale (code wordBase cy s binBase : ℕ) :
    MatrixWeightedDiagonalMachine.finalBound code wordBase cy s binBase ≤
      100*(diagonalScale code wordBase cy s binBase)^3 := by
  let M := diagonalScale code wordBase cy s binBase
  have hM : 1 ≤ M := diagonalScale_pos _ _ _ _ _
  have hM2 : M ≤ M^2 := by nlinarith
  have hM3 : M^2 ≤ M^3 := by
    nlinarith [Nat.mul_le_mul_left (M^2) hM]
  have hd : code ≤ M := by dsimp [M, diagonalScale]; omega
  have hb : binBase ≤ M := by dsimp [M, diagonalScale]; omega
  have hp : binBase^s ≤ M := by dsimp [M, diagonalScale]; omega
  have hword : MatrixWeightedDiagonalMachine.word code wordBase ≤ M :=
    (Nat.mod_le _ _).trans hd
  have htail : MatrixWeightedDiagonalMachine.tail code wordBase cy s ≤ M :=
    (Nat.mod_le _ _).trans hword
  have hgeom : MatrixWeightedDiagonalMachine.geom binBase s ≤ M := by
    simp only [MatrixWeightedDiagonalMachine.geom,
      MatrixWeightedDiagonalMachine.binPowerValue]
    exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans hp)
  have hprod₀ : code * MatrixWeightedDiagonalMachine.geom binBase s ≤
      M^2 := by
    have h := Nat.mul_le_mul hd hgeom
    nlinarith
  have hprod₁ : MatrixWeightedDiagonalMachine.tail code wordBase cy s *
      binBase^s ≤ M^2 := by
    have h := Nat.mul_le_mul htail hp
    nlinarith
  have haddr₀ : MatrixAddressMachine.exactTime code
      (MatrixWeightedDiagonalMachine.geom binBase s) 0 ≤ 10*M^2 := by
    dsimp [MatrixAddressMachine.exactTime]
    nlinarith
  have haddr₁ : MatrixAddressMachine.exactTime
      (MatrixWeightedDiagonalMachine.tail code wordBase cy s)
      (binBase^s)
      (code * MatrixWeightedDiagonalMachine.geom binBase s) ≤
      20*M^2 := by
    dsimp [MatrixAddressMachine.exactTime]
    nlinarith
  have hclear := clearTime_le_scale code wordBase cy s binBase
  change MatrixWeightedDiagonalMachine.clearTime
    (MatrixWeightedDiagonalMachine.preclearWords code wordBase cy s
      binBase) 17 ≤ 17*(2*M^3+1) at hclear
  change MatrixWeightedDiagonalMachine.finalBound code wordBase cy s
    binBase ≤ 100*M^3
  dsimp [MatrixWeightedDiagonalMachine.finalBound,
    MatrixWeightedDiagonalMachine.binPowerValue] at *
  omega

theorem diagonalBound_le_scale (code wordBase cy s binBase : ℕ) :
    MatrixWeightedDiagonalMachine.bound code wordBase cy s binBase ≤
      500*(diagonalScale code wordBase cy s binBase)^3 := by
  have ht := tailBound_le_scale code wordBase cy s binBase
  have hg := geomBound_le_scale code wordBase cy s binBase
  have hf := finalBound_le_scale code wordBase cy s binBase
  dsimp [MatrixWeightedDiagonalMachine.bound]
  omega

/-- The two row-cleanup banks contain at most the row coordinate and one
sentinel bit after any of the four row branches. -/
theorem rowClearCost_fullFull_le (d : Input) (x y : ℕ) :
    rowClearCost (fullFullRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, fullFullRowBank, fullRowResult,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    fullCore, writerExtra]
  split_ifs <;> omega

theorem rowClearCost_fullTemplate_le (d : Input) (x y : ℕ) :
    rowClearCost (fullTemplateRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, fullTemplateRowBank, templateRowResult,
    MatrixWeightedRowController.afterCut2,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    fullCore, writerExtra]
  split_ifs <;> omega

theorem rowClearCost_fullVertex_le (d : Input) (x y : ℕ) :
    rowClearCost (fullVertexRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, fullVertexRowBank, vertexRowResult,
    MatrixWeightedRowController.afterCut3,
    MatrixWeightedRowController.afterCut2,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    fullCore, writerExtra]
  split_ifs <;> omega

theorem rowClearCost_fullAuxiliary_le (d : Input) (x y : ℕ) :
    rowClearCost (fullAuxiliaryRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, fullAuxiliaryRowBank, auxiliaryRowResult,
    MatrixWeightedRowController.afterCut3,
    MatrixWeightedRowController.afterCut2,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    fullCore, writerExtra]
  split_ifs <;> omega

theorem rowClearCost_diagonalFull_le (d : Input) (x y : ℕ) :
    rowClearCost (diagonalFullRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, diagonalFullRowBank, fullRowResult,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    diagonalCore, writerExtra]
  split_ifs <;> omega

theorem rowClearCost_diagonalTemplate_le (d : Input) (x y : ℕ) :
    rowClearCost (diagonalTemplateRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, diagonalTemplateRowBank, templateRowResult,
    MatrixWeightedRowController.afterCut2,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    diagonalCore, writerExtra]
  split_ifs <;> omega

theorem rowClearCost_diagonalVertex_le (d : Input) (x y : ℕ) :
    rowClearCost (diagonalVertexRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, diagonalVertexRowBank, vertexRowResult,
    MatrixWeightedRowController.afterCut3,
    MatrixWeightedRowController.afterCut2,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    diagonalCore, writerExtra]
  split_ifs <;> omega

theorem rowClearCost_diagonalAuxiliary_le (d : Input) (x y : ℕ) :
    rowClearCost (diagonalAuxiliaryRowBank d x y) ≤ y + 3 := by
  simp [rowClearCost, diagonalAuxiliaryRowBank, auxiliaryRowResult,
    MatrixWeightedRowController.afterCut3,
    MatrixWeightedRowController.afterCut2,
    MatrixWeightedRowController.afterCut1,
    MatrixWeightedRowController.afterCopy,
    diagonalCore, writerExtra]
  split_ifs <;> omega

/-- Both variable exponentiations performed by the diagonal controller are
bounded by the literal raw Stage--4 table width. -/
theorem actual_diagonal_powers_le_rawWidth
    (a s q cy : ℕ) (hcy : 0 < cy)
    (hbin : 2 ≤ MatrixStage4Digits.binBase a s q cy) :
    MatrixWeightedDiagonalMachine.tailPowerValue cy s ≤
      MatrixStage4Codes.cols a s q cy ∧
    MatrixWeightedDiagonalMachine.binPowerValue
        (MatrixStage4Digits.binBase a s q cy) s ≤
      MatrixStage4Codes.cols a s q cy := by
  have hbpos : 0 < (MatrixStage4Digits.binBase a s q cy)^s :=
    pow_pos (by omega) _
  have hcpos : 0 < cy^(s+1) := pow_pos hcy _
  constructor
  · simp only [MatrixWeightedDiagonalMachine.tailPowerValue,
      MatrixStage4Codes.cols]
    exact Nat.le_mul_of_pos_right _ hbpos
  · simp only [MatrixWeightedDiagonalMachine.binPowerValue,
      MatrixStage4Codes.cols, MatrixStage4Digits.binBase,
      MatrixStage4Digits.wordBase]
    exact Nat.le_mul_of_pos_left _ hcpos

theorem diagonalScale_le_inputScale (d : Input) (x y : ℕ)
    (hcy : 0 < d.cy) (hbin : 0 < d.binBase)
    (hwidth : d.rawWidth = d.cy^(d.s+1) * d.binBase^d.s) :
    diagonalScale (diagonalCode d x) d.wordBase d.cy d.s d.binBase ≤
      2*inputScale d x y := by
  have hcode : diagonalCode d x ≤ x := by
    unfold diagonalCode
    have h₁ := Nat.div_le_self x d.uniform
    have h₂ := Nat.div_le_self (x/d.uniform-d.fullBoundary)
      d.diagonalDivisor
    omega
  have hpow₀ : d.cy^(d.s+1) ≤ d.rawWidth := by
    rw [hwidth]
    exact Nat.le_mul_of_pos_right _ (pow_pos hbin _)
  have hpow₁ : d.binBase^d.s ≤ d.rawWidth := by
    rw [hwidth]
    exact Nat.le_mul_of_pos_left _ (pow_pos hcy _)
  dsimp [diagonalScale, inputScale]
  omega

theorem diagonalAddressCost_le_inputScale (d : Input) (x y : ℕ)
    (hcy : 0 < d.cy) (hbin : 0 < d.binBase)
    (hwidth : d.rawWidth = d.cy^(d.s+1) * d.binBase^d.s) :
    diagonalAddressCost d x ≤
      500*(2*inputScale d x y)^3+2 := by
  have hb := diagonalBound_le_scale (diagonalCode d x) d.wordBase
    d.cy d.s d.binBase
  have hs := diagonalScale_le_inputScale d x y hcy hbin hwidth
  have hp : (diagonalScale (diagonalCode d x) d.wordBase d.cy
      d.s d.binBase)^3 ≤ (2*inputScale d x y)^3 := by gcongr
  dsimp [diagonalAddressCost]
  exact Nat.add_le_add_right (hb.trans (Nat.mul_le_mul_left 500 hp)) 2

/-- A coarse address bound that also covers out-of-range diagonal codes.
No semantic promise about the code is used. -/
theorem diagonal_rawValue_le (code wordBase cy s binBase : ℕ)
    (hcy : 0 < cy) :
    MatrixWeightedDiagonalMachine.rawValue code wordBase cy s binBase ≤
      (code + 1) * (cy^(s+1) * binBase^s) := by
  have ht : MatrixWeightedDiagonalMachine.tail code wordBase cy s ≤
      cy^(s+1) := by
    simp only [MatrixWeightedDiagonalMachine.tail,
      MatrixWeightedDiagonalMachine.tailPowerValue]
    have hp : 0 < cy^(s+1) := pow_pos hcy _
    exact (Nat.mod_lt _ hp).le
  have hg : MatrixWeightedDiagonalMachine.geom binBase s ≤ binBase^s := by
    simp only [MatrixWeightedDiagonalMachine.geom,
      MatrixWeightedDiagonalMachine.binPowerValue]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  simp only [MatrixWeightedDiagonalMachine.rawValue,
    MatrixWeightedDiagonalMachine.binPowerValue]
  calc
    MatrixWeightedDiagonalMachine.tail code wordBase cy s * binBase^s +
        code * MatrixWeightedDiagonalMachine.geom binBase s
        ≤ cy^(s+1) * binBase^s + code * binBase^s := by
          exact Nat.add_le_add (Nat.mul_le_mul_right _ ht)
            (Nat.mul_le_mul_left _ hg)
    _ ≤ (code+1) * (cy^(s+1) * binBase^s) := by
      have hp : 1 ≤ cy^(s+1) := pow_pos hcy _
      have hB : binBase^s ≤ cy^(s+1) * binBase^s :=
        Nat.le_mul_of_pos_left _ hp
      calc
        cy^(s+1) * binBase^s + code * binBase^s
            ≤ cy^(s+1) * binBase^s +
                code * (cy^(s+1) * binBase^s) :=
              Nat.add_le_add_left (Nat.mul_le_mul_left code hB) _
        _ = (code+1) * (cy^(s+1) * binBase^s) := by ring

/-- The concrete diagonal column bank cannot grow faster than the row
coordinate times the raw-table width, even before in-range semantic decoding. -/
theorem diagonalColumnValue_le_width (d : Input) (x : ℕ)
    (hcy : 0 < d.cy)
    (hwidth : d.rawWidth = d.cy ^ (d.s + 1) * d.binBase ^ d.s) :
    diagonalColumnValue d x ≤ (x+1)*d.rawWidth := by
  have hcode : diagonalCode d x ≤ x := by
    unfold diagonalCode
    have h₁ := Nat.div_le_self x d.uniform
    have h₂ := Nat.div_le_self (x / d.uniform - d.fullBoundary)
      d.diagonalDivisor
    omega
  have h := diagonal_rawValue_le (diagonalCode d x) d.wordBase
    d.cy d.s d.binBase hcy
  unfold diagonalColumnValue
  rw [hwidth]
  exact h.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hcode 1))

theorem actualInput_diagonalColumnValue_le
    {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s) (hcy : 0 < cy)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s)
    (x : ℕ) :
    let d := MatrixWeightedEntrySemantic.actualInput R a s q L nv nb
      hs family order vectors cap
    diagonalColumnValue d x ≤ (x+1)*d.rawWidth := by
  simpa only [MatrixWeightedEntrySemantic.actualInput,
    MatrixStage4Codes.cols, MatrixStage4Digits.binBase,
    MatrixStage4Digits.wordBase] using
    diagonalColumnValue_le_width
      (MatrixWeightedEntrySemantic.actualInput R a s q L nv nb hs
        family order vectors cap) x hcy rfl

def localScale (d : Input) (x y rank : ℕ) : ℕ :=
  inputScale d x y + diagonalColumnValue d x + rank*d.rx

theorem basicStageCosts_le (d : Input) (x y rank K : ℕ)
    (hK : localScale d x y rank ≤ K) :
    copyCost x y ≤ 5*K+5 ∧
    fullColumnCost d x ≤ 50*K+50 ∧
    diagonalColumnCost d x ≤ 50*K+50 ∧
    fullRowCost d y ≤ 50*K+50 ∧
    templateRowCost d y ≤ 50*K+50 ∧
    vertexRowCost d y ≤ 50*K+50 ∧
    auxiliaryRowCost d y ≤ 50*K+50 := by
  have hxdiv := Nat.div_le_self x d.uniform
  have hminx := Nat.min_le_left (x/d.uniform) d.fullBoundary
  have hminy := Nat.min_le_left y d.rowBoundary₁
  have hminy₂ := Nat.min_le_left (y-d.rowBoundary₁) d.rowBoundary₂
  have hminy₃ := Nat.min_le_left
    (y-d.rowBoundary₁-d.rowBoundary₂) d.rowBoundary₃
  have hy₁ := Nat.sub_le y d.rowBoundary₁
  have hy₂ := Nat.sub_le (y-d.rowBoundary₁) d.rowBoundary₂
  have hx₁ := Nat.sub_le (x/d.uniform) d.fullBoundary
  have hrow₀ := Nat.div_le_self y d.rowDivisor₀
  dsimp [localScale, inputScale] at hK
  dsimp [copyCost, fullColumnCost, diagonalColumnCost,
    fullRowCost, templateRowCost, vertexRowCost, auxiliaryRowCost]
  omega

theorem lookupCost_le (row width col sourceLength K : ℕ)
    (hr : row ≤ K) (hw : width ≤ K)
    (hc : col ≤ K) (hs : sourceLength ≤ K) :
    lookupCost row width col sourceLength ≤ 32*(4*K+1)^2+1 := by
  have hsum : row+width+col+sourceLength+1 ≤ 4*K+1 := by omega
  unfold lookupCost
  gcongr

theorem orderedRow_and_orderCost_le (d : Input) (x y K : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb)) (label : ℕ) (aux : Bool)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hl : label ≤ y)
    (hK : localScale d x y (order j).val ≤ K) :
    d.stagePrefixRows + (order j).val*d.rx + label%d.rx ≤ K ∧
    orderBound order j label d.rx d.stagePrefixRows aux ≤ 100*K+100 := by
  have hmod : label % d.rx ≤ label := Nat.mod_le _ _
  have hdiv : label / d.rx ≤ label := Nat.div_le_self _ _
  have hj : j.val < d.nv+d.nb := j.isLt
  have hrank : (order j).val < d.nv+d.nb := (order j).isLt
  dsimp [localScale, inputScale] at hK
  rw [horder] at hK
  constructor
  · omega
  · cases aux <;>
      dsimp [orderBound, MatrixAddressMachine.exactTime] <;>
      simp only [mul_assoc] <;>
      omega

def cellTermBound (K : ℕ) : ℕ :=
  (500*(2*K)^3+2) + (32*(4*K+1)^2+1) + 500*K+500

theorem cellTermBound_le_poly (K : ℕ) :
    cellTermBound K ≤ 10000*(K+1)^3 := by
  dsimp [cellTermBound]
  nlinarith [Nat.zero_le K]

theorem eight_lookups_le (d : Input) (x y K : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hK : localScale d x y (order j).val ≤ K) :
    let B := 32*(4*K+1)^2+1
    lookupCost (fullLabel d y) d.rawWidth
      ((x/d.uniform)/d.fullDivisor) d.rawBits.length ≤ B ∧
    lookupCost (templateLabel d y) d.rawWidth
      ((x/d.uniform)/d.fullDivisor) d.rawBits.length ≤ B ∧
    lookupCost (fullLabel d y) d.rawWidth
      (diagonalColumnValue d x) d.rawBits.length ≤ B ∧
    lookupCost (templateLabel d y) d.rawWidth
      (diagonalColumnValue d x) d.rawBits.length ≤ B ∧
    lookupCost (d.stagePrefixRows+(order j).val*d.rx+
      vertexLabel d y%d.rx) d.rawWidth
      ((x/d.uniform)/d.fullDivisor) d.rawBits.length ≤ B ∧
    lookupCost (d.stagePrefixRows+(order j).val*d.rx+
      auxiliaryLabel d y%d.rx) d.rawWidth
      ((x/d.uniform)/d.fullDivisor) d.rawBits.length ≤ B ∧
    lookupCost (d.stagePrefixRows+(order j).val*d.rx+
      vertexLabel d y%d.rx) d.rawWidth
      (diagonalColumnValue d x) d.rawBits.length ≤ B ∧
    lookupCost (d.stagePrefixRows+(order j).val*d.rx+
      auxiliaryLabel d y%d.rx) d.rawWidth
      (diagonalColumnValue d x) d.rawBits.length ≤ B := by
  have hdiv₀ := Nat.div_le_self x d.uniform
  have hdiv₁ := Nat.div_le_self (x/d.uniform) d.fullDivisor
  have hfull : fullLabel d y ≤ y := Nat.div_le_self _ _
  have htemplate : templateLabel d y ≤ y := by
    unfold templateLabel
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hv : vertexLabel d y ≤ y := by
    unfold vertexLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have ha : auxiliaryLabel d y ≤ y := by
    unfold auxiliaryLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans
        (Nat.sub_le _ _)))
  have hrowv := (orderedRow_and_orderCost_le d x y K order j
    (vertexLabel d y) false horder hv hK).1
  have hrowa := (orderedRow_and_orderCost_le d x y K order j
    (auxiliaryLabel d y) true horder ha hK).1
  have hx : x ≤ K := by dsimp [localScale, inputScale] at hK; omega
  have hy : y ≤ K := by dsimp [localScale, inputScale] at hK; omega
  have hw : d.rawWidth ≤ K := by dsimp [localScale, inputScale] at hK; omega
  have hs : d.rawBits.length ≤ K := by
    dsimp [localScale, inputScale] at hK; omega
  have hd : diagonalColumnValue d x ≤ K := by
    dsimp [localScale] at hK; omega
  have hc : (x/d.uniform)/d.fullDivisor ≤ K :=
    hdiv₁.trans (hdiv₀.trans hx)
  refine ⟨lookupCost_le _ _ _ _ K (hfull.trans hy) hw hc hs,
    lookupCost_le _ _ _ _ K (htemplate.trans hy) hw hc hs,
    lookupCost_le _ _ _ _ K (hfull.trans hy) hw hd hs,
    lookupCost_le _ _ _ _ K (htemplate.trans hy) hw hd hs,
    lookupCost_le _ _ _ _ K hrowv hw hc hs,
    lookupCost_le _ _ _ _ K hrowa hw hc hs,
    lookupCost_le _ _ _ _ K hrowv hw hd hs,
    lookupCost_le _ _ _ _ K hrowa hw hd hs⟩

theorem eight_cell_terms_le (d : Input) (x y K : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (j : Fin (d.nv+d.nb))
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hcy : 0 < d.cy) (hbin : 0 < d.binBase)
    (hwidth : d.rawWidth = d.cy^(d.s+1)*d.binBase^d.s)
    (hK : localScale d x y (order j).val ≤ K) :
    fullFullCost d x y ≤ cellTermBound K ∧
    fullTemplateCost d x y ≤ cellTermBound K ∧
    diagonalFullCost d x y ≤ cellTermBound K ∧
    diagonalTemplateCost d x y ≤ cellTermBound K ∧
    fullVertexCost d x y order j ≤ cellTermBound K ∧
    fullAuxiliaryCost d x y order j ≤ cellTermBound K ∧
    diagonalVertexCost d x y order j ≤ cellTermBound K ∧
    diagonalAuxiliaryCost d x y order j ≤ cellTermBound K := by
  let D := inputScale d x y + diagonalColumnValue d x
  let O := localScale d x y (order j).val
  have hD : D ≤ K := by dsimp [D, localScale] at *; omega
  have hO : O ≤ K := hK
  have hlocal : inputScale d x y + diagonalColumnValue d x +
      (order j).val*d.rx ≤ K := by simpa only [localScale] using hK
  have hscale : inputScale d x y ≤ K := by
    dsimp [localScale] at hK; omega
  have hy : y ≤ K := by dsimp [localScale, inputScale] at hK; omega
  obtain ⟨hcopy,hfullcol,hdiagcol,hfullrow,htemplrow,
      hverrow,hauxrow⟩ := basicStageCosts_le d x y (order j).val K hK
  obtain ⟨hw₀,hw₁,hw₂,hw₃⟩ := direct_workLengths_le d x y
  obtain ⟨hw₄,hw₅,hw₆,hw₇⟩ :=
    ordered_workLengths_le d x y order j horder
  obtain ⟨hl₀,hl₁,hl₂,hl₃,hl₄,hl₅,hl₆,hl₇⟩ :=
    eight_lookups_le d x y K order j horder hK
  have hv : vertexLabel d y ≤ y := by
    unfold vertexLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have ha : auxiliaryLabel d y ≤ y := by
    unfold auxiliaryLabel
    exact (Nat.div_le_self _ _).trans
      ((Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans
        (Nat.sub_le _ _)))
  have hfullLabel : fullLabel d y ≤ y := Nat.div_le_self _ _
  have htemplateLabel : templateLabel d y ≤ y := by
    unfold templateLabel
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have horderV := (orderedRow_and_orderCost_le d x y K order j
    (vertexLabel d y) false horder hv hK).2
  have horderA := (orderedRow_and_orderCost_le d x y K order j
    (auxiliaryLabel d y) true horder ha hK).2
  have haddr₀ := diagonalAddressCost_le_inputScale d x y hcy hbin hwidth
  have haddr : diagonalAddressCost d x ≤ 500*(2*K)^3+2 := by
    have hp : (2*inputScale d x y)^3 ≤ (2*K)^3 := by gcongr
    exact haddr₀.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 500 hp) 2)
  have hclear₀ := rowClearCost_fullFull_le d x y
  have hclear₁ := rowClearCost_fullTemplate_le d x y
  have hclear₂ := rowClearCost_diagonalFull_le d x y
  have hclear₃ := rowClearCost_diagonalTemplate_le d x y
  have hclear₄ := rowClearCost_fullVertex_le d x y
  have hclear₅ := rowClearCost_fullAuxiliary_le d x y
  have hclear₆ := rowClearCost_diagonalVertex_le d x y
  have hclear₇ := rowClearCost_diagonalAuxiliary_le d x y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp [fullFullCost, fullTemplateCost, diagonalFullCost,
    diagonalTemplateCost, fullVertexCost, fullAuxiliaryCost,
    diagonalVertexCost, diagonalAuxiliaryCost, cellTermBound]
  all_goals omega

theorem direct_four_terms_le (d : Input) (x y K : ℕ)
    (hcy : 0 < d.cy) (hbin : 0 < d.binBase)
    (hwidth : d.rawWidth = d.cy^(d.s+1)*d.binBase^d.s)
    (hK : inputScale d x y + diagonalColumnValue d x ≤ K) :
    fullFullCost d x y ≤ cellTermBound K ∧
    fullTemplateCost d x y ≤ cellTermBound K ∧
    diagonalFullCost d x y ≤ cellTermBound K ∧
    diagonalTemplateCost d x y ≤ cellTermBound K := by
  have hlocal : localScale d x y 0 ≤ K := by
    simpa only [localScale, zero_mul, add_zero] using hK
  obtain ⟨hcopy,hfullcol,hdiagcol,hfullrow,htemplrow,_,_⟩ :=
    basicStageCosts_le d x y 0 K hlocal
  obtain ⟨hw₀,hw₁,hw₂,hw₃⟩ := direct_workLengths_le d x y
  have hx : x ≤ K := by dsimp [inputScale] at hK; omega
  have hy : y ≤ K := by dsimp [inputScale] at hK; omega
  have hwidth' : d.rawWidth ≤ K := by dsimp [inputScale] at hK; omega
  have hsource : d.rawBits.length ≤ K := by
    dsimp [inputScale] at hK; omega
  have hdiag : diagonalColumnValue d x ≤ K := by omega
  have hcol : (x/d.uniform)/d.fullDivisor ≤ K :=
    (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hx)
  have hfullLabel : fullLabel d y ≤ y := Nat.div_le_self _ _
  have htemplateLabel : templateLabel d y ≤ y := by
    unfold templateLabel
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hl₀ := lookupCost_le (fullLabel d y) d.rawWidth
    ((x/d.uniform)/d.fullDivisor) d.rawBits.length K
    (hfullLabel.trans hy) hwidth' hcol hsource
  have hl₁ := lookupCost_le (templateLabel d y) d.rawWidth
    ((x/d.uniform)/d.fullDivisor) d.rawBits.length K
    (htemplateLabel.trans hy) hwidth' hcol hsource
  have hl₂ := lookupCost_le (fullLabel d y) d.rawWidth
    (diagonalColumnValue d x) d.rawBits.length K
    (hfullLabel.trans hy) hwidth' hdiag hsource
  have hl₃ := lookupCost_le (templateLabel d y) d.rawWidth
    (diagonalColumnValue d x) d.rawBits.length K
    (htemplateLabel.trans hy) hwidth' hdiag hsource
  have haddr₀ := diagonalAddressCost_le_inputScale d x y hcy hbin hwidth
  have haddr : diagonalAddressCost d x ≤ 500*(2*K)^3+2 := by
    have hs : inputScale d x y ≤ K := by omega
    have hp : (2*inputScale d x y)^3 ≤ (2*K)^3 := by gcongr
    exact haddr₀.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 500 hp) 2)
  have hclear₀ := rowClearCost_fullFull_le d x y
  have hclear₁ := rowClearCost_fullTemplate_le d x y
  have hclear₂ := rowClearCost_diagonalFull_le d x y
  have hclear₃ := rowClearCost_diagonalTemplate_le d x y
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals dsimp [fullFullCost, fullTemplateCost,
    diagonalFullCost, diagonalTemplateCost, cellTermBound]
  all_goals omega

theorem cellTermBound_mono {K L : ℕ} (h : K ≤ L) :
    cellTermBound K ≤ cellTermBound L := by
  unfold cellTermBound
  gcongr

def uniformCellScale (d : Input) (x y : ℕ) : ℕ :=
  inputScale d x y + diagonalColumnValue d x + (d.nv+d.nb)*d.rx

theorem cellCost_le_uniformCellScale (d : Input) (x y : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hcy : 0 < d.cy) (hbin : 0 < d.binBase)
    (hwidth : d.rawWidth = d.cy^(d.s+1)*d.binBase^d.s) :
    cellCost d x y order ≤ cellTermBound (uniformCellScale d x y) := by
  let K := uniformCellScale d x y
  have hdirect : inputScale d x y + diagonalColumnValue d x ≤ K := by
    dsimp [K, uniformCellScale]
    omega
  obtain ⟨h₀,h₁,h₂,h₃⟩ := direct_four_terms_le d x y K
    hcy hbin hwidth hdirect
  unfold cellCost directCaseCost orderedCaseCost
  apply max_le
  · exact max_le (max_le h₀ h₁) (max_le h₂ h₃)
  · apply Finset.sup_le
    intro j _
    have hrank : (order j).val ≤ d.nv+d.nb := (order j).isLt.le
    have hlocal : localScale d x y (order j).val ≤ K := by
      dsimp [localScale, K, uniformCellScale]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right d.rx hrank) _
    obtain ⟨_,_,_,_,hv,ha,hdv,hda⟩ :=
      eight_cell_terms_le d x y K order j horder hcy hbin hwidth hlocal
    exact max_le (max_le hv ha) (max_le hdv hda)

def globalScale (d : Input) (rows cols : ℕ) : ℕ :=
  inputScale d rows cols + (rows+1)*d.rawWidth +
    (d.nv+d.nb)*d.rx

theorem uniformCellScale_le_globalScale (d : Input)
    (rows cols x y : ℕ) (hx : x ≤ rows) (hy : y ≤ cols)
    (hcy : 0 < d.cy)
    (hwidth : d.rawWidth = d.cy^(d.s+1)*d.binBase^d.s) :
    uniformCellScale d x y ≤ globalScale d rows cols := by
  have hdiag := diagonalColumnValue_le_width d x hcy hwidth
  have hdiag' : diagonalColumnValue d x ≤ (rows+1)*d.rawWidth :=
    hdiag.trans (Nat.mul_le_mul_right _ (by omega))
  dsimp [uniformCellScale, globalScale, inputScale]
  omega

theorem commonCost_le_globalScale (d : Input) (rows cols : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hcy : 0 < d.cy) (hbin : 0 < d.binBase)
    (hwidth : d.rawWidth = d.cy^(d.s+1)*d.binBase^d.s) :
    commonCost d rows cols order ≤ cellTermBound (globalScale d rows cols) := by
  unfold commonCost
  apply Finset.sup_le
  intro x _
  apply Finset.sup_le
  intro y _
  have hc := cellCost_le_uniformCellScale d x.val y.val order
    horder hcy hbin hwidth
  have hs := uniformCellScale_le_globalScale d rows cols x.val y.val
    x.isLt.le y.isLt.le hcy hwidth
  exact hc.trans (cellTermBound_mono hs)

theorem globalScale_le_quadratic (d : Input) (rows cols : ℕ) :
    globalScale d rows cols ≤ 3*(inputScale d rows cols)^2 := by
  let N := inputScale d rows cols
  have hN : 1 ≤ N := by dsimp [N, inputScale]; omega
  have hN2 : N ≤ N^2 := by nlinarith
  have hrows : rows+1 ≤ N := by dsimp [N, inputScale]; omega
  have hwidth : d.rawWidth ≤ N := by dsimp [N, inputScale]; omega
  have hitems : d.nv+d.nb ≤ N := by dsimp [N, inputScale]; omega
  have hrx : d.rx ≤ N := by dsimp [N, inputScale]; omega
  have hprod₀ : (rows+1)*d.rawWidth ≤ N^2 := by
    have h := Nat.mul_le_mul hrows hwidth
    nlinarith
  have hprod₁ : (d.nv+d.nb)*d.rx ≤ N^2 := by
    have h := Nat.mul_le_mul hitems hrx
    nlinarith
  dsimp only [N] at *
  dsimp [globalScale]
  omega

/-- Explicit fixed polynomial for the finite maximum of the eight charged
stage sums. No least-halting-time supremum appears in this statement. -/
theorem commonCost_polynomial (d : Input) (rows cols : ℕ)
    (order : Construction.ItemOrder d.nv d.nb)
    (horder : d.orderBits = MatrixWeightedRowOrderLookup.orderWord order)
    (hcy : 0 < d.cy) (hbin : 0 < d.binBase)
    (hwidth : d.rawWidth = d.cy^(d.s+1)*d.binBase^d.s) :
    commonCost d rows cols order ≤
      10000*(3*(inputScale d rows cols)^2+1)^3 := by
  have hc := commonCost_le_globalScale d rows cols order
    horder hcy hbin hwidth
  have hp := cellTermBound_le_poly (globalScale d rows cols)
  have hs := globalScale_le_quadratic d rows cols
  have hpow : (globalScale d rows cols+1)^3 ≤
      (3*(inputScale d rows cols)^2+1)^3 := by gcongr
  exact hc.trans (hp.trans (Nat.mul_le_mul_left 10000 hpow))

/-- The actual protected matrix, with literal raw table and public item
order, has one polynomial charged entry clock in its supplied unary scalars,
payload lengths and output dimensions. This does not charge preparation of
those physical input words from the original graph. -/
theorem actual_commonCost_poly
    {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L nv nb : ℕ) (hs : 0 < s) (hcy : 0 < cy)
    (hbin : 2 ≤ MatrixStage4Digits.binBase a s q cy)
    (family : Construction.SecondFamily a q L (Fin rx))
    (order : Construction.ItemOrder nv nb)
    (vectors : Fin (nv+nb) → Fin q → Bool)
    (cap : ∀ α, (Construction.activeItems vectors α).card ≤ s) :
    let d := MatrixWeightedEntrySemantic.actualInput R a s q L nv nb
      hs family order vectors cap
    let rows := Fintype.card (Construction.ProtectedColumns a s q (Fin cy))
    let cols := Fintype.card
      (Construction.ProtectedRows s L nv nb (Fin rx))
    commonCost d rows cols order ≤
      10000*(3*(inputScale d rows cols)^2+1)^3 := by
  apply commonCost_polynomial
  · rfl
  · exact hcy
  · change 0 < MatrixStage4Digits.binBase a s q cy
    omega
  · rfl

end EthInapproximability.CurrentPaper.MatrixWeightedEntryEnvelope
