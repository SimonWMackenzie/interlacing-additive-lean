import EthInapproximability.CurrentPaper.MatrixExactComputableUnaryHeaderSequence
import EthInapproximability.CurrentPaper.SamplerWriterPhysicalSequence

/-!
# Shared bank for the physical sampler and exact-instance constructor

The writer cells are shared literally. The sampler's two extra input cells
remain disjoint from the header conversion work and threshold cells. These
are explicit input layouts, not data imported from the target instance.
-/

namespace EthInapproximability.CurrentPaper.MatrixExactSamplerHeaderBridge

abbrev Header := MatrixExactComputableUnaryHeaderSequence.Stack
abbrev Sampler := SamplerWriterPhysicalSequence.Stack
abbrev Stack := Header ⊕ Fin 2

def samplerSlots : Sampler ↪ Stack where
  toFun
    | .inl k => .inl (.inl k)
    | .inr k => .inr k
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

def headerSlots : Header ↪ Stack where
  toFun := Sum.inl
  inj' := by
    intro x y h
    exact Sum.inl.inj h

def startBank (a d N₁ N₂ n threshold : ℕ)
    (source firstDegree secondDegree : List Bool)
    (firstLength secondLength : ℕ) : Stack → List Bool
  | .inl (.inl k) =>
      SamplerWriterPhysicalSequence.initial a d N₁ N₂ n source
        firstDegree secondDegree firstLength secondLength (.inl k)
  | .inl (.inr (.inl _)) => []
  | .inl (.inr (.inr ())) => List.replicate threshold true
  | .inr k =>
      SamplerWriterPhysicalSequence.initial a d N₁ N₂ n source
        firstDegree secondDegree firstLength secondLength (.inr k)

theorem startBank_sampler (a d N₁ N₂ n threshold : ℕ)
    (source firstDegree secondDegree : List Bool)
    (firstLength secondLength : ℕ) (k : Sampler) :
    startBank a d N₁ N₂ n threshold source firstDegree secondDegree
        firstLength secondLength (samplerSlots k) =
      SamplerWriterPhysicalSequence.initial a d N₁ N₂ n source
        firstDegree secondDegree firstLength secondLength k := by
  cases k <;> rfl

theorem startBank_embedded (a d N₁ N₂ n threshold : ℕ)
    (source firstDegree secondDegree : List Bool)
    (firstLength secondLength : ℕ) :
    BitMachineStackEmbedding.bank samplerSlots
      (startBank a d N₁ N₂ n threshold source firstDegree secondDegree
        firstLength secondLength)
      (SamplerWriterPhysicalSequence.initial a d N₁ N₂ n source
        firstDegree secondDegree firstLength secondLength) =
    startBank a d N₁ N₂ n threshold source firstDegree secondDegree
      firstLength secondLength := by
  classical
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  exact (startBank_sampler a d N₁ N₂ n threshold source firstDegree
    secondDegree firstLength secondLength k).symm

def readyBank (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) : Stack → List Bool :=
  Sum.elim
    (MatrixExactComputableUnaryHeaderSequence.initial a d N₁ N₂ n
      threshold data)
    (fun _ => [])

theorem readyBank_header (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (k : Header) :
    readyBank a d N₁ N₂ n threshold data (headerSlots k) =
      MatrixExactComputableUnaryHeaderSequence.initial a d N₁ N₂ n
        threshold data k := rfl

theorem readyBank_sampler (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) (k : Sampler) :
    readyBank a d N₁ N₂ n threshold data (samplerSlots k) =
      Sum.elim (MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data)
        (fun _ => []) k := by
  cases k <;> rfl

theorem readyBank_from_sampler (a d N₁ N₂ n threshold : ℕ)
    (source firstDegree secondDegree : List Bool)
    (firstLength secondLength : ℕ)
    (data : MatrixMaterialization.ExactBitData) :
    BitMachineStackEmbedding.bank samplerSlots
      (startBank a d N₁ N₂ n threshold source firstDegree secondDegree
        firstLength secondLength)
      (Sum.elim (MatrixScalarWriterFrame.rawInput a d N₁ N₂ n data)
        (fun _ => [])) =
    readyBank a d N₁ N₂ n threshold data := by
  classical
  funext j
  by_cases h : ∃ k, samplerSlots k = j
  · obtain ⟨k, rfl⟩ := h
    rw [BitMachineStackEmbedding.bank_at]
    exact (readyBank_sampler a d N₁ N₂ n threshold data k).symm
  · rw [BitMachineStackEmbedding.bank_outside _ _ _ _ h]
    cases j with
    | inl j =>
      cases j with
      | inl j => exact False.elim (h ⟨.inl j, rfl⟩)
      | inr j => cases j <;> rfl
    | inr j => exact False.elim (h ⟨.inr j, rfl⟩)

theorem readyBank_embedded (a d N₁ N₂ n threshold : ℕ)
    (data : MatrixMaterialization.ExactBitData) :
    BitMachineStackEmbedding.bank headerSlots
      (readyBank a d N₁ N₂ n threshold data)
      (MatrixExactComputableUnaryHeaderSequence.initial a d N₁ N₂ n
        threshold data) =
    readyBank a d N₁ N₂ n threshold data := by
  classical
  apply BitMachineStackEmbedding.bank_eq_self
  exact readyBank_header a d N₁ N₂ n threshold data

end EthInapproximability.CurrentPaper.MatrixExactSamplerHeaderBridge
