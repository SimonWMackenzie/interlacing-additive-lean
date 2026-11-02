import EthInapproximability.CurrentPaper.EncodedGraph
import EthInapproximability.CurrentPaper.ExactConstruction
import EthInapproximability.CurrentPaper.GraphVectors
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-! # Source-vector payloads for the two graph constructions

The exact reduction uses five disjoint copies of the edge-incidence vectors.
The ETH construction instead uses its own edge-only coordinates, four-times-s
copies, and auxiliary rows. These layouts are deliberately separate. The
definitions here identify the Boolean payloads expected by the row-major
materializer; they do not assert a bit-machine running-time bound for producing
those payloads from an encoded graph.
-/

namespace EthInapproximability.CurrentPaper.SourceGraphVectorPayload

open MatrixMaterialization

/-- The literal five-copy source table of the exact reduction. -/
def exactBits (g : EncodedGraph.Graph) (hg : g.Valid) (D : ℕ) : List Bool :=
  rowMajor (ExactConstruction.sourceVectors D (EncodedGraph.endpoints g hg))

theorem exactBits_length (g : EncodedGraph.Graph) (hg : g.Valid) (D : ℕ) :
    (exactBits g hg D).length = (5 * g.vertices) * D := by
  simp [exactBits]

theorem exactBits_entry (g : EncodedGraph.Graph) (hg : g.Valid) (D : ℕ)
    (i : Fin (5 * g.vertices)) (α : Fin D) :
    (exactBits g hg D)[i.val * D + α.val]? =
      some (ExactConstruction.sourceVectors D (EncodedGraph.endpoints g hg) i α) := by
  exact rowMajor_entry _ i α

/-- Beyond all five edge-coordinate copies the exact source row is zero. -/
theorem exactBits_padding (g : EncodedGraph.Graph) (hg : g.Valid) (D : ℕ)
    (i : Fin (5 * g.vertices)) (α : Fin D)
    (hα : 5 * g.edges.length ≤ α.val) :
    (exactBits g hg D)[i.val * D + α.val]? = some false := by
  rw [exactBits_entry]
  simp [ExactConstruction.sourceVectors, ExactConstruction.padVectors, not_lt.mpr hα]

/-- Every nonzero unpadded exact coordinate is an endpoint incidence in the
same one of the five copies. The coordinate and row permutations are the
literal public copy-major permutations of `ExactConstruction`. -/
theorem exactBits_incidence (g : EncodedGraph.Graph) (hg : g.Valid) (D : ℕ)
    (i : Fin (5 * g.vertices)) (α : Fin D)
    (hα : α.val < 5 * g.edges.length) :
    (exactBits g hg D)[i.val * D + α.val]? = some true ↔
      (finProdFinEquiv.symm i).1 =
          (finProdFinEquiv.symm (⟨α.val, hα⟩ : Fin (5 * g.edges.length))).1 ∧
        ∃ j : Fin 2, (finProdFinEquiv.symm i).2 =
          EncodedGraph.endpoints g hg
            (finProdFinEquiv.symm (⟨α.val, hα⟩ : Fin (5 * g.edges.length))).2 j := by
  rw [exactBits_entry]
  simp [ExactConstruction.sourceVectors, ExactConstruction.padVectors,
    ExactConstruction.encodedFiveCopyVectors, ExactConstruction.fiveCopyVectors, hα]

theorem exactBits_storeBits_source (g : EncodedGraph.Graph) (hg : g.Valid)
    {a N₁ N₂ : ℕ} (D : ℕ) (C₁ : ExactConstruction.FirstFamily a N₁)
    (C₂ : ExactConstruction.SecondFamily a D N₂) :
    (storeBits C₁ C₂
      (ExactConstruction.sourceVectors D (EncodedGraph.endpoints g hg))).source =
      exactBits g hg D := rfl

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

/-- The distinct ETH edge-coordinate payload in the public copy-major row order. -/
def ethBits {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (s : ℕ) : List Bool :=
  rowMajor (GraphVectors.vectors G s)

theorem ethBits_length {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (s : ℕ) :
    (ethBits G s).length =
      (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) *
        q2 G s := by
  simp [ethBits]

theorem ethBits_entry {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (s : ℕ)
    (i : Fin (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s))
    (α : Fin (q2 G s)) :
    (ethBits G s)[i.val * q2 G s + α.val]? =
      some (GraphVectors.vectors G s i α) := by
  exact rowMajor_entry _ i α

end EthInapproximability.CurrentPaper.SourceGraphVectorPayload
