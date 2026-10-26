import Paper2.SourceSupportCapacity

/-!
# Dense genuine Alice fibres for paired-selector capacity

These generic facts use the actual retained row set and the query of an
actual Alice node. The two fibres partition that row set; no independence
or product structure is required of its finite law. The protocol adapters
reuse the same genuine-child construction as the frozen v12 remaining-
conversation argument in `SourceSupportCapacity`.
-/

namespace Paper2.PairedSelectorCapacityFibre

open SourceSupportCapacity
open Workspace.Types.CommComplexity Workspace.Types.Protocol

section Mass

variable {A : Type*} [Fintype A]

/-- The heavier actual message fibre, with the existing false-on-ties rule. -/
noncomputable def heavyRowBit (μ : FiniteLaw A) (V : Set A) (query : V → Bool) : Bool := by
  classical
  exact SourceSupportStep.heavyBit μ V.toFinset (rawQuery V query)

/-- A lower bound on the original retained mass gives half that bound
on the genuine heavier Alice fibre. -/
theorem heavy_rowFibre_mass (μ : FiniteLaw A) (V : Set A) (query : V → Bool)
    (t : ℝ) (hV : 2 * t ≤ μ.prob (· ∈ V)) :
    t ≤ μ.prob (· ∈ rowFibre V query (heavyRowBit μ V query)) := by
  classical
  have hmass : SourceSupportStep.mass μ V.toFinset = μ.prob (· ∈ V) := by
    simp [SourceSupportStep.mass]
  have hf := SourceSupportStep.heavy_floor μ V.toFinset (rawQuery V query) t
    (by simpa only [hmass] using hV)
  simpa only [heavyRowBit, SourceSupportStep.mass, SourceSupportStep.mem_fibre,
    Set.mem_toFinset, rowFibre, Set.mem_setOf_eq] using hf

/-- The same concrete bit satisfies both the exact half-mass bound and
the weaker threshold required by the row-capacity estimate. -/
theorem exists_dense_rowFibre (μ : FiniteLaw A) (V : Set A) (query : V → Bool)
    (hV : (49 / 64 : ℝ) ≤ μ.prob (· ∈ V)) :
    ∃ b, (49 / 128 : ℝ) ≤ μ.prob (· ∈ rowFibre V query b) ∧
      (9 / 25 : ℝ) ≤ μ.prob (· ∈ rowFibre V query b) := by
  have hh := heavy_rowFibre_mass μ V query (49 / 128) (by linarith)
  exact ⟨heavyRowBit μ V query, hh, by linarith⟩

end Mass

section Protocol

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Pointwise correctness of an actual protocol bounds the cost of the
same retained rectangle, without transposing or replacing its inputs. -/
theorem restrictionD_le_protocol (F : A → B → Bool) (V : Set A) (U : Set B)
    (P : Protocol V U Bool)
    (hP : P.Computes (fun v u => F v.val u.val)) :
    Compression.restrictionD F V U ≤ P.cost := by
  classical
  exact Nat.sInf_le ⟨P, rfl, hP⟩

/-- The selected genuine child pays at most the parent's budget minus
the actual Alice bit; its entire retained column carrier is unchanged. -/
theorem rowFibre_restrictionD_add_one_le (F : A → B → Bool)
    (V : Set A) (U : Set B) (query : V → Bool)
    (left right : Protocol V U Bool)
    (hP : (Protocol.aNode query left right).Computes (fun v u => F v.val u.val))
    (b : Bool) :
    Compression.restrictionD F (rowFibre V query b) U + 1 ≤
      (Protocol.aNode query left right).cost := by
  have hc := childProtocol_computes (fun v (u : U) => F v u.val)
    V query left right hP b
  have hd := restrictionD_le_protocol F (rowFibre V query b) U
    (childProtocol V query left right b) hc
  exact (Nat.add_le_add_right hd 1).trans (childProtocol_cost V query left right b)

end Protocol

end Paper2.PairedSelectorCapacityFibre

#print axioms Paper2.PairedSelectorCapacityFibre.heavy_rowFibre_mass
#print axioms Paper2.PairedSelectorCapacityFibre.exists_dense_rowFibre
#print axioms Paper2.PairedSelectorCapacityFibre.restrictionD_le_protocol
#print axioms Paper2.PairedSelectorCapacityFibre.rowFibre_restrictionD_add_one_le
