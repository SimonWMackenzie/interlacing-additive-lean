import CurrentAdditive.SmallBiasPublicFixedGap
import Paper2.YaoX05Draft

/-!
# The adopted hypergraph source feeds the public printed matrix

Source: v27 Section 7, `yao:source` and `yao:main`. The external
Guruswami--Lee reduction remains an explicit parameter `GLSourceDraft`;
its measure-to-colouring and distinct-clone conversions are proved in
Paper2. This module selects computable edge addresses and applies the
fixed-gap physical-list semantic theorem. Machine runtime is separate.
-/

namespace CurrentAdditive.SmallBias

open Paper2.Yao Paper2.YaoLookup Workspace.Types.Protocol
open Paper2.YaoCloneSource Paper2.YaoX05Draft
open CurrentAdditive.FiniteFieldConstructor

/-- Enough public bits to address every edge, including the empty case. -/
def publicAddressBits (edgeCount : ℕ) : ℕ :=
  Nat.clog 2 (edgeCount + 1)

theorem publicAddress_capacity (edgeCount : ℕ) :
    edgeCount ≤ 2 ^ publicAddressBits edgeCount := by
  have h := Nat.le_pow_clog (by omega : 1 < 2) (edgeCount + 1)
  dsimp [publicAddressBits]
  omega

/-- Address edge `i` by its own natural index in the public binary bank. -/
def publicAddressIndex (edgeCount : ℕ) :
    Fin edgeCount ↪ Fin (2 ^ publicAddressBits edgeCount) :=
  ⟨fun i => Fin.castLE (publicAddress_capacity edgeCount) i,
    fun _ _ h => Fin.castLE_injective _ h⟩

/-- Relative to the author-adopted external hypergraph source contract,
one deterministic printed word list serves both source promises. -/
theorem gl_source_public_printed_gap
    (g : ℕ) (G : GLSourceDraft (v27GapParameter g))
    (input : List Bool) :
    let t := v27GapParameter g
    let source := cloneSource t (forbiddenColours t) (G.output input)
    let b := publicAddressBits source.2.1
    ∃ output : List (ℕ × ℕ × List Bool), ∃ modulus : ℕ,
      TrialSearch.makeList (publicFieldDegree b t)
        (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output ∧
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      output = StreamingPrinter.labelledWords (publicFieldDegree b t)
        modulus (2 ^ b * (2 ^ t * 2 ^ t + 1)) ∧
      (let M := matrix (placeEdges source.2.2
          (publicAddressIndex source.2.1))
          (fullSelector (2 ^ (t - 1)) (2 ^ b))
          (printedPairFieldWord b t (publicFieldDegree b t) modulus)
       (input ∈ G.L → Dalt .alice M ≤ 2 * b + 4 * t + 2) ∧
       (input ∉ G.L → (2 * b + 4 * t + 2) + g ≤ Dalt .alice M)) := by
  dsimp only
  let t := v27GapParameter g
  let source := cloneSource t (forbiddenColours t) (G.output input)
  let b := publicAddressBits source.2.1
  obtain ⟨output, modulus, hmake, hmod, heq, _, hyes, hno⟩ :=
    public_printed_matrix_fixed_gap g b source.2.2
      (publicAddressIndex source.2.1)
  refine ⟨output, modulus, hmake, hmod, heq, ?_, ?_⟩
  · intro hmember
    obtain ⟨colour, hbalanced⟩ := draft_clone_source_yes G input hmember
    exact hyes colour hbalanced
  · intro hnot
    exact hno (draft_clone_source_no G input hnot)

#print axioms CurrentAdditive.SmallBias.publicAddress_capacity
#print axioms CurrentAdditive.SmallBias.gl_source_public_printed_gap

end CurrentAdditive.SmallBias
