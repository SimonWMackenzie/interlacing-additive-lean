import CurrentAdditive.CanonicalPhysicalIndexClock
import Paper2.YaoPosFull

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing Paper2.YaoLookup Paper2.YaoPositionFull
open Paper2.UnaryFieldListParserScratch Paper2.YaoSourceCodec
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

theorem canonical_position_eq_padded {v e t : ℕ}
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : Fin (paddedEdgeCount e)) (vertex : Fin v) :
    position (le_paddedEdgeCount e) edges a vertex =
      positionEval (paddedEdgesEval edges) a vertex := rfl

/-- The old fixed physical incidence scanner computes the exact position
used by the canonical table, at the source's least power-of-two address
width. Its body tape and unary inputs are explicitly required. -/
theorem physical_canonical_position {J : Type*} [DecidableEq J]
    (ι : Fin 13 ↪ J) (W : J → List Bool) {t v e : ℕ}
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (a : Fin (paddedEdgeCount e)) (vertex : Fin v)
    (h0 : W (ι 0) = tokens (List.ofFn (flatten edges)))
    (h1 : W (ι 1) = List.replicate a.val true)
    (h2 : W (ι 2) = List.replicate (arity t) true)
    (h3 : W (ι 3) = List.replicate vertex.val true)
    (hempty : ∀ k : Fin 13, 4 ≤ k.val → W (ι k) = []) :
    ∃ total ≤ (2 * (tokens (List.ofFn (flatten edges))).length + 2) +
        (2 * a.val + 2) + (2 * arity t + 2) +
        (a.val * (2 * arity t + 3) + 1 + (arity t + 1)) +
        (2 * arity t + 2) +
        (2 * (a.val * arity t) +
          5 * (tokens (List.ofFn (flatten edges))).length +
          arity t * (3 * vertex.val + 6) + arity t + 6) + 5,
      ∃ c',
      ((advance (program ι))^[total])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          startControl, W⟩ : TM2.Cfg (fun _ : J => Bool) _ _) =
        ⟨none, c', Function.update W (ι 9)
          (List.replicate (position (le_paddedEdgeCount e) edges a vertex).val true)⟩ := by
  obtain ⟨total, htime, c', hrun⟩ :=
    physical_position ι W edges a vertex h0 h1 h2 h3
      (hempty 4 (by omega)) (hempty 5 (by omega))
      (hempty 6 (by omega)) (hempty 7 (by omega))
      (hempty 8 (by omega)) (hempty 9 (by omega))
      (hempty 10 (by omega)) (hempty 11 (by omega))
      (hempty 12 (by omega))
  refine ⟨total, htime, c', ?_⟩
  simpa only [canonical_position_eq_padded] using hrun

#print axioms canonical_position_eq_padded
#print axioms physical_canonical_position

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
