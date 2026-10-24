import Paper2.AFrontRoute
import Paper2.A4FrontClosed

/-!
# The all-input T10 front: malformed and trivially decided inputs go to fixed graphs
# (lane `owner:a-front-1`)

Private lane module, 27 September 2026. Paper A, lock v12, decisions D-A1, D-A2, D-A7
(`AUTHOR_DECISIONS_2026-09-27.md`: the cited Dinur/BOT records `D`, `B` are Paper B's records,
parameters here).

Lock text: v12 `appendices/C-parameters.tex:204-206` (proof of `src:gap-colouring`, row T10):
"Empty or trivially decided input formulas can be sent directly to fixed YES or NO graphs.
Every step is polynomial-time."

* `phiGraph D B hN b = t10Graph D B ⟨phiFormula N b, _⟩` is a FIXED graph (it depends only on
  `N`, `b` and the records). `phiGraph_yes`: for `b = true` it is three-colourable;
  `phiGraph_no`: for `b = false` every three-colouring has at least `γ·|E|` monochromatic edges.
* `T10_all_input`: for every `k` there is ONE fixed machine which on EVERY `pair w tape`
  (tape of the selected law of the routed graph) prints the literal H-A3 bank of the routed
  graph `t10Graph D B (routed hN w)`, in polynomial time; the routed graph is the fixed NO graph
  on malformed `w`, the fixed YES/NO graph `phiGraph (satAnswer w)` on valid `w` with fewer than
  `N` variables, and the T10 graph of `w` itself otherwise (`routed_*`).

The machine is `composition (frontRoute N) MF` where `MF` is the admitted T10 front of
`FrontClosed.H_T10Front_holds D B k` (every handoff charged). No ledger row is closed.
-/

namespace AFront.T10

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCNF
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite
open AFront.Route
open Paper2

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The routed valid formula. -/
noncomputable def routed {N : ℕ} (hN : 1 ≤ N) (w : List Bool) : ValidFormula :=
  ⟨routedFormula N w, routedFormula_valid hN w⟩

/-- The fixed canonical formula as a valid formula. -/
def phiValid {N : ℕ} (hN : 1 ≤ N) (b : Bool) : ValidFormula :=
  ⟨Front.phiFormula N b, Front.phiFormula_valid hN b⟩

/-- The fixed YES (`b = true`) / NO (`b = false`) graph. -/
noncomputable def phiGraph {N : ℕ} (hN : 1 ≤ N) (b : Bool) : EncodedGraph.Graph :=
  t10Graph D B (phiValid hN b)

theorem phiGraph_yes {N : ℕ} (hN : 1 ≤ N) :
    FiniteFallbackOutput.ThreeColourable
      (CanonicalEdgeTape.graphEdge (phiGraph D B hN true) (t10Graph_valid D B (phiValid hN true))) :=
  (t10_source D B (phiValid hN true)).2.2.2.2.2.1 ((Front.phiFormula_sat true).mpr rfl)

theorem phiGraph_no {N : ℕ} (hN : 1 ≤ N) :
    ∀ colour : Fin (phiGraph D B hN false).vertices → Fin 3,
      ((sourceGap D B : ℚ) : ℝ) * (phiGraph D B hN false).edges.length ≤
        ((Finset.univ.filter (fun e =>
          colour (CanonicalEdgeTape.graphEdge (phiGraph D B hN false)
            (t10Graph_valid D B (phiValid hN false)) e false) =
          colour (CanonicalEdgeTape.graphEdge (phiGraph D B hN false)
            (t10Graph_valid D B (phiValid hN false)) e true))).card : ℝ) :=
  (t10_source D B (phiValid hN false)).2.2.2.2.2.2
    (fun h => by simpa using (Front.phiFormula_sat (N := N) false).mp h)

theorem routed_malformed {N : ℕ} (hN : 1 ≤ N) {w : List Bool} (h : EncodedCNF.decode w = none) :
    routed hN w = phiValid hN false := by
  apply Subtype.ext
  simp [routed, phiValid, routedFormula, h]

theorem routed_small {N : ℕ} (hN : 1 ≤ N) {w : List Bool} {f : Formula}
    (h : EncodedCNF.decode w = some f) (hs : f.variables < N) :
    routed hN w = phiValid hN (EncodedETHTail.satAnswer w) := by
  apply Subtype.ext
  simp [routed, phiValid, routedFormula, h, hs]

theorem routed_large {N : ℕ} (hN : 1 ≤ N) {w : List Bool} {f : Formula}
    (h : EncodedCNF.decode w = some f) (hl : N ≤ f.variables) :
    (routed hN w).val = f := by
  simp [routed, routedFormula, h, Nat.not_lt.mpr hl]

private theorem budget (X m K CF EF T1 : ℕ) (hm : m ≤ X + 2 * K)
    (hT1 : T1 ≤ (300 + 2 * K) * (X + 1) ^ 3) :
    T1 + 2 * m + 2 + CF * (m + 1) ^ EF ≤
      ((300 + 2 * K) + 2 * (1 + 2 * K) + 2 + CF * (1 + 2 * K) ^ EF) * (X + 1) ^ (3 + EF) := by
  have h1 : 1 ≤ (X + 1) ^ EF := Nat.one_le_pow _ _ (by omega)
  have h3 : (X + 1) ^ 3 ≤ (X + 1) ^ (3 + EF) := Nat.pow_le_pow_right (by omega) (by omega)
  have hX : X + 1 ≤ (X + 1) ^ (3 + EF) := by
    calc X + 1 = (X + 1) ^ 1 := (pow_one _).symm
      _ ≤ (X + 1) ^ (3 + EF) := Nat.pow_le_pow_right (by omega) (by omega)
  have hm1 : m + 1 ≤ (1 + 2 * K) * (X + 1) := by nlinarith
  have hpow : (m + 1) ^ EF ≤ (1 + 2 * K) ^ EF * (X + 1) ^ (3 + EF) := by
    calc (m + 1) ^ EF ≤ ((1 + 2 * K) * (X + 1)) ^ EF := Nat.pow_le_pow_left hm1 EF
      _ = (1 + 2 * K) ^ EF * (X + 1) ^ EF := by rw [mul_pow]
      _ ≤ (1 + 2 * K) ^ EF * (X + 1) ^ (3 + EF) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
  have hA : T1 ≤ (300 + 2 * K) * (X + 1) ^ (3 + EF) := hT1.trans (Nat.mul_le_mul_left _ h3)
  have hB : 2 * m + 2 ≤ (2 * (1 + 2 * K) + 2) * (X + 1) ^ (3 + EF) := by nlinarith
  have hC : CF * (m + 1) ^ EF ≤ CF * (1 + 2 * K) ^ EF * (X + 1) ^ (3 + EF) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hpow
  have hexp : ((300 + 2 * K) + 2 * (1 + 2 * K) + 2 + CF * (1 + 2 * K) ^ EF) * (X + 1) ^ (3 + EF) =
      (300 + 2 * K) * (X + 1) ^ (3 + EF) + (2 * (1 + 2 * K) + 2) * (X + 1) ^ (3 + EF) +
        CF * (1 + 2 * K) ^ EF * (X + 1) ^ (3 + EF) := by ring
  rw [hexp]
  omega

/-- **The all-input T10 front (C-parameters.tex:204-206).** For every `N ≥ 1` and `k`, ONE fixed
machine prints on EVERY `pair w (tapeBits t)` the literal H-A3 bank of the routed graph, within
`C·(|input|+1)^E`. -/
theorem T10_all_input {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    ∃ (M : BitMachine.Machine) (C E : ℕ), ∀ (w : List Bool)
      (t : (Paper2.TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routed hN w))
        (CanonicalEdgeTape.graphEdge (t10Graph D B (routed hN w)) (t10Graph_valid D B (routed hN w)))
        B.degreeBound (sourceGap D B) k).Tape),
      M.OutputsWithin
        (EncodedComplexity.pair w ((Paper2.TotalFiniteConstructorScratch.select
          (t10_vertices_pos D B (routed hN w))
          (CanonicalEdgeTape.graphEdge (t10Graph D B (routed hN w)) (t10Graph_valid D B (routed hN w)))
          B.degreeBound (sourceGap D B) k).tapeBits t))
        (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B (routed hN w)),
          List.replicate k true,
          (Paper2.TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routed hN w))
            (CanonicalEdgeTape.graphEdge (t10Graph D B (routed hN w)) (t10Graph_valid D B (routed hN w)))
            B.degreeBound (sourceGap D B) k).tapeBits t])
        (C * ((EncodedComplexity.pair w ((Paper2.TotalFiniteConstructorScratch.select
          (t10_vertices_pos D B (routed hN w))
          (CanonicalEdgeTape.graphEdge (t10Graph D B (routed hN w)) (t10Graph_valid D B (routed hN w)))
          B.degreeBound (sourceGap D B) k).tapeBits t)).length + 1) ^ E) := by
  obtain ⟨MF, CF, EF, hMF⟩ := Paper2.Unit4Shell.FrontClosed.H_T10Front_holds D B k
  set K := (Front.phi N true).length + (Front.phi N false).length
  refine ⟨BitMachineComposition.composition (frontRoute N) MF,
    (300 + 2 * K) + 2 * (1 + 2 * K) + 2 + CF * (1 + 2 * K) ^ EF, 3 + EF, ?_⟩
  intro w t
  set tape := (Paper2.TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routed hN w))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (routed hN w)) (t10Graph_valid D B (routed hN w)))
    B.degreeBound (sourceGap D B) k).tapeBits t
  have h1 := frontRoute_outputs_poly hN w tape
  have heq : Front.scanTarget N w = EncodedCNF.encode (routed hN w).val := scanTarget_eq_encode N w
  rw [heq] at h1
  have h2 := hMF (routed hN w) t
  have hc := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  apply BitMachine.outputsWithin_mono _ hc
  have hs := Front.scanTarget_length hN w
  rw [heq] at hs
  have hX := EncodedComplexity.pair_length w tape
  have hY := EncodedComplexity.pair_length (EncodedCNF.encode (routed hN w).val) tape
  exact budget _ _ K CF EF _ (by omega) le_rfl

#print axioms phiGraph_yes
#print axioms phiGraph_no
#print axioms routed_malformed
#print axioms routed_small
#print axioms routed_large
#print axioms T10_all_input

end AFront.T10
