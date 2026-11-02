import Paper2.E6Clock3
import Paper2.BrGlobal
import Paper2.PublicScheduleSourceSize
-- a-eth-owner-6 copy of frozen a-eth-owner-3/E3Red.lean (SHA-256 9441e025a153d1146072a2c13c86c68ae97f06e1ccdf8814991a99ba31dc2e4c); import lines renamed only.

/-!
# Paper A (lock v12), lane `owner:a-eth-3`, segment 1 (obstacle B2): the cut stage hands the
# growing-gap reduction exactly `inputBits` bits

ONE fixed machine `redMachine = frontCut ; MF ; graphStageMachine`:
* `frontCut` (E3Inner): `pair (encode Φ) t ↦ pair (encode Φ) (t.take (cutLen Φ))`, clock free of `t`;
* `MF`: the machine of the ADMITTED raw-suffix T24 front `KofFront.front_T24_raw` (it COMPUTES
  `kOf N`): `pair (encode Φ) w ↦ encode ![encode (t10Graph Φ), 1^(kOf N), w]` for EVERY raw `w`;
* `graphStageMachine` (ADMITTED `Paper2.ABridge`, lane a-bridge-owner-1, A20): the admitted cut
  machine (retains exactly `w.take inputBits`, identified with the selected input-bit count by the
  admitted `FrontPreparedCut.frontD_eq_selected_inputBits`) followed by the ADMITTED
  `A3Close.H_A3_closed` machine.

`red_outputs`: for every valid `Φ` with `1 ≤ kOf N` and `N ≥ cut0` (so the admitted public schedule
checks hold, `checks_of_large`), and every tape `t` with `inputBits ≤ |t|` and
`inputBits ≤ cutLen Φ`, the machine prints exactly `outputBits … (kOf N) t'` for the typed selected
tape `t'` with `tapeBits t' = t.take inputBits`, within `redTime Φ`, a bound in `|encode Φ|`, `N`,
`kOf N` and the graph only (never in `|t|`). `red_outputs_sparse` discharges the two length side
conditions for sparse valid `Φ` with `N` large and any tape of at least `expLen N` bits.

This is the handoff only: the reduction stage's D-A6 clock bound (`redTime ≤ C⌈2^(εN)⌉(|x|+1)^d`)
is NOT stated here, and `redTime` is TOO LOSSY for it: it uses the admitted merged bound
`ABridge.stageClock_le` (`gC k · (|encode g| + |word| + 1)^(gE k)`, `gE k = Θ(k)`), whose word term is
`(expLen N)^Θ(kOf N)`, super-exponential in `N`. The D-A6 bound needs the additive form of the stage
clock (admitted `BrPoly.packetBd_graph_le` separates `(|encode g|+1)^(ePk·(k+1))` from a term linear
in `|word|`); not done here. No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth3

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The admitted raw-suffix T24 front machine and its constants. -/
def MF : BitMachine.Machine := Classical.choose (Paper2.Unit4Shell.KofFront.front_T24_raw D B)
def CF : ℕ := Classical.choose (Classical.choose_spec (Paper2.Unit4Shell.KofFront.front_T24_raw D B))
def EF : ℕ := Classical.choose (Classical.choose_spec (Classical.choose_spec
  (Paper2.Unit4Shell.KofFront.front_T24_raw D B)))

theorem MF_runs (Φ : ValidFormula) (tb : List Bool) :
    (MF D B).OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) tb)
      (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
        List.replicate (kOf Φ.val.variables) true, tb])
      (CF D B * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val) tb).length + 1) ^ EF D B) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Paper2.Unit4Shell.KofFront.front_T24_raw D B))) Φ tb

/-- The admitted graph stage at the source parameters. -/
def GS : BitMachine.Machine :=
  Paper2.ABridge.graphStageMachine B.degreeBound (sourceGap D B) B.degreeBound_pos
    (source_gap_pos D B)

/-- THE fixed reduction machine of the growing-gap decider (front cut, T24 front, graph stage). -/
def redMachine : BitMachine.Machine :=
  BitMachineComposition.composition frontCut
    (BitMachineComposition.composition (MF D B) (GS D B))

/-- The variable cutoff above which the public schedule checks hold for the T10 graph. -/
def cut0 : ℕ := max 1 (B.degreeBound *
  Paper2.CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B))

/-- The admitted public schedule checks for the T10 graph of every valid `Φ` with `N ≥ cut0`
(the argument of the frozen `SourceImageGap.routed_checks`, for an unrouted formula). -/
theorem checks_of_large (Φ : ValidFormula) (hN : cut0 D B ≤ Φ.val.variables) :
    Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin (t10Graph D B Φ).vertices) (E := Fin (t10Graph D B Φ).edges.length)
      (Nat.clog 2 (t10Graph D B Φ).vertices) B.degreeBound (sourceGap D B) := by
  obtain ⟨hm, hNm, hinc, hdeg, _, _, _⟩ := t10_source D B Φ
  have h2m := (Paper2.Unit4Shell.T10Size.t45_relations D B Φ).2.1
  have hcut : B.degreeBound *
      Paper2.CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B) ≤
      cut0 D B := le_max_right _ _
  have hsize : Paper2.CompletePublicScheduleScratch.sizeThreshold B.degreeBound (sourceGap D B) ≤
      (t10Graph D B Φ).vertices := by
    by_contra h
    have hlt := Nat.lt_of_not_ge h
    have hmul := Nat.mul_lt_mul_of_pos_left hlt B.degreeBound_pos
    omega
  haveI : Nonempty (Fin (t10Graph D B Φ).vertices) := ⟨⟨0, t10_vertices_pos D B Φ⟩⟩
  have h := Paper2.CompletePublicScheduleScratch.all_large_checks_at_graph
    (V := Fin (t10Graph D B Φ).vertices) (E := Fin (t10Graph D B Φ).edges.length)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (source_gap_pos D B) B.degreeBound_pos hinc hdeg
    (by simpa only [Fintype.card_fin] using hsize)
  simpa only [Fintype.card_fin] using h

/-- Bank-word length is monotone in the length of the third field. -/
theorem bank_len_le (A C W : List Bool) (L : ℕ) (hW : W.length ≤ L) :
    (BitMachineBankCodec.encode ![A, C, W]).length ≤
      (BitMachineBankCodec.encode ![A, C, List.replicate L false]).length := by
  rw [BitMachineBankCodec.encode_length, BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, List.length_replicate]
  omega

/-- The reduction clock: in `|encode Φ|`, `N`, `kOf N` and the T10 graph only. -/
def redTime (Φ : ValidFormula) : ℕ :=
  frontTime Φ.val + 2 * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val) + 2 +
    (CF D B * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val + 1) ^ EF D B +
      2 * (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
        List.replicate (kOf Φ.val.variables) true,
        List.replicate (cutLen Φ.val) false]).length + 2 +
      Paper2.ABridge.gC B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B)
          (kOf Φ.val.variables) *
        ((EncodedGraph.encode (t10Graph D B Φ)).length + cutLen Φ.val + 1) ^
          Paper2.ABridge.gE B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B)
            (kOf Φ.val.variables))

/-- **The handoff.** ONE fixed machine; for every valid `Φ` with `1 ≤ kOf N`, `N ≥ cut0`, and
every tape `t` at least `inputBits` long with `inputBits ≤ cutLen Φ`: it prints exactly the
selected output bits at `k = kOf N` of the typed tape whose bits are `t.take inputBits`, within
`redTime Φ` (independent of `t`). -/
theorem red_outputs (Φ : ValidFormula) (hk : 1 ≤ kOf Φ.val.variables)
    (hN : cut0 D B ≤ Φ.val.variables) (t : List Bool)
    (hI1 : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits ≤ cutLen Φ.val)
    (hI2 : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits ≤ t.length) :
    ∃ t' : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).Tape,
      (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
        (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
        B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeBits t' =
        t.take (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits ∧
      (redMachine D B).OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) t)
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t')
        (redTime D B Φ) := by
  set I := (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits with hIdef
  set w := t.take (cutLen Φ.val) with hw
  have hwlen : w.length ≤ cutLen Φ.val := List.length_take_le _ _
  have hIw : I ≤ w.length := by
    rw [hw, List.length_take]; exact le_min hI1 hI2
  obtain ⟨hm, -, hinc, hdeg, -⟩ := t10_source D B Φ
  have hc := checks_of_large D B Φ hN
  obtain ⟨t', ht', hrun⟩ := Paper2.ABridge.graph_stage_outputs B.degreeBound (sourceGap D B)
    B.degreeBound_pos (source_gap_pos D B) (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (t10_vertices_pos D B Φ) hm (kOf Φ.val.variables) hk hinc hdeg hc w hIw
  have htake : w.take I = t.take I := by
    rw [hw, List.take_take, Nat.min_eq_left hI1]
  refine ⟨t', ht'.trans htake, ?_⟩
  have hH : A3Assembly.Run.Hyp B.degreeBound (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (kOf Φ.val.variables) := ⟨hk, hinc, hdeg⟩
  have hclk := Paper2.ABridge.stageClock_le B.degreeBound (sourceGap D B) B.degreeBound_pos
    (source_gap_pos D B) (t10Graph D B Φ) (t10Graph_valid D B Φ) (t10_vertices_pos D B Φ) hm
    (kOf Φ.val.variables) hH hc w
  have h3 := BitMachine.outputsWithin_mono _ hrun hclk
  have h1 := frontCut_outputs Φ.val t
  have h2 := MF_runs D B Φ w
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2 h3)
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hb := bank_len_le (EncodedGraph.encode (t10Graph D B Φ))
    (List.replicate (kOf Φ.val.variables) true) w (cutLen Φ.val) hwlen
  have hpw : (EncodedComplexity.pair (EncodedCNF.encode Φ.val) w).length ≤
      2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val := by
    rw [EncodedComplexity.pair_length]; omega
  have hCF : CF D B * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val) w).length + 1) ^ EF D B ≤
      CF D B * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val + 1) ^ EF D B :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hpw 1) _)
  have hG : Paper2.ABridge.gC B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B)
        (kOf Φ.val.variables) *
      ((EncodedGraph.encode (t10Graph D B Φ)).length + w.length + 1) ^
        Paper2.ABridge.gE B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B)
          (kOf Φ.val.variables) ≤
      Paper2.ABridge.gC B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B)
        (kOf Φ.val.variables) *
      ((EncodedGraph.encode (t10Graph D B Φ)).length + cutLen Φ.val + 1) ^
        Paper2.ABridge.gE B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B)
          (kOf Φ.val.variables) := by
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add_left hwlen _) 1) _)
  unfold redTime
  exact add_le_add (add_le_add (add_le_add le_rfl (Nat.mul_le_mul_left 2 hpw)) le_rfl)
    (add_le_add (add_le_add (add_le_add hCF (Nat.mul_le_mul_left 2 hb)) le_rfl) hG)

/-- **The handoff on sparse inputs.** For every density `cs` there is `N₀` such that for every
sparse valid `Φ` with `N ≥ N₀` and every tape `t` with at least `expLen N` bits, the conclusion
of `red_outputs` holds (the side conditions are discharged by `inputBits_fit`, `cutLen_ge`). -/
theorem red_outputs_sparse (cs : ℕ) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs * Φ.val.variables →
      N₀ ≤ Φ.val.variables → ∀ t : List Bool, Paper2.AEth.expLen Φ.val.variables ≤ t.length →
      ∃ t' : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).Tape,
        (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).tapeBits t' =
          t.take (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits ∧
        (redMachine D B).OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) t)
          (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
            (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
            B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t')
          (redTime D B Φ) := by
  obtain ⟨N₁, hN₁⟩ := inputBits_fit D B cs
  refine ⟨max N₁ (cut0 D B), fun Φ hsp hN t ht => ?_⟩
  obtain ⟨hk, hI⟩ := hN₁ Φ hsp (le_trans (le_max_left _ _) hN)
  have hge := cutLen_ge Φ.val
  exact red_outputs D B Φ hk (le_trans (le_max_right _ _) hN) t (by omega) (by omega)

end Paper2.AEth3

#print axioms Paper2.AEth3.checks_of_large
#print axioms Paper2.AEth3.bank_len_le
#print axioms Paper2.AEth3.red_outputs
#print axioms Paper2.AEth3.red_outputs_sparse
