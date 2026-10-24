import Paper2.E6Red3
-- a-eth-owner-6 copy of frozen a-eth-owner-3/E3RedClock.lean (SHA-256 28e2cd6fb94780a077c77e87813bb2afbd91c43ca985e2e8044ba0e5673163fd); import lines renamed only.

/-!
# Paper A (lock v12), lane `owner:a-eth-3`, segment 1 (obstacle B2): the reduction stage with an
# ADDITIVE clock

`E3Red.red_outputs` charges the admitted graph stage by the merged admitted bound
`ABridge.stageClock_le`, which multiplies the word length into a `k`-dependent power. Here the SAME
machine `redMachine` is charged by the admitted stage clock `ABridge.stageClock` itself, with the
admitted packet bound `ABridge.packetBd_graph_le` (which keeps `(|encode g|+1)^(ePk·(k+1))` and the
word-linear term apart). The resulting clock `redTime2 Φ` depends on `|encode Φ|`, `N`, `kOf N` and the
T10 graph only, and is ADDITIVE in the cut length: no power of the cut length carries `k`.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth3

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics

/-- The admitted cut-machine clock as a function of the bank length `nb` and the packet clock `P`. -/
def cutClockN (a b Δ nb P : ℕ) : ℕ :=
  (Paper2.ABridge.nJ + 3 + 1) + 2 * (Paper2.ABridge.nJ + 3 + nb) + 2 +
    (((2 * (Paper2.ABridge.nJ + 3 + 3) + 1) * ((Paper2.ABridge.nJ + 3 + nb) + 1) +
      Paper2.ABridge.cutBdN a b Δ nb P + 2 * (nb + (Paper2.ABridge.nJ + 3)) + 4) +
     2 * (nb + (Paper2.ABridge.nJ + 3)) + 2 + (2 * nb + 2 * (Paper2.ABridge.nJ + 3) + 3))

theorem cutClock_eq (a b Δ : ℕ) (g : EncodedGraph.Graph) (k : ℕ) (word : List Bool) :
    Paper2.ABridge.cutClock a b Δ g k word =
      cutClockN a b Δ
        (BitMachineBankCodec.encode ![EncodedGraph.encode g, List.replicate k true, word]).length
        (Paper2.ABridge.packetBd a b Δ g k word) := rfl

theorem cutClockN_mono {a b Δ nb P nb' P' : ℕ} (h1 : nb ≤ nb') (h2 : P ≤ P') :
    cutClockN a b Δ nb P ≤ cutClockN a b Δ nb' P' := by
  unfold cutClockN Paper2.ABridge.cutBdN Paper2.ABridge.clearBd
  gcongr

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- Graph-encoding length of the T10 graph. -/
def gl (Φ : ValidFormula) : ℕ := (EncodedGraph.encode (t10Graph D B Φ)).length

/-- Bank-length bound at the cut length. -/
def nbOf (Φ : ValidFormula) : ℕ := 2 * (gl D B Φ + kOf Φ.val.variables + cutLen Φ.val) + 3

/-- Packet-clock bound at the cut length (admitted `packetBd_graph_le` shape). -/
def PBof (Φ : ValidFormula) : ℕ :=
  (2 + Paper2.ABridge.prepConst) * (gl D B Φ + 1) ^
      (Paper2.ABridge.ePk B.degreeBound (sourceGap D B) * (kOf Φ.val.variables + 1)) +
    (26 * cutLen Φ.val + 2 * (cutLen Φ.val * Paper2.ABridge.cutPS) + 7)

/-- The additive graph-stage bound. -/
def stageOf (Φ : ValidFormula) : ℕ :=
  cutClockN (sourceGap D B).num.toNat (sourceGap D B).den B.degreeBound (nbOf D B Φ) (PBof D B Φ) +
    2 * nbOf D B Φ + 2 +
    Paper2.ABridge.stageCA B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B) *
      ((t10Graph D B Φ).vertices + 2) ^
        (Paper2.ABridge.stageEA B.degreeBound (sourceGap D B) B.degreeBound_pos (source_gap_pos D B) *
          (kOf Φ.val.variables + 1))

/-- The additive reduction clock. -/
def redTime2 (Φ : ValidFormula) : ℕ :=
  frontTime Φ.val + 2 * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val) + 2 +
    (CF D B * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val + 1) ^ EF D B +
      2 * nbOf D B Φ + 2 + stageOf D B Φ)

/-- **The handoff with the additive clock.** Same machine and hypotheses as `red_outputs`;
clock `redTime2 Φ` (independent of `t`). -/
theorem red_outputs2 (Φ : ValidFormula) (hk : 1 ≤ kOf Φ.val.variables)
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
        (redTime2 D B Φ) := by
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
  have hbw := Paper2.ABridge.bank3_length (t10Graph D B Φ) (kOf Φ.val.variables) w
  have hnb : 2 * ((EncodedGraph.encode (t10Graph D B Φ)).length + kOf Φ.val.variables +
      w.length) + 3 ≤ nbOf D B Φ := by
    unfold nbOf gl; omega
  have hP := Paper2.ABridge.packetBd_graph_le B.degreeBound (sourceGap D B) (source_gap_pos D B)
    B.degreeBound_pos (t10Graph D B Φ) (t10Graph_valid D B Φ) (t10_vertices_pos D B Φ) hm
    (kOf Φ.val.variables) hH hc w
  have hPB : Paper2.ABridge.packetBd (sourceGap D B).num.toNat (sourceGap D B).den B.degreeBound
      (t10Graph D B Φ) (kOf Φ.val.variables) w ≤ PBof D B Φ := by
    refine hP.trans (Nat.add_le_add le_rfl ?_)
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 26 hwlen)
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hwlen))) 7
  have hstage : Paper2.ABridge.stageClock B.degreeBound (sourceGap D B) B.degreeBound_pos
      (source_gap_pos D B) (t10Graph D B Φ) (kOf Φ.val.variables) w ≤ stageOf D B Φ := by
    unfold Paper2.ABridge.stageClock stageOf
    rw [cutClock_eq, hbw]
    exact add_le_add (add_le_add (add_le_add (cutClockN_mono hnb hPB)
      (Nat.mul_le_mul_left 2 hnb)) le_rfl) le_rfl
  have h3 := BitMachine.outputsWithin_mono _ hrun hstage
  have h1 := frontCut_outputs Φ.val t
  have h2 := MF_runs D B Φ w
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2 h3)
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hpw : (EncodedComplexity.pair (EncodedCNF.encode Φ.val) w).length ≤
      2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val := by
    rw [EncodedComplexity.pair_length]; omega
  have hCF : CF D B * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val) w).length + 1) ^ EF D B ≤
      CF D B * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val + 1) ^ EF D B :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hpw 1) _)
  have hbank : (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
      List.replicate (kOf Φ.val.variables) true, w]).length ≤ nbOf D B Φ := by
    rw [hbw]; exact hnb
  unfold redTime2
  exact add_le_add (add_le_add (add_le_add le_rfl (Nat.mul_le_mul_left 2 hpw)) le_rfl)
    (add_le_add (add_le_add (add_le_add hCF (Nat.mul_le_mul_left 2 hbank)) le_rfl) le_rfl)

end Paper2.AEth3

#print axioms Paper2.AEth3.cutClock_eq
#print axioms Paper2.AEth3.cutClockN_mono
#print axioms Paper2.AEth3.red_outputs2
