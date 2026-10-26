import Paper2.E6RedClock3
import Paper2.E4Front
import Paper2.E5Budget
-- a-eth-owner-6 copy of frozen a-eth-owner-5/E5Red.lean (SHA-256 3dc1f9bf1211cf99903dbc7a06f7b552c3d565566458d4143985d29e0238a4a4); import lines renamed only.

/-! a-eth-owner-5 copy of frozen `a-eth-owner-4/E4Red.lean` (SHA-256 8590f0e8ca7040c2349c8e00adc92d70b2bf7b398d94ab2d83909f2e9be87a85). Changes: import lines renamed E4Budget/E4Red/E4Hd/E4Size -> E5Budget/E5Red/E5Hd/E5Size; nothing else. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 4 (partial): the reduction stage on EVERY word

ONE fixed machine `redMachine4 K N₁ = frontCut4 K N₁ ; MF ; GS` (segment 3's total front cut, then the
ADMITTED raw-suffix T24 front and the ADMITTED graph stage exactly as in a-eth-owner-3 `redMachine`).
`red4_outputs`: on `pair w t` for EVERY word `w`, it prints the selected T24 output at `k = kOf N'` of the
ROUTED formula `Φ' = routed4 K N₁ w` for the typed tape `t'` with `tapeBits t' = t.take inputBits`, within
`redTime4 w` (never in `|t|`), under the side conditions of a-eth-owner-3 `red_outputs2`.
`red4_outputs_all`: for `N₁` above one cutoff, every side condition is discharged for EVERY word `w` and
every tape of at least `2^(e0 (|w| + phiLen N₁) + 7)` bits (segment 2's fit; no monotonicity needed).
No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth4

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.AEth3 (MF CF EF GS cut0 checks_of_large nbOf PBof stageOf cutClock_eq cutClockN_mono
  gl inputBits_fit cutLen cutLen_eq cutLen_ge fOut)

/-- The routed formula as a valid formula. -/
def routedV (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) : ValidFormula :=
  ⟨routed4 K N₁ w, routed4_valid K hN₁ w⟩

/-- The routed word is never longer than the input plus the two fixed formulas. -/
theorem routed4_encode_length (K : ℕ) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) (w : List Bool) :
    (EncodedCNF.encode (routed4 K N₁ w)).length ≤ w.length + phiLen N₁ := by
  rw [← route3Out_eq]
  have h1 := Front.scanTarget_length hN₁ (Select.selWord (AFront.Sparse.sparseAnswer K w) w)
  have h2 := selWord_length (AFront.Sparse.sparseAnswer K w) w
  unfold route3Out phiLen
  omega

/-- **The cut request of the routed formula fits, for EVERY word.** -/
theorem cut4_fit (K : ℕ) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) (w : List Bool) :
    cutLen (routed4 K N₁ w) ≤ 2 ^ (e0 (w.length + phiLen N₁) + 7) := by
  rw [cutLen_eq]
  set m := w.length + phiLen N₁
  have hE := routed4_encode_length K hN₁ w
  have hNv := Paper2.AEth.encode_length_ge (routed4 K N₁ w)
  have h1 := lin_fit m
  have h2 := expLen_fit (routed4 K N₁ w).variables m (by omega)
  have h6 : 2 ^ (e0 m + 6) = 4 * 2 ^ (e0 m + 4) := by rw [pow_add, pow_add]; ring
  have h7 : 2 ^ (e0 m + 7) = 8 * 2 ^ (e0 m + 4) := by rw [pow_add, pow_add]; ring
  omega

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- THE fixed reduction machine on every word. -/
def redMachine4 (K N₁ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (frontCut4 K N₁)
    (BitMachineComposition.composition (MF D B) (GS D B))

/-- The additive reduction clock (a-eth-owner-3 `redTime2` with the total front). -/
def redTime4 (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) : ℕ :=
  frontTime4 K N₁ w +
    2 * (2 * (EncodedCNF.encode (routedV K N₁ hN₁ w).val).length + 1 +
      cutLen (routedV K N₁ hN₁ w).val) + 2 +
    (CF D B * (2 * (EncodedCNF.encode (routedV K N₁ hN₁ w).val).length + 1 +
        cutLen (routedV K N₁ hN₁ w).val + 1) ^ EF D B +
      2 * nbOf D B (routedV K N₁ hN₁ w) + 2 + stageOf D B (routedV K N₁ hN₁ w))

/-- **The reduction stage on EVERY word** (the side conditions of a-eth-owner-3 `red_outputs2`). -/
theorem red4_outputs (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool)
    (hk : 1 ≤ kOf (routedV K N₁ hN₁ w).val.variables)
    (hN : cut0 D B ≤ (routedV K N₁ hN₁ w).val.variables) (t : List Bool)
    (hI1 : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
        (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
          (t10Graph_valid D B (routedV K N₁ hN₁ w)))
        B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).inputBits ≤
          cutLen (routedV K N₁ hN₁ w).val)
    (hI2 : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
        (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
          (t10Graph_valid D B (routedV K N₁ hN₁ w)))
        B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).inputBits ≤
          t.length) :
    ∃ t' : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
        (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
          (t10Graph_valid D B (routedV K N₁ hN₁ w)))
        B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).Tape,
      (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
        (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
          (t10Graph_valid D B (routedV K N₁ hN₁ w)))
        B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).tapeBits t' =
        t.take (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
          (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
            (t10Graph_valid D B (routedV K N₁ hN₁ w)))
          B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).inputBits ∧
      (redMachine4 D B K N₁).OutputsWithin (EncodedComplexity.pair w t)
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B (routedV K N₁ hN₁ w))
          (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
            (t10Graph_valid D B (routedV K N₁ hN₁ w)))
          B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables) t')
        (redTime4 D B K N₁ hN₁ w) := by
  set Φ := routedV K N₁ hN₁ w with hΦ
  set I := (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables)).inputBits with hIdef
  set c := t.take (cutLen Φ.val) with hc
  have hclen : c.length ≤ cutLen Φ.val := List.length_take_le _ _
  have hIc : I ≤ c.length := by
    rw [hc, List.length_take]; exact le_min hI1 hI2
  obtain ⟨hm, -, hinc, hdeg, -⟩ := t10_source D B Φ
  have hch := checks_of_large D B Φ hN
  obtain ⟨t', ht', hrun⟩ := Paper2.ABridge.graph_stage_outputs B.degreeBound (sourceGap D B)
    B.degreeBound_pos (source_gap_pos D B) (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (t10_vertices_pos D B Φ) hm (kOf Φ.val.variables) hk hinc hdeg hch c hIc
  have htake : c.take I = t.take I := by
    rw [hc, List.take_take, Nat.min_eq_left hI1]
  refine ⟨t', ht'.trans htake, ?_⟩
  have hH : A3Assembly.Run.Hyp B.degreeBound (t10Graph D B Φ) (t10Graph_valid D B Φ)
      (kOf Φ.val.variables) := ⟨hk, hinc, hdeg⟩
  have hbw := Paper2.ABridge.bank3_length (t10Graph D B Φ) (kOf Φ.val.variables) c
  have hnb : 2 * ((EncodedGraph.encode (t10Graph D B Φ)).length + kOf Φ.val.variables +
      c.length) + 3 ≤ nbOf D B Φ := by
    unfold nbOf gl; omega
  have hP := Paper2.ABridge.packetBd_graph_le B.degreeBound (sourceGap D B) (source_gap_pos D B)
    B.degreeBound_pos (t10Graph D B Φ) (t10Graph_valid D B Φ) (t10_vertices_pos D B Φ) hm
    (kOf Φ.val.variables) hH hch c
  have hPB : Paper2.ABridge.packetBd (sourceGap D B).num.toNat (sourceGap D B).den B.degreeBound
      (t10Graph D B Φ) (kOf Φ.val.variables) c ≤ PBof D B Φ := by
    refine hP.trans (Nat.add_le_add le_rfl ?_)
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 26 hclen)
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hclen))) 7
  have hstage : Paper2.ABridge.stageClock B.degreeBound (sourceGap D B) B.degreeBound_pos
      (source_gap_pos D B) (t10Graph D B Φ) (kOf Φ.val.variables) c ≤ stageOf D B Φ := by
    unfold Paper2.ABridge.stageClock stageOf
    rw [cutClock_eq, hbw]
    exact add_le_add (add_le_add (add_le_add (cutClockN_mono hnb hPB)
      (Nat.mul_le_mul_left 2 hnb)) le_rfl) le_rfl
  have h3 := BitMachine.outputsWithin_mono _ hrun hstage
  have h1 := frontCut4_outputs K N₁ hN₁ w t
  have h2 := Paper2.AEth3.MF_runs D B Φ c
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2 h3)
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hpw : (EncodedComplexity.pair (EncodedCNF.encode Φ.val) c).length ≤
      2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val := by
    rw [EncodedComplexity.pair_length]; omega
  have hCF : CF D B * ((EncodedComplexity.pair (EncodedCNF.encode Φ.val) c).length + 1) ^ EF D B ≤
      CF D B * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val + 1) ^ EF D B :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hpw 1) _)
  have hbank : (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
      List.replicate (kOf Φ.val.variables) true, c]).length ≤ nbOf D B Φ := by
    rw [hbw]; exact hnb
  unfold redTime4
  exact add_le_add (add_le_add (add_le_add le_rfl (Nat.mul_le_mul_left 2 hpw)) le_rfl)
    (add_le_add (add_le_add (add_le_add hCF (Nat.mul_le_mul_left 2 hbank)) le_rfl) le_rfl)

/-- **All side conditions discharged for EVERY word.** For every density `K` there is `N₀` such that
for every threshold `N₁ ≥ N₀` with `2 ≤ K·N₁`, every word `w` and every tape `t` with at least
`2^(e0 (|w| + phiLen N₁) + 7)` bits, the conclusion of `red4_outputs` holds. -/
theorem red4_outputs_all (K : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N₁ (hN₁ : 1 ≤ N₁), N₀ ≤ N₁ → 2 ≤ K * N₁ →
      ∀ (w t : List Bool), 2 ^ (e0 (w.length + phiLen N₁) + 7) ≤ t.length →
      1 ≤ kOf (routedV K N₁ hN₁ w).val.variables ∧
      ∃ t' : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
          (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
            (t10Graph_valid D B (routedV K N₁ hN₁ w)))
          B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).Tape,
        (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
          (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
            (t10Graph_valid D B (routedV K N₁ hN₁ w)))
          B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).tapeBits t' =
          t.take (TotalFiniteConstructorScratch.select (t10_vertices_pos D B (routedV K N₁ hN₁ w))
            (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
              (t10Graph_valid D B (routedV K N₁ hN₁ w)))
            B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables)).inputBits ∧
        (redMachine4 D B K N₁).OutputsWithin (EncodedComplexity.pair w t)
          (EncodedSelectedOutput.outputBits (t10_vertices_pos D B (routedV K N₁ hN₁ w))
            (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
              (t10Graph_valid D B (routedV K N₁ hN₁ w)))
            B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables) t')
          (redTime4 D B K N₁ hN₁ w) := by
  obtain ⟨N₂, hN₂⟩ := inputBits_fit D B K
  refine ⟨max 1 (max N₂ (cut0 D B)), le_max_left _ _, ?_⟩
  intro N₁ hN₁ hle hK w t ht
  have hvars : N₁ ≤ (routedV K N₁ hN₁ w).val.variables := routed4_variables K N₁ w
  have hsp : (routedV K N₁ hN₁ w).val.clauses.length ≤
      K * (routedV K N₁ hN₁ w).val.variables := routed4_sparse K N₁ hK w
  have hN2 : N₂ ≤ (routedV K N₁ hN₁ w).val.variables := by
    have : N₂ ≤ max 1 (max N₂ (cut0 D B)) := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hN3 : cut0 D B ≤ (routedV K N₁ hN₁ w).val.variables := by
    have : cut0 D B ≤ max 1 (max N₂ (cut0 D B)) := le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  obtain ⟨hk, hI⟩ := hN₂ (routedV K N₁ hN₁ w) hsp hN2
  have hge := cutLen_ge (routedV K N₁ hN₁ w).val
  have hfit := cut4_fit K hN₁ w
  exact ⟨hk, red4_outputs D B K N₁ hN₁ w hk hN3 t (by omega) (by
    have : cutLen (routedV K N₁ hN₁ w).val = cutLen (routed4 K N₁ w) := rfl
    omega)⟩

end Paper2.AEth4

end

#print axioms Paper2.AEth4.routed4_encode_length
#print axioms Paper2.AEth4.cut4_fit
#print axioms Paper2.AEth4.red4_outputs
#print axioms Paper2.AEth4.red4_outputs_all
