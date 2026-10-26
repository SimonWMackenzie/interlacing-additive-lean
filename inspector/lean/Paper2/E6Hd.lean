import Paper2.E6Red
import Paper2.E4Head
import Paper2.PairConcat
-- a-eth-owner-6 copy of frozen a-eth-owner-5/E5Hd.lean (SHA-256 75a347be02483cc8d476027d728d279f2a64134f627a401051e123ae0c5e0327); import lines renamed only.

/-! a-eth-owner-5 copy of frozen `a-eth-owner-4/E4Hd.lean` (SHA-256 0fa6359f5a26a0f2ba721e8cd620dd1f3ad0e6f0fac98d7b27ecc3affb31f230). Changes: import lines renamed E4Budget/E4Red/E4Hd/E4Size -> E5Budget/E5Red/E5Hd/E5Size; nothing else. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 4 (partial, 4d): from `pair w t` to the header word at `k = kOf N'`

ONE fixed machine `hdMachine4 D B K N₁`:
`frontCut4 ; Pack ; PairMap (MF ; GS) ; Swap ; PairConcat ; KHeader`, where
* `Pack` (new, fixed): `pair e c ↦ pair (pair e c) (pair (field e) [])` (keeps a copy of the routed formula word);
* `PairMap (MF ; GS)`: the admitted T24 front and graph stage on the first field (a-eth-owner-3 wiring);
* `Swap` (admitted), `PairConcat` (admitted): `↦ pair e (outputBits …)`;
* `KHeader` (segment 1): `pair (encode f) (encodeInstance i) ↦ headeredWord (kOf f.variables) i`.
`hd4_outputs_all`: for EVERY word `w` and every tape `t` of at least `2^(e0 (|w| + phiLen N₁) + 7)` bits, the machine
prints `HeaderWordRun.headeredWord (kOf N') (selectedInstance … t')` for the typed selected tape `t'` with
`tapeBits t' = t.take inputBits`, within `hdTime4 w` (never in `|t|`). No ledger row is closed. Nothing is admitted.
-/

noncomputable section

namespace Paper2.AEth4

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.Loops
open Paper2.Unit4Shell.KofLoops (dupStmt dup_loop)
open Paper2.AEth3 (MF CF EF GS cut0 checks_of_large nbOf PBof stageOf cutClock_eq cutClockN_mono
  gl inputBits_fit cutLen cutLen_eq cutLen_ge fOut)

namespace Pack

inductive KL
  | a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 7
abbrev Control := Option Bool × Unit

def program : KL → TM2.Stmt (fun _ : Stack => Bool) KL Control
  | .a1 => dupStmt 0 1 2 .a1 .a2
  | .a2 => moveStmt 2 3 .a2 .a3
  | .a3 => parseStmt 3 4 .a3 .a4
  | .a4 => pushFalseStmt 5 .a5
  | .a5 => emitStmt 4 5 .a5 .a6
  | .a6 => moveStmt 5 6 .a6 .a7
  | .a7 => pushFalseStmt 0 .a8
  | .a8 => emitStmt 6 0 .a8 .a9
  | .a9 => pushFalseStmt 0 .a10
  | .a10 => emitStmt 1 0 .a10 .done
  | .done => .halt

/-- `pair e c ↦ pair (pair e c) (pair (field e) [])` (input and output stack `0`). -/
def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) KL.a1 ((none, ()) : Control) program

theorem outputs (e c : List Bool) :
    machine.OutputsWithin (EncodedComplexity.pair e c)
      (EncodedComplexity.pair (EncodedComplexity.pair e c)
        (EncodedComplexity.pair (EncodedCommunication.field e) []))
      (8 * ((EncodedComplexity.pair e c).length + 2)) := by
  set X := EncodedComplexity.pair e c with hX
  have hXf : X = EncodedCommunication.field e ++ c := rfl
  let S0 : Stack → List Bool := fun j => if j = 0 then X else []
  have e1 := dup_loop program (0 : Stack) 1 2 KL.a1 KL.a2 (by decide) (by decide) (by decide) rfl
    X S0 none () (by simp [S0])
  set S1 := Function.update (Function.update (Function.update S0 1 (X.reverse ++ S0 1)) 2
    (X.reverse ++ S0 2)) 0 [] with hS1
  have e2 := move_loop program (2 : Stack) 3 KL.a2 KL.a3 (by decide) rfl X.reverse S1 none ()
    (by simp [hS1, S0])
  rw [List.length_reverse] at e2
  set S2 := Function.update (Function.update S1 3 (X.reverse.reverse ++ S1 3)) 2 [] with hS2
  have e3 := parse_loop program (3 : Stack) 4 KL.a3 KL.a4 (by decide) rfl e c S2 none ()
    (by simp [hS2, hS1, S0, hXf])
  set S3 := Function.update (Function.update S2 4 (e.reverse ++ S2 4)) 3 c with hS3
  have e4 := pushFalse_step program (5 : Stack) KL.a4 KL.a5 rfl (some false, ()) S3
  set S4 := Function.update S3 5 (false :: S3 5) with hS4
  have e5 := emit_loop program (4 : Stack) 5 KL.a5 KL.a6 (by decide) rfl e.reverse S4
    (some false) () (by simp [hS4, hS3, hS2, hS1, S0])
  rw [List.length_reverse] at e5
  set S5 := Function.update (Function.update S4 5 (e.reverse.foldl emitFold (S4 5))) 4 [] with hS5
  have h55 : S5 5 = EncodedCommunication.field e ++ [] := by
    have : S4 5 = false :: [] := by simp [hS4, hS3, hS2, hS1, S0]
    simp only [hS5, Function.update_of_ne (by decide : (5 : Stack) ≠ 4), Function.update_self,
      this]
    exact emit_reverse_field e []
  have e6 := move_loop program (5 : Stack) 6 KL.a6 KL.a7 (by decide) rfl
    (EncodedCommunication.field e ++ []) S5 none () h55
  set S6 := Function.update (Function.update S5 6
    ((EncodedCommunication.field e ++ []).reverse ++ S5 6)) 5 [] with hS6
  have e7 := pushFalse_step program (0 : Stack) KL.a7 KL.a8 rfl (none, ()) S6
  set S7 := Function.update S6 0 (false :: S6 0) with hS7
  have h76 : S7 6 = (EncodedCommunication.field e ++ []).reverse := by
    simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have e8 := emit_loop program (6 : Stack) 0 KL.a8 KL.a9 (by decide) rfl
    (EncodedCommunication.field e ++ []).reverse S7 none () h76
  rw [List.length_reverse] at e8
  set S8 := Function.update (Function.update S7 0
    ((EncodedCommunication.field e ++ []).reverse.foldl emitFold (S7 0))) 6 [] with hS8
  have h80 : S8 0 = EncodedCommunication.field (EncodedCommunication.field e ++ []) ++ [] := by
    have : S7 0 = false :: [] := by simp [hS7, hS6, hS5, hS4, hS3, hS2, hS1]
    simp only [hS8, Function.update_of_ne (by decide : (0 : Stack) ≠ 6), Function.update_self,
      this]
    exact emit_reverse_field _ []
  have e9 := pushFalse_step program (0 : Stack) KL.a9 KL.a10 rfl (none, ()) S8
  set S9 := Function.update S8 0 (false :: S8 0) with hS9
  have h91 : S9 1 = X.reverse := by simp [hS9, hS8, hS7, hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have e10 := emit_loop program (1 : Stack) 0 KL.a10 KL.done (by decide) rfl X.reverse S9
    none () h91
  rw [List.length_reverse] at e10
  set S10 := Function.update (Function.update S9 0 (X.reverse.foldl emitFold (S9 0))) 1 []
    with hS10
  have h100 : S10 0 = EncodedCommunication.field X ++
      (EncodedCommunication.field (EncodedCommunication.field e ++ []) ++ []) := by
    have : S9 0 = false :: (EncodedCommunication.field (EncodedCommunication.field e ++ []) ++ []) := by
      simp only [hS9, Function.update_self, h80]
    simp only [hS10, Function.update_of_ne (by decide : (0 : Stack) ≠ 1), Function.update_self,
      this]
    exact emit_reverse_field X _
  have e11 := halt_step program KL.done rfl (none, ()) S10
  have hrun := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain (iter_chain (iter_chain (iter_chain e1 e2) e3) (one_step e4)) e5) e6)
    (one_step e7)) e8) (one_step e9)) e10) (one_step e11)
  have hraw : rawInit (0 : Stack) KL.a1 ((none, ()) : Control) X =
      ⟨some KL.a1, (none, ()), S0⟩ := rfl
  rw [← hraw] at hrun
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) KL.a1 ((none, ()) : Control)
    program X _ _ _ ?_ (by rw [hrun]) ?_
  · have hex : X.length = 2 * e.length + 1 + c.length := by
      rw [hXf, List.length_append, EncodedCommunication.field_length]
    simp only [List.length_append, List.length_nil, EncodedCommunication.field_length]
    omega
  · rw [hrun]
    simpa [EncodedComplexity.pair] using h100

end Pack

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- The selected T24 output at the growing gap `k = kOf N`. -/
abbrev Sel (Φ : ValidFormula) : TotalFiniteConstructorScratch.SelectedOutput :=
  TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables)

/-- The (tape-independent) length of the printed instance word. -/
def obLen (Φ : ValidFormula) : ℕ :=
  2 * ((Sel D B Φ).rows.bits.length + (Sel D B Φ).cols.bits.length + (Sel D B Φ).budget.bits.length) + 3 +
    (Sel D B Φ).rows * (Sel D B Φ).cols

theorem outputBits_length (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) :
    (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t').length = obLen D B Φ := by
  have h := EncodedSelectedOutput.outputBits_length (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t'
  simpa only [obLen] using h

/-- The clock of `MF ; GS` on `pair (encode Φ) c`. -/
def mgTime (Φ : ValidFormula) : ℕ :=
  CF D B * (2 * (EncodedCNF.encode Φ.val).length + 1 + cutLen Φ.val + 1) ^ EF D B + 2 * nbOf D B Φ +
    2 + stageOf D B Φ

/-- **The reduction core on the cut prefix** (the inner part of a-eth-owner-3 `red_outputs2`). -/
theorem mg_outputs (Φ : ValidFormula) (hk : 1 ≤ kOf Φ.val.variables)
    (hN : cut0 D B ≤ Φ.val.variables) (c : List Bool) (hcl : c.length ≤ cutLen Φ.val)
    (hIc : (Sel D B Φ).inputBits ≤ c.length) :
    ∃ t' : (Sel D B Φ).Tape, (Sel D B Φ).tapeBits t' = c.take (Sel D B Φ).inputBits ∧
      (BitMachineComposition.composition (MF D B) (GS D B)).OutputsWithin
        (EncodedComplexity.pair (EncodedCNF.encode Φ.val) c)
        (EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t')
        (mgTime D B Φ) := by
  obtain ⟨hm, -, hinc, hdeg, -⟩ := t10_source D B Φ
  have hch := checks_of_large D B Φ hN
  obtain ⟨t', ht', hrun⟩ := Paper2.ABridge.graph_stage_outputs B.degreeBound (sourceGap D B)
    B.degreeBound_pos (source_gap_pos D B) (t10Graph D B Φ) (t10Graph_valid D B Φ)
    (t10_vertices_pos D B Φ) hm (kOf Φ.val.variables) hk hinc hdeg hch c hIc
  refine ⟨t', ht', ?_⟩
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
    exact Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left 26 hcl)
      (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hcl))) 7
  have hstage : Paper2.ABridge.stageClock B.degreeBound (sourceGap D B) B.degreeBound_pos
      (source_gap_pos D B) (t10Graph D B Φ) (kOf Φ.val.variables) c ≤ stageOf D B Φ := by
    unfold Paper2.ABridge.stageClock stageOf
    rw [cutClock_eq, hbw]
    exact add_le_add (add_le_add (add_le_add (cutClockN_mono hnb hPB)
      (Nat.mul_le_mul_left 2 hnb)) le_rfl) le_rfl
  have h3 := BitMachine.outputsWithin_mono _ hrun hstage
  have h2 := Paper2.AEth3.MF_runs D B Φ c
  have hC := BitMachineComposition.composition_outputsWithin _ _ h2 h3
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
  unfold mgTime
  exact add_le_add (add_le_add (add_le_add hCF (Nat.mul_le_mul_left 2 hbank)) le_rfl) le_rfl

/-- THE fixed header machine of the growing-gap decider. -/
def hdMachine4 (K N₁ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (frontCut4 K N₁)
    (BitMachineComposition.composition Pack.machine
      (BitMachineComposition.composition
        (Paper2.Unit4Shell.PairMap.machine (BitMachineComposition.composition (MF D B) (GS D B)))
        (BitMachineComposition.composition Paper2.Unit4Shell.KofLoops.Swap.machine
          (BitMachineComposition.composition PairConcat.machine KHeader.machine))))

/-- The header clock of the uniform header at the printed instance (tape-independent). -/
def khTime (Φ : ValidFormula) : ℕ :=
  (2 * (EncodedCNF.encode Φ.val).length +
      Paper2.Unit4Shell.KofFront.BK * (Φ.val.variables + 1) ^ 2 + 2 * kOf Φ.val.variables + 6) +
    2 * (2 * kOf Φ.val.variables + 1 + obLen D B Φ) + 2 +
    GrowHeader.clock (kOf Φ.val.variables) (Sel D B Φ).rows (Sel D B Φ).cols (Sel D B Φ).budget

/-- The whole header clock, in `|w|` and the routed formula only (never the tape). -/
def hdTime4 (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) : ℕ :=
  let Φ := routedV K N₁ hN₁ w
  let eL := (EncodedCNF.encode Φ.val).length
  let XL := 2 * eL + 1 + cutLen Φ.val
  let ob := obLen D B Φ
  frontTime4 K N₁ w + 2 * XL + 2 +
    (8 * (XL + 2) + 2 * (2 * XL + 4 * eL + 4) + 2 +
      ((2 * XL + mgTime D B Φ + 2 * ob + 6) + 2 * (2 * ob + 4 * eL + 4) + 2 +
        (3 * (2 * ob + 4 * eL + 5) + 2 * (2 * ob + 4 * eL + 4) + 2 +
          (3 * (2 * ob + 4 * eL + 5) + 2 * (2 * eL + 1 + ob) + 2 + khTime D B Φ))))

theorem khTime_eq (Φ : ValidFormula) (t' : (Sel D B Φ).Tape) :
    KHeader.clock Φ.val (EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t') = khTime D B Φ := by
  have hl := outputBits_length D B Φ t'
  unfold EncodedSelectedOutput.outputBits at hl
  unfold KHeader.clock khTime
  simp only [EncodedComplexity.pair_length, List.length_replicate, hl]
  rfl

/-- **The header at the growing gap, on EVERY word.** -/
theorem hd4_outputs_all (K : ℕ) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N₁ (hN₁ : 1 ≤ N₁), N₀ ≤ N₁ → 2 ≤ K * N₁ →
      ∀ (w t : List Bool), 2 ^ (e0 (w.length + phiLen N₁) + 7) ≤ t.length →
      1 ≤ kOf (routedV K N₁ hN₁ w).val.variables ∧
      ∃ t' : (Sel D B (routedV K N₁ hN₁ w)).Tape,
        (Sel D B (routedV K N₁ hN₁ w)).tapeBits t' = t.take (Sel D B (routedV K N₁ hN₁ w)).inputBits ∧
        (hdMachine4 D B K N₁).OutputsWithin (EncodedComplexity.pair w t)
          (Paper2.HeaderWordRun.headeredWord (kOf (routedV K N₁ hN₁ w).val.variables)
            (EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B (routedV K N₁ hN₁ w))
              (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ w))
                (t10Graph_valid D B (routedV K N₁ hN₁ w)))
              B.degreeBound (sourceGap D B) (kOf (routedV K N₁ hN₁ w).val.variables) t'))
          (hdTime4 D B K N₁ hN₁ w) := by
  obtain ⟨N₂, hN₂⟩ := inputBits_fit D B K
  refine ⟨max 1 (max N₂ (cut0 D B)), le_max_left _ _, ?_⟩
  intro N₁ hN₁ hle hK w t ht
  set Φ := routedV K N₁ hN₁ w with hΦ
  have hvars : N₁ ≤ Φ.val.variables := routed4_variables K N₁ w
  have hsp : Φ.val.clauses.length ≤ K * Φ.val.variables := routed4_sparse K N₁ hK w
  have hN2 : N₂ ≤ Φ.val.variables := by
    have : N₂ ≤ max 1 (max N₂ (cut0 D B)) := le_trans (le_max_left _ _) (le_max_right _ _)
    omega
  have hN3 : cut0 D B ≤ Φ.val.variables := by
    have : cut0 D B ≤ max 1 (max N₂ (cut0 D B)) := le_trans (le_max_right _ _) (le_max_right _ _)
    omega
  obtain ⟨hk, hI⟩ := hN₂ Φ hsp hN2
  have hI' : (Sel D B Φ).inputBits ≤ Paper2.AEth.expLen Φ.val.variables := hI
  have hge := cutLen_ge Φ.val
  have hfit := cut4_fit K hN₁ w
  have hcf : cutLen Φ.val = cutLen (routed4 K N₁ w) := rfl
  set c := t.take (cutLen Φ.val) with hc
  have hcl : c.length ≤ cutLen Φ.val := List.length_take_le _ _
  have hIc : (Sel D B Φ).inputBits ≤ c.length := by
    rw [hc, List.length_take]; exact le_min (by omega) (by omega)
  obtain ⟨t', ht', hmg⟩ := mg_outputs D B Φ hk hN3 c hcl hIc
  refine ⟨hk, t', ?_, ?_⟩
  · rw [ht', hc, List.take_take, Nat.min_eq_left (by omega)]
  set e := EncodedCNF.encode Φ.val with he
  set ob := EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t' with hob
  set i := EncodedSelectedOutput.selectedInstance (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) (kOf Φ.val.variables) t' with hi
  have hobi : ob = EncodedCommunication.encodeInstance i := rfl
  have h1 : (frontCut4 K N₁).OutputsWithin (EncodedComplexity.pair w t)
      (EncodedComplexity.pair e c) (frontTime4 K N₁ w) := frontCut4_outputs K N₁ hN₁ w t
  have h2 := Pack.outputs e c
  have h3 := Paper2.Unit4Shell.PairMap.machine_outputs
    (M := BitMachineComposition.composition (MF D B) (GS D B)) (EncodedComplexity.pair e c) ob
    (EncodedComplexity.pair (EncodedCommunication.field e) []) _ hmg
  have h4 := Paper2.Unit4Shell.KofLoops.Swap.machine_outputs ob (EncodedCommunication.field e) []
  have h5 := PairConcat.outputs
    (EncodedComplexity.pair (EncodedCommunication.field e) (EncodedComplexity.pair ob []))
  rw [PairConcat.concat_pair] at h5
  have h6 := KHeader.machine_outputs Φ.val hk i
  rw [← hobi, khTime_eq D B Φ t'] at h6
  have hfe : EncodedCommunication.field e ++ ob = EncodedComplexity.pair e ob := rfl
  rw [hfe] at h5
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2
      (BitMachineComposition.composition_outputsWithin _ _ h3
        (BitMachineComposition.composition_outputsWithin _ _ h4
          (BitMachineComposition.composition_outputsWithin _ _ h5 h6))))
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hobl : ob.length = obLen D B Φ := outputBits_length D B Φ t'
  simp only [hdTime4, EncodedComplexity.pair_length, EncodedCommunication.field_length,
    List.length_nil, hobl]
  rw [← hΦ, ← he]
  omega

end Paper2.AEth4

end

#print axioms Paper2.AEth4.Pack.outputs
#print axioms Paper2.AEth4.outputBits_length
#print axioms Paper2.AEth4.mg_outputs
#print axioms Paper2.AEth4.khTime_eq
#print axioms Paper2.AEth4.hd4_outputs_all
