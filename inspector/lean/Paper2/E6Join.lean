import Paper2.E6Dec
import Paper2.E2Join
import Paper2.AModelTapeBridge
-- a-eth-owner-6 module E6Join: the ETape-dependent tail of a-eth-owner-5/E5Dec.lean (lines 239-281, `decAlg`, `decAlg_output`, verbatim) followed by the UNCHECKED draft a-eth-owner-5/E5Join.lean (SHA-256 4d47013cde348b7c7e94c6d5ed8a6c1bb9ddb7e09c59a0e4fd138a1cabe603c1) with import `E5Dec` -> `E6Dec` and repairs in `decAlg_joinAt` only: `rw [hout, hsw t']` -> `refine hout.trans ?_; rw [hsw t']`; `hlenT` closed by `rfl`; `rw [hblk]; congr 1; ...; exact (hw_transport ...).symm` -> `all_goals rfl` after the `hbits` rewrite and `exact congrArg₂ _ hhw hblk.symm` (see CHECKPOINT).

/-!
# Paper A (lock v12), lane `owner:a-eth-5`, segment 3: the full `JoinRealises` law of the composite decider

`JoinRealisesAt x Φ k E A` is the a-eth-owner-2 `JoinRealises` (route B) with the INPUT word `x` separated
from the formula `Φ` whose experiment is run (`joinAt_encode`: at `x = encode Φ` it IS `JoinRealises`, by
`Iff.rfl`). For inputs routed to another formula (below the cutoff, off-promise words) the decider runs the
construction on the routed formula `Φ' = routedV K N₁ hN₁ x`, so the identity holds at `(x, Φ')`.

* `split_law` (generic): the typed tape decoded from the first `r` bits and the block `(t.drop L).take s` of a
  uniform tape have the law `μ × uniform(s)` whenever `μ` is the pushforward of the uniform `r`-bit law through
  the bits map (the admitted `AModel.experiment_prob_uniform` form) and `dec` inverts the bits map.
* `hw_transport` (the header identity via `experiment_output_eq_select`): for a tape `b` of the experiment's
  output and a tape `t'` of the selected output with the same bits, the a-eth-owner-2 `headerWord` at `b` is the
  printed header word `hwOf` at `t'`.
* **`decAlg_joinAt`**: for EVERY word `x`, the composite decider `decAlg D B (selectedClassifier E) K N₁ …`
  realises the route-B identity at `(x, Φ', kOf N')`; **`decAlg_join`**: at `x = encode Φ` for every
  `K`-sparse valid `Φ` with `N₁ ≤ N`, it is the a-eth-owner-2 `JoinRealises D B Φ (kOf N) E`.

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth5

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open Paper2.Unit4Shell.T10Finite Paper2.Unit4Shell.Asymptotics
open Paper2.Unit4Shell.Definitions (uniformTape)
open Paper2.AEth4
open Paper2.AEth3 (cutLen)

/-- The Boolean vector of a word (`false` beyond its end). -/
def vecOf (v : List Bool) (s : ℕ) : Fin s → Bool := fun l => v.getD l.val false

theorem ofFn_vecOf (v : List Bool) (s : ℕ) (h : v.length = s) : List.ofFn (vecOf v s) = v := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [vecOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem vecOf_ofFn {s : ℕ} (x : Fin s → Bool) : vecOf (List.ofFn x) s = x := by
  funext l
  simp [vecOf, List.getD_eq_getElem?_getD]

/-- **Generic split law.** -/
theorem split_law {τ : Type} [Fintype τ] (μ : Paper2.FiniteLaw τ) (bits : τ → List Bool) (r : ℕ)
    (hF : ∀ F : List Bool → Prop, μ.prob (fun a => F (bits a)) =
      (uniformTape r).prob (fun s => F (List.ofFn s)))
    (dec : List Bool → τ) (hdec : ∀ a, dec (bits a) = a)
    {L s R : ℕ} (hrL : r ≤ L) (h : L + s ≤ R) (P : τ × (Fin s → Bool) → Prop) :
    (uniformTape R).prob (fun t => P (dec ((List.ofFn t).take r),
        vecOf (((List.ofFn t).drop L).take s) s)) =
      (μ.prod (uniformTape s)).prob P := by
  rw [uniform_split_take_prob hrL h (fun u v => P (dec u, vecOf v s))]
  have l1 := prod_prob_snd (uniformTape r) (uniformTape s) (fun a b => P (dec (List.ofFn a), b))
  have l2 := prod_prob_snd μ (uniformTape s) (fun a b => P (a, b))
  simp only [vecOf_ofFn]
  simp only at l1 l2
  rw [l1]
  have e : (μ.prod (uniformTape s)).prob P =
      (μ.prod (uniformTape s)).prob (fun x => P (x.1, x.2)) := rfl
  rw [e, l2]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  have := hF (fun l => P (dec l, b))
  simp only [hdec] at this
  exact this.symm

/-- **Header transport** along `O = S` (used with `experiment_output_eq_select`). -/
theorem hw_transport (O S : TotalFiniteConstructorScratch.SelectedOutput) (hOS : O = S)
    (hinj : Function.Injective O.tapeBits) (k : ℕ) (b : O.Tape) (t' : S.Tape)
    (hb : O.tapeBits b = S.tapeBits t') :
    EncodedCommunication.natField (2 * O.budget + k) ++
        Paper2.AModel.matrixWord O.rows O.cols (O.table b).bits =
      EncodedCommunication.natField (2 * S.budget + k) ++
        AFront.Projection.matrixWord S.rows S.cols (S.table t').bits := by
  subst hOS
  have := hinj hb
  subst this
  rfl

theorem len_transport (O S : TotalFiniteConstructorScratch.SelectedOutput) (hOS : O = S) (k : ℕ)
    (b : O.Tape) :
    (EncodedCommunication.natField (2 * O.budget + k) ++
        Paper2.AModel.matrixWord O.rows O.cols (O.table b).bits).length =
      (EncodedCommunication.natField (2 * S.budget + k)).length +
        ((EncodedCommunication.natField S.rows).length +
          (EncodedCommunication.natField S.cols).length + S.rows * S.cols) := by
  subst hOS
  have hT := (O.table b).length
  simp only [Paper2.AModel.matrixWord, List.length_append]
  rw [hT]

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **Segment 4: the composite R20 decider** (`N0 ≤ N₁`, `2 ≤ K N₁`). -/
def decAlg (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN : N0 D B C K ≤ N₁)
    (hK : 2 ≤ K * N₁) : Paper2.AEth2.ETape.Algorithm where
  tapeLen := tapeCA (phiLen N₁) (7 + C.cR)
  lenMachine := CAMachine (phiLen N₁) (7 + C.cR)
  lenTime := CAtime (phiLen N₁) (7 + C.cR)
  lenC := (BT + 30) * (phiLen N₁ + 1) ^ 2
  lenE := 2
  lenRuns := CAMachine_outputs (phiLen N₁) (7 + C.cR)
  lenPoly := CAtime_poly (phiLen N₁) (7 + C.cR)
  tapeSubexp := tapeCA_subexp (phiLen N₁) (7 + C.cR)
  machine := decMachine D B C K N₁
  time := decTime D B C K N₁ hN₁
  output := fun x t => ((decMachine D B C K N₁).run (decTime D B C K N₁ hN₁ x)
    ((decMachine D B C K N₁).init (EncodedComplexity.pair x t))).stk (decMachine D B C K N₁).output
  runs := by
    intro x t
    have hlen : 2 ^ C.cR * L1 K N₁ x ≤ (List.ofFn t).length := by
      rw [List.length_ofFn]; exact twoCut_fit K N₁ C.cR hN₁ x
    obtain ⟨-, t', -, -, -, hrun⟩ := (N0_spec D B C K).2 N₁ hN₁ hN hK x (List.ofFn t) hlen
    have hb := BitMachine.outputsWithin_at_bound _ hrun
    rw [hb.2]
    exact hrun
  extend := by
    intro x t u ht
    have hlen : 2 ^ C.cR * L1 K N₁ x ≤ t.length := by
      rw [ht]; exact twoCut_fit K N₁ C.cR hN₁ x
    have hlenu : 2 ^ C.cR * L1 K N₁ x ≤ (t ++ u).length := by
      rw [List.length_append]; omega
    obtain ⟨-, t1, ht1, hI1, hfit1, hrun1⟩ := (N0_spec D B C K).2 N₁ hN₁ hN hK x t hlen
    obtain ⟨-, t2, ht2, -, -, hrun2⟩ := (N0_spec D B C K).2 N₁ hN₁ hN hK x (t ++ u) hlenu
    have hEq := TotalFiniteConstructorScratch.experiment_output_eq_select
      (t10_vertices_pos D B (routedV K N₁ hN₁ x))
      (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ x))
        (t10Graph_valid D B (routedV K N₁ hN₁ x))) B.degreeBound
      (sourceGap D B) (kOf (routedV K N₁ hN₁ x).val.variables)
    obtain ⟨-, -, hinj, -, -⟩ := Paper2.AModel.experiment_uniformExact
      (t10_vertices_pos D B (routedV K N₁ hN₁ x))
      (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ x))
        (t10Graph_valid D B (routedV K N₁ hN₁ x))) B.degreeBound
      (sourceGap D B) (kOf (routedV K N₁ hN₁ x).val.variables)
    have hinjS : Function.Injective (Sel D B (routedV K N₁ hN₁ x)).tapeBits := by
      rw [hEq] at hinj; exact hinj
    have hIt : (Sel D B (routedV K N₁ hN₁ x)).inputBits ≤ t.length := by
      have : L1 K N₁ x ≤ 2 ^ C.cR * L1 K N₁ x := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      omega
    have ht12 : t2 = t1 := hinjS (by rw [ht1, ht2, List.take_append_of_le_length hIt])
    subst ht12
    have hsb := second_block_fit C.cR (routedV K N₁ hN₁ x).val
    have hL : L1 K N₁ x = cutLen (routedV K N₁ hN₁ x).val := rfl
    rw [← hL] at hsb
    have hs : L1 K N₁ x + C.tapeLength (hwOf D B (routedV K N₁ hN₁ x) t2) ≤ t.length := by
      omega
    have hblk : ((t ++ u).drop (L1 K N₁ x)).take (C.tapeLength (hwOf D B (routedV K N₁ hN₁ x) t2)) =
        (t.drop (L1 K N₁ x)).take (C.tapeLength (hwOf D B (routedV K N₁ hN₁ x) t2)) := by
      rw [List.drop_append_of_le_length (by omega),
        List.take_append_of_le_length (by rw [List.length_drop]; omega)]
    rw [hblk] at hrun2
    have hout := (BitMachine.outputsWithin_at_bound _ hrun1).2
    show (decMachine D B C K N₁).OutputsWithin (EncodedComplexity.pair x (t ++ u))
      (((decMachine D B C K N₁).run (decTime D B C K N₁ hN₁ x)
        ((decMachine D B C K N₁).init (EncodedComplexity.pair x t))).stk (decMachine D B C K N₁).output)
      (decTime D B C K N₁ hN₁ x)
    rw [hout]
    exact hrun2

/-- **The output identity of the composite decider.** -/
theorem decAlg_output (C : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁)
    (hN : N0 D B C K ≤ N₁) (hK : 2 ≤ K * N₁) (x : List Bool)
    (t : Fin (tapeCA (phiLen N₁) (7 + C.cR) x.length) → Bool) :
    1 ≤ kOf (routedV K N₁ hN₁ x).val.variables ∧
    ∃ t' : (Sel D B (routedV K N₁ hN₁ x)).Tape,
      (Sel D B (routedV K N₁ hN₁ x)).tapeBits t' =
        (List.ofFn t).take (Sel D B (routedV K N₁ hN₁ x)).inputBits ∧
      (Sel D B (routedV K N₁ hN₁ x)).inputBits ≤ L1 K N₁ x ∧
      C.tapeLength (hwOf D B (routedV K N₁ hN₁ x) t') ≤
        C.cR * Paper2.AEth.expLen (routedV K N₁ hN₁ x).val.variables ∧
      (decAlg D B C K N₁ hN₁ hN hK).output x (List.ofFn t) =
        C.output (hwOf D B (routedV K N₁ hN₁ x) t')
          (((List.ofFn t).drop (L1 K N₁ x)).take (C.tapeLength (hwOf D B (routedV K N₁ hN₁ x) t'))) := by
  have hlen : 2 ^ C.cR * L1 K N₁ x ≤ (List.ofFn t).length := by
    rw [List.length_ofFn]; exact twoCut_fit K N₁ C.cR hN₁ x
  obtain ⟨hk, t', ht', hIL, hfit, hrun⟩ := (N0_spec D B C K).2 N₁ hN₁ hN hK x (List.ofFn t) hlen
  exact ⟨hk, t', ht', hIL, hfit, (BitMachine.outputsWithin_at_bound _ hrun).2⟩


set_option hygiene false in
local notation "EXP" Φ:max k:max => TotalFiniteConstructorScratch.experiment (t10_vertices_pos D B Φ)
  (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ)) B.degreeBound (sourceGap D B) k

/-- Route-B identity with the input word separated from the formula. -/
def JoinRealisesAt (x : List Bool) (Φ : ValidFormula) (k : ℕ) (E : Paper2.SelectedTape.Algorithm)
    (A : Paper2.AEth2.ETape.Algorithm) : Prop :=
  letI : Fintype (EXP Φ k).output.Tape := (EXP Φ k).tapeFintype
  ∃ (s : ℕ) (π : (Fin (A.tapeLen x.length) → Bool) → (EXP Φ k).output.Tape × (Fin s → Bool)),
    (∀ b, (Paper2.HeaderStrip.selectedClassifier E).tapeLength (Paper2.AEth.headerWord D B Φ k b) = s) ∧
    (∀ P : (EXP Φ k).output.Tape × (Fin s → Bool) → Prop,
      (uniformTape (A.tapeLen x.length)).prob (fun t => P (π t)) =
        ((EXP Φ k).tapeLaw.prod (uniformTape s)).prob P) ∧
    ∀ t, A.output x (List.ofFn t) =
      (Paper2.HeaderStrip.selectedClassifier E).output (Paper2.AEth.headerWord D B Φ k (π t).1)
        (List.ofFn (π t).2)

theorem joinAt_encode (Φ : ValidFormula) (k : ℕ) (E : Paper2.SelectedTape.Algorithm)
    (A : Paper2.AEth2.ETape.Algorithm) :
    JoinRealisesAt D B (EncodedCNF.encode Φ.val) Φ k E A ↔ Paper2.AEth2.JoinRealises D B Φ k E A :=
  Iff.rfl

set_option maxHeartbeats 1600000 in
/-- **Segment 3: the composite decider realises the route-B identity on EVERY word.** -/
theorem decAlg_joinAt (E : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁)
    (hN : N0 D B (Paper2.HeaderStrip.selectedClassifier E) K ≤ N₁) (hK : 2 ≤ K * N₁)
    (x : List Bool) :
    JoinRealisesAt D B x (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables) E
      (decAlg D B (Paper2.HeaderStrip.selectedClassifier E) K N₁ hN₁ hN hK) := by
  letI : Fintype (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output.Tape := (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).tapeFintype
  have hEq := TotalFiniteConstructorScratch.experiment_output_eq_select (t10_vertices_pos D B (routedV K N₁ hN₁ x))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ x)) (t10Graph_valid D B (routedV K N₁ hN₁ x))) B.degreeBound
    (sourceGap D B) (kOf (routedV K N₁ hN₁ x).val.variables)
  obtain ⟨r, hlen, hinj, hsurj, -⟩ := Paper2.AModel.experiment_uniformExact (t10_vertices_pos D B (routedV K N₁ hN₁ x))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ x)) (t10Graph_valid D B (routedV K N₁ hN₁ x))) B.degreeBound
    (sourceGap D B) (kOf (routedV K N₁ hN₁ x).val.variables)
  obtain ⟨r2, hlen2, hF⟩ := Paper2.AModel.experiment_prob_uniform (t10_vertices_pos D B (routedV K N₁ hN₁ x))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ x)) (t10Graph_valid D B (routedV K N₁ hN₁ x))) B.degreeBound
    (sourceGap D B) (kOf (routedV K N₁ hN₁ x).val.variables)
  obtain ⟨b0⟩ := Paper2.FiniteLaw.nonempty (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).tapeLaw
  have hr2 : r2 = r := (hlen2 b0).symm.trans (hlen b0)
  subst hr2
  -- the decoder of the reduction block
  let dec : List Bool → (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output.Tape := fun l =>
    if h : ∃ a, (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output.tapeBits a = l then Classical.choose h else b0
  have hdec_spec : ∀ l, l.length = r2 → (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output.tapeBits (dec l) = l := by
    intro l hl
    have h := hsurj l hl
    simp only [dec, dif_pos h]
    exact Classical.choose_spec h
  have hdec : ∀ a, dec ((EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output.tapeBits a) = a :=
    fun a => hinj (hdec_spec _ (hlen a))
  -- one reference run: r2 = inputBits, the block sizes
  have hR : (decAlg D B (Paper2.HeaderStrip.selectedClassifier E) K N₁ hN₁ hN hK).tapeLen x.length = tapeCA (phiLen N₁) (7 + (Paper2.HeaderStrip.selectedClassifier E).cR) x.length := rfl
  obtain ⟨hk1, t0, ht0, hIL, hfit0, -⟩ :=
    decAlg_output D B (Paper2.HeaderStrip.selectedClassifier E) K N₁ hN₁ hN hK x (fun _ => false)
  have hsel := TotalFiniteConstructorScratch.selected_exact_lengths (t10_vertices_pos D B (routedV K N₁ hN₁ x))
    (CanonicalEdgeTape.graphEdge (t10Graph D B (routedV K N₁ hN₁ x)) (t10Graph_valid D B (routedV K N₁ hN₁ x))) B.degreeBound
    (sourceGap D B) (kOf (routedV K N₁ hN₁ x).val.variables) (t10_source D B (routedV K N₁ hN₁ x)).2.2.2.2.1 (t10_source D B (routedV K N₁ hN₁ x)).2.2.2.1
    (source_gap_pos D B) B.degreeBound_pos (t10_source D B (routedV K N₁ hN₁ x)).1
  have hlenS : ∀ t' : (Sel D B (routedV K N₁ hN₁ x)).Tape, ((Sel D B (routedV K N₁ hN₁ x)).tapeBits t').length = r2 := by
    rw [hEq] at hlen; exact hlen
  have hrI : r2 = (Sel D B (routedV K N₁ hN₁ x)).inputBits := (hlenS t0).symm.trans (hsel t0).2
  set s := (Paper2.HeaderStrip.selectedClassifier E).cR * (hwLen D B (routedV K N₁ hN₁ x) + 1) ^ (Paper2.HeaderStrip.selectedClassifier E).dR with hs
  have hsw : ∀ t' : (Sel D B (routedV K N₁ hN₁ x)).Tape, (Paper2.HeaderStrip.selectedClassifier E).tapeLength (hwOf D B (routedV K N₁ hN₁ x) t') = s := by
    intro t'
    show (Paper2.HeaderStrip.selectedClassifier E).cR * ((hwOf D B (routedV K N₁ hN₁ x) t').length + 1) ^ (Paper2.HeaderStrip.selectedClassifier E).dR = s
    rw [hw_length_eq]
  have hsb := second_block_fit (Paper2.HeaderStrip.selectedClassifier E).cR (routedV K N₁ hN₁ x).val
  have hfitR := twoCut_fit K N₁ (Paper2.HeaderStrip.selectedClassifier E).cR hN₁ x
  have hLs : L1 K N₁ x + s ≤ tapeCA (phiLen N₁) (7 + (Paper2.HeaderStrip.selectedClassifier E).cR) x.length := by
    have := hsw t0
    have hL : L1 K N₁ x = cutLen (routedV K N₁ hN₁ x).val := rfl
    rw [hL] at hfitR ⊢
    omega
  have hrL : r2 ≤ L1 K N₁ x := by rw [hrI]; exact hIL
  refine ⟨s, fun t => (dec ((List.ofFn t).take r2),
    vecOf (((List.ofFn t).drop (L1 K N₁ x)).take s) s), ?_, ?_, ?_⟩
  · intro b
    show (Paper2.HeaderStrip.selectedClassifier E).cR * ((Paper2.AEth.headerWord D B (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables) b).length + 1) ^ (Paper2.HeaderStrip.selectedClassifier E).dR = s
    have hl := len_transport (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output (Sel D B (routedV K N₁ hN₁ x)) hEq (kOf (routedV K N₁ hN₁ x).val.variables) b
    have hh : (Paper2.AEth.headerWord D B (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables) b).length = hwLen D B (routedV K N₁ hN₁ x) := hl
    rw [hh]
  · intro P
    exact split_law (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).tapeLaw (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output.tapeBits r2 hF dec hdec hrL hLs P
  · intro t
    dsimp only
    obtain ⟨-, t', ht', -, -, hout⟩ := decAlg_output D B (Paper2.HeaderStrip.selectedClassifier E) K N₁ hN₁ hN hK x t
    refine hout.trans ?_
    rw [hsw t']
    have hlenT : (List.ofFn t).length = tapeCA (phiLen N₁) (7 + (Paper2.HeaderStrip.selectedClassifier E).cR) x.length := by
      rw [List.length_ofFn]; rfl
    have hblk : List.ofFn (vecOf (((List.ofFn t).drop (L1 K N₁ x)).take s) s) =
        ((List.ofFn t).drop (L1 K N₁ x)).take s := by
      apply ofFn_vecOf
      rw [List.length_take, List.length_drop, hlenT]
      omega
    have hbits : (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output.tapeBits (dec ((List.ofFn t).take r2)) =
        (Sel D B (routedV K N₁ hN₁ x)).tapeBits t' := by
      rw [hdec_spec _ (by rw [List.length_take, hlenT]; omega), ht', ← hrI]
      all_goals rfl
    have hhw := (hw_transport (EXP (routedV K N₁ hN₁ x) (kOf (routedV K N₁ hN₁ x).val.variables)).output (Sel D B (routedV K N₁ hN₁ x)) hEq hinj (kOf (routedV K N₁ hN₁ x).val.variables) _ t' hbits).symm
    exact congrArg₂ (Paper2.HeaderStrip.selectedClassifier E).output hhw hblk.symm

/-- **At a sparse valid formula beyond the cutoff, the decider realises `JoinRealises`.** -/
theorem decAlg_join (E : Paper2.SelectedTape.Algorithm) (K N₁ : ℕ) (hN₁ : 1 ≤ N₁)
    (hN : N0 D B (Paper2.HeaderStrip.selectedClassifier E) K ≤ N₁) (hK : 2 ≤ K * N₁)
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length ≤ K * Φ.val.variables)
    (hNΦ : N₁ ≤ Φ.val.variables) :
    Paper2.AEth2.JoinRealises D B Φ (kOf Φ.val.variables) E
      (decAlg D B (Paper2.HeaderStrip.selectedClassifier E) K N₁ hN₁ hN hK) := by
  have hr : routedV K N₁ hN₁ (EncodedCNF.encode Φ.val) = Φ :=
    Subtype.ext (routed4_encode K N₁ Φ.val Φ.property hsp hNΦ)
  have h := decAlg_joinAt D B E K N₁ hN₁ hN hK (EncodedCNF.encode Φ.val)
  rw [hr] at h
  exact h

end Paper2.AEth5

end

#print axioms Paper2.AEth5.decAlg
#print axioms Paper2.AEth5.decAlg_output
#print axioms Paper2.AEth5.ofFn_vecOf
#print axioms Paper2.AEth5.vecOf_ofFn
#print axioms Paper2.AEth5.split_law
#print axioms Paper2.AEth5.hw_transport
#print axioms Paper2.AEth5.len_transport
#print axioms Paper2.AEth5.joinAt_encode
#print axioms Paper2.AEth5.decAlg_joinAt
#print axioms Paper2.AEth5.decAlg_join
