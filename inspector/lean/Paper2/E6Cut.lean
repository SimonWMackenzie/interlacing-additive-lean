import Paper2.E6Tape
import Paper2.E4Law
import Paper2.BindSplit
-- a-eth-owner-6 copy of frozen a-eth-owner-5/E5Cut.lean (SHA-256 dd48983a1f192c68bb271a24bb45d4275266f5b7da93684501dfe53ed3872e22); import lines renamed only.

/-!
# Paper A (lock v12), lane `owner:a-eth-5`, segment 1: the second request and the split of the cut prefix

Lock v12 `sections/06-reduction.tex:107-153` (`thm:quantitative`, proof: "The midpoint test from
\cref{intro:corollary} decides the formula with bounded error"). The growing-gap decider needs TWO
independent blocks of its tape: the reduction block (read by the T24 construction) and the classifier
block (read by the A27 selected classifier). No stage may transfer the whole tape.

ONE fixed machine `twoCut K N₁ j` = `Cut.machine (inner4 K N₁) (2^j) 1 ; Retain.machine idMachine 1 1`:
* the a-eth-owner-2 physical prefix cutter, with the SAME inner machine `inner4` as `frontCut4`
  (a-eth-owner-4) but the constant `2^j` in place of `1`: it cuts `P = t.take (2^j · L1)` where
  `L1 = |fOut Φ'| + 1 = cutLen Φ'` (the second unary request is `2^j` copies of the first one;
  the unread rest of `t` is never touched);
* the admitted retained-suffix split `SelectedTape.Bind.Retain.machine` with the admitted identity
  witness `Bind.idMachine` and constants `1, 1`: it splits `P` at `|fOut Φ'| + 1 = L1` and keeps
  the suffix verbatim.
Output on `pair w t` (EVERY word, EVERY tape):
`pair (pair (fOut Φ') (t.take L1)) ((t.take (2^j · L1)).drop L1)`, clock `twoCutTime` without `t`.

`blocks_law`: the reduction block `t.take I` (`I ≤ L1`) and the classifier block
`(((t.take (2^j L1)).drop L1).take s)` (`L1 + s ≤ 2^j L1 ≤ R`) of a uniform length-`R` tape are
uniform and independent (the a-eth-owner-4 `uniform_split_take_prob`).
`twoCut_fit`: `2^j · cutLen (routed4 K N₁ w) ≤ tapeCA (phiLen N₁) (7 + j) |w|` for EVERY word.
`second_block_fit`: `cR · expLen N' ≤ (2^cR - 1) · L1`.

No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth5

open EthInapproximability.CurrentPaper
open Paper2.AEth4
open Paper2.AEth3 (fOut cutLen cutLen_eq cutLen_ge)

/-- THE fixed two-block cutter. -/
def twoCut (K N₁ j : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (Paper2.AEth2.Cut.machine (inner4 K N₁) (2 ^ j) 1)
    (Paper2.SelectedTape.Bind.Retain.machine Paper2.SelectedTape.Bind.idMachine 1 1)

/-- The routed formula's cut length (`L1`). -/
abbrev L1 (K N₁ : ℕ) (w : List Bool) : ℕ := cutLen (routed4 K N₁ w)

/-- Length bound of the middle word (tape-independent). -/
def midLen (K N₁ j : ℕ) (w : List Bool) : ℕ :=
  2 * (fOut (routed4 K N₁ w)).length + 1 + 2 ^ j * L1 K N₁ w

/-- The two-block cutter clock, in `|w|` and the routed formula only (never in the tape). -/
def twoCutTime (K N₁ j : ℕ) (w : List Bool) : ℕ :=
  Paper2.AEth2.Cut.cutTimeG (2 ^ j) 1 (inner4 K N₁).pushBound w.length (inner4Time K N₁ w) +
    2 * midLen K N₁ j w + 2 +
    Paper2.SelectedTape.Bind.Retain.timeBound 1 1 Paper2.SelectedTape.Bind.idC
      Paper2.SelectedTape.Bind.idD Paper2.SelectedTape.Bind.idMachine.pushBound (midLen K N₁ j w)

theorem retain_timeBound_mono (cf df pb : ℕ) {N N' : ℕ} (h : N ≤ N') :
    Paper2.SelectedTape.Bind.Retain.timeBound 1 1 cf df pb N ≤
      Paper2.SelectedTape.Bind.Retain.timeBound 1 1 cf df pb N' := by
  unfold Paper2.SelectedTape.Bind.Retain.timeBound
  gcongr

/-- **Segment 1: the two-block cut, on EVERY word and EVERY tape.** -/
theorem twoCut_outputs (K N₁ j : ℕ) (hN₁ : 1 ≤ N₁) (w t : List Bool) :
    (twoCut K N₁ j).OutputsWithin (EncodedComplexity.pair w t)
      (EncodedComplexity.pair
        (EncodedComplexity.pair (fOut (routed4 K N₁ w)) (t.take (L1 K N₁ w)))
        ((t.take (2 ^ j * L1 K N₁ w)).drop (L1 K N₁ w)))
      (twoCutTime K N₁ j w) := by
  have h1 := Paper2.AEth2.Cut.cut_outputs_gen (inner4 K N₁) (2 ^ j) 1
    (fun _ => fOut (routed4 K N₁ w)) (fun _ => inner4Time K N₁ w) w
    (inner4_outputs K N₁ hN₁ w) t
  have hL : 2 ^ j * ((fOut (routed4 K N₁ w)).length + 1) ^ 1 = 2 ^ j * L1 K N₁ w := by
    simp [L1, cutLen]
  simp only [hL] at h1
  set P := t.take (2 ^ j * L1 K N₁ w) with hP
  have h2 := Paper2.SelectedTape.Bind.Retain.machine_outputs Paper2.SelectedTape.Bind.idMachine 1 1
    id Paper2.SelectedTape.Bind.idC Paper2.SelectedTape.Bind.idD Paper2.SelectedTape.Bind.idRuns
    (EncodedComplexity.pair (fOut (routed4 K N₁ w)) P)
  rw [Paper2.SelectedTape.Bind.Retain.result_pair] at h2
  have hL2 : 1 * ((fOut (routed4 K N₁ w)).length + 1) ^ 1 = L1 K N₁ w := by
    simp [L1, cutLen]
  simp only [id] at h2
  rw [hL2] at h2
  have hPt : P.take (L1 K N₁ w) = t.take (L1 K N₁ w) := by
    rw [hP, List.take_take]
    congr 1
    have : L1 K N₁ w ≤ 2 ^ j * L1 K N₁ w :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos j)
    omega
  rw [hPt] at h2
  have hmid : (EncodedComplexity.pair (fOut (routed4 K N₁ w)) P).length ≤ midLen K N₁ j w := by
    rw [EncodedComplexity.pair_length]
    have : P.length ≤ 2 ^ j * L1 K N₁ w := by rw [hP]; exact List.length_take_le _ _
    unfold midLen; omega
  have h2' := BitMachine.outputsWithin_mono _ h2 (retain_timeBound_mono _ _ _ hmid)
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1 h2'
  refine BitMachine.outputsWithin_mono _ hC ?_
  unfold twoCutTime
  omega

/-- The reduction block and the classifier block of the cut prefix. -/
theorem blocks_eq (L j I s : ℕ) (t : List Bool) (hI : I ≤ L) (hs : L + s ≤ 2 ^ j * L) :
    (t.take L).take I = t.take I ∧
      ((t.take (2 ^ j * L)).drop L).take s = (t.drop L).take s := by
  refine ⟨by rw [List.take_take, Nat.min_eq_left hI], ?_⟩
  rw [List.drop_take, List.take_take]
  congr 1
  omega

/-- **Segment 1 law.** The two blocks of a uniform tape are uniform and independent. -/
theorem blocks_law {I L s R j : ℕ} (hI : I ≤ L) (hs : L + s ≤ 2 ^ j * L) (hR : 2 ^ j * L ≤ R)
    (F : List Bool → List Bool → Prop) :
    (Paper2.Unit4Shell.Definitions.uniformTape R).prob
        (fun t => F (((List.ofFn t).take L).take I)
          ((((List.ofFn t).take (2 ^ j * L)).drop L).take s)) =
      ((Paper2.Unit4Shell.Definitions.uniformTape I).prod
        (Paper2.Unit4Shell.Definitions.uniformTape s)).prob
        (fun x => F (List.ofFn x.1) (List.ofFn x.2)) := by
  have e : (fun t : Fin R → Bool => F (((List.ofFn t).take L).take I)
      ((((List.ofFn t).take (2 ^ j * L)).drop L).take s)) =
      (fun t => F ((List.ofFn t).take I) (((List.ofFn t).drop L).take s)) := by
    funext t
    rw [(blocks_eq L j I s (List.ofFn t) hI hs).1, (blocks_eq L j I s (List.ofFn t) hI hs).2]
  rw [e]
  exact uniform_split_take_prob hI (le_trans hs hR) F

/-- **The cut fits the carrier tape** `tapeCA (phiLen N₁) (7 + j)`, for EVERY word. -/
theorem twoCut_fit (K N₁ j : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) :
    2 ^ j * L1 K N₁ w ≤ tapeCA (phiLen N₁) (7 + j) w.length := by
  have h : L1 K N₁ w ≤ 2 ^ (e0 (w.length + phiLen N₁) + 7) := cut4_fit K hN₁ w
  unfold tapeCA
  calc 2 ^ j * L1 K N₁ w ≤ 2 ^ j * 2 ^ (e0 (w.length + phiLen N₁) + 7) :=
        Nat.mul_le_mul_left _ h
    _ = 2 ^ (e0 (w.length + phiLen N₁) + (7 + j)) := by
        rw [← pow_add]; congr 1; omega

/-- **The second block covers `cR · expLen N'`** when `j = cR`. -/
theorem second_block_fit (cR : ℕ) (F : EncodedCNF.Formula) :
    cutLen F + cR * Paper2.AEth.expLen F.variables ≤ 2 ^ cR * cutLen F := by
  have hge := cutLen_ge F
  have hlt : cR < 2 ^ cR := Nat.lt_two_pow_self
  have h1 : cR * Paper2.AEth.expLen F.variables ≤ cR * cutLen F :=
    le_trans (Nat.mul_le_mul_left _ (by omega : Paper2.AEth.expLen F.variables ≤ 2 * Paper2.AEth.expLen F.variables))
      (Nat.mul_le_mul_left _ hge)
  have h2 : cutLen F + cR * cutLen F = (cR + 1) * cutLen F := by ring
  have h3 : (cR + 1) * cutLen F ≤ 2 ^ cR * cutLen F := Nat.mul_le_mul_right _ hlt
  omega

end Paper2.AEth5

end

#print axioms Paper2.AEth5.retain_timeBound_mono
#print axioms Paper2.AEth5.twoCut_outputs
#print axioms Paper2.AEth5.blocks_eq
#print axioms Paper2.AEth5.blocks_law
#print axioms Paper2.AEth5.twoCut_fit
#print axioms Paper2.AEth5.second_block_fit
