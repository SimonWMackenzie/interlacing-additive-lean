import Paper2.E3Inner
import Paper2.AFrontRoute
import Paper2.AFrontSparse

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 3 (obstacle O3): a total front on EVERY word and EVERY tape

a-eth-owner-3's `frontCut` is proved only on literal `encode F` words. Here ONE fixed machine `frontCut4 K N₁`
is proved on `pair w t` for EVERY word `w` and EVERY tape `t`. Inside the cutter's inner machine (so that no
stage ever transfers the tape: the a-eth-owner-1 KEY DESIGN CONSTRAINT), the raw word is routed:

* `RawDup` (frozen `E3Loops`), then the admitted density checker `AFront.Sparse.sparseCheck K` under the admitted
  `PairMap`, then the new fixed `Select` machine keeps `w` if it is a valid formula with `#clauses ≤ K·#variables`
  and replaces it by the empty (malformed) word otherwise;
* the admitted all-input router `AFront.Route.frontRoute N₁` (lock C-parameters.tex:204-206) sends malformed
  words to the fixed NO formula `phi N₁ false`, valid formulas with fewer than `N₁` variables to the fixed
  YES/NO formula `phi N₁ (satAnswer w)` (the admitted charged finite-control `SmallArm` decides them: this is the
  charged finite table below the cutoff), and keeps all other words; `Fst` (frozen `E3Loops`) unwraps.

The routed formula is ALWAYS valid, has at least `N₁` variables, is `K`-sparse (for `2 ≤ K·N₁`), equals the input
formula on sparse valid inputs with `N ≥ N₁`, and has the same satisfiability as the input on every sparse valid
input. Then the frozen a-eth-owner-3 inner machine prints the cut request and the frozen a-eth-owner-2 cutter
takes exactly `cutLen` tape bits. No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth4

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops

namespace Select

inductive SL
  | s1 | s2 | s3 | s4 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3
abbrev Control := Option Bool × Unit

def program : SL → TM2.Stmt (fun _ : Stack => Bool) SL Control
  | .s1 => parseStmt 0 1 .s1 .s2
  | .s2 => .pop 1 setBit (.branch (fun v => v.1.getD false) (.goto fun _ => SL.done)
      (.goto fun _ => SL.s3))
  | .s3 => parseStmt 0 2 .s3 .s4
  | .s4 => pushFalseStmt 0 .done
  | .done => .halt

/-- `pair [s] (pair u r) ↦ pair (if s then u else []) r` (input and output stack `0`). -/
def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) SL.s1 ((none, ()) : Control) program

def selWord (s : Bool) (u : List Bool) : List Bool := if s then u else []

theorem one_step' {α : Type*} {f : α → α} {a b : α} (h : f a = b) : f^[1] a = b := by
  rw [Function.iterate_one]
  exact h

theorem outputs (s : Bool) (u r : List Bool) :
    machine.OutputsWithin (EncodedComplexity.pair [s] (EncodedComplexity.pair u r))
      (EncodedComplexity.pair (selWord s u) r) (u.length + 6) := by
  set inW := EncodedComplexity.pair [s] (EncodedComplexity.pair u r) with hinW
  let S0 : Stack → List Bool := fun j => if j = 0 then inW else []
  have e1 := parse_loop program (0 : Stack) 1 SL.s1 SL.s2 (by decide) rfl [s]
    (EncodedCommunication.field u ++ r) S0 none () (by simp [S0, hinW, EncodedComplexity.pair])
  set S1 := Function.update (Function.update S0 1 ([s].reverse ++ S0 1)) 0
    (EncodedCommunication.field u ++ r) with hS1
  have h11 : S1 1 = [s] := by simp [hS1, S0]
  have hraw : rawInit (0 : Stack) SL.s1 ((none, ()) : Control) inW =
      ⟨some SL.s1, (none, ()), S0⟩ := rfl
  cases s with
  | true =>
      have e2 : advance program ⟨some SL.s2, ((some false, ()) : Control), S1⟩ =
          ⟨some SL.done, ((some true, ()) : Control), Function.update S1 1 []⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, setBit, h11]
      set S2 := Function.update S1 1 [] with hS2
      have e3 := halt_step program SL.done rfl ((some true, ()) : Control) S2
      have hrun := iter_chain (iter_chain e1 (one_step' e2)) (one_step' e3)
      rw [← hraw] at hrun
      refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) SL.s1 ((none, ()) : Control)
        program inW _ _ _ ?_ (by rw [hrun]) ?_
      · simp only [List.length_singleton]
        omega
      · rw [hrun]
        simp [hS2, hS1, selWord, EncodedComplexity.pair]
  | false =>
      have e2 : advance program ⟨some SL.s2, ((some false, ()) : Control), S1⟩ =
          ⟨some SL.s3, ((some false, ()) : Control), Function.update S1 1 []⟩ := by
        simp [advance, TM2.step, TM2.stepAux, program, setBit, h11]
      set S2 := Function.update S1 1 [] with hS2
      have e3 := parse_loop program (0 : Stack) 2 SL.s3 SL.s4 (by decide) rfl u r S2 (some false)
        () (by simp [hS2, hS1])
      set S3 := Function.update (Function.update S2 2 (u.reverse ++ S2 2)) 0 r with hS3
      have e4 := pushFalse_step program (0 : Stack) SL.s4 SL.done rfl (some false, ()) S3
      set S4 := Function.update S3 0 (false :: S3 0) with hS4
      have e5 := halt_step program SL.done rfl ((some false, ()) : Control) S4
      have hrun := iter_chain (iter_chain (iter_chain (iter_chain e1 (one_step' e2)) e3)
        (one_step' e4)) (one_step' e5)
      rw [← hraw] at hrun
      refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) SL.s1 ((none, ()) : Control)
        program inW _ _ _ ?_ (by rw [hrun]) ?_
      · simp only [List.length_singleton]
        omega
      · rw [hrun]
        simp [hS4, hS3, selWord, EncodedComplexity.pair, EncodedCommunication.field]

end Select

open Select (selWord)

/-- The sum of the two fixed-formula lengths of the admitted router at threshold `N₁`. -/
def phiLen (N₁ : ℕ) : ℕ := (Front.phi N₁ true).length + (Front.phi N₁ false).length

/-- THE fixed raw routing machine `w ↦ scanTarget N₁ (selWord (sparseAnswer K w) w)`. -/
def route3 (K N₁ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition Paper2.AEth3.RawDup.machine
    (BitMachineComposition.composition
      (Paper2.Unit4Shell.PairMap.machine (AFront.Sparse.sparseCheck K))
      (BitMachineComposition.composition Select.machine
        (BitMachineComposition.composition (AFront.Route.frontRoute N₁) Paper2.AEth3.Fst.machine)))

/-- The routed word. -/
def route3Out (K N₁ : ℕ) (w : List Bool) : List Bool :=
  Front.scanTarget N₁ (selWord (AFront.Sparse.sparseAnswer K w) w)

/-- The routed formula. -/
def routed4 (K N₁ : ℕ) (w : List Bool) : EncodedCNF.Formula :=
  AFront.Route.routedFormula N₁ (selWord (AFront.Sparse.sparseAnswer K w) w)

theorem route3Out_eq (K N₁ : ℕ) (w : List Bool) :
    route3Out K N₁ w = EncodedCNF.encode (routed4 K N₁ w) :=
  AFront.Route.scanTarget_eq_encode N₁ _

/-- The cubic clock of the router, in `|w|` only. -/
def route3Time (_K N₁ : ℕ) (w : List Bool) : ℕ := (3000 + 30 * phiLen N₁) * (w.length + 1) ^ 3

theorem selWord_length (s : Bool) (w : List Bool) : (selWord s w).length ≤ w.length := by
  cases s <;> simp [selWord]

/-- **The total router is correct and charged on EVERY word.** -/
theorem route3_outputs (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) :
    (route3 K N₁).OutputsWithin w (route3Out K N₁ w) (route3Time K N₁ w) := by
  set s := AFront.Sparse.sparseAnswer K w with hs
  set u := selWord s w with hu
  set v := Front.scanTarget N₁ u with hv
  have h1 := Paper2.AEth3.RawDup.machine_outputs w
  have h2 := Paper2.Unit4Shell.PairMap.machine_outputs (M := AFront.Sparse.sparseCheck K) w [s]
    (EncodedComplexity.pair w []) _ (AFront.Sparse.sparseCheck_outputs_poly K w)
  have h3 := Select.outputs s w []
  have h4 := AFront.Route.frontRoute_outputs_poly hN₁ u []
  have h5 := Paper2.AEth3.Fst.machine_outputs v []
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2
      (BitMachineComposition.composition_outputsWithin _ _ h3
        (BitMachineComposition.composition_outputsWithin _ _ h4 h5)))
  refine BitMachine.outputsWithin_mono _ hC ?_
  have hul : u.length ≤ w.length := selWord_length s w
  have hvl : v.length ≤ u.length + phiLen N₁ := by
    rw [hv]
    have := Front.scanTarget_length hN₁ u
    unfold phiLen
    omega
  simp only [EncodedComplexity.pair_length, List.length_nil, List.length_singleton]
  set Y := (w.length + 1) ^ 3 with hY
  have hY1 : w.length + 1 ≤ Y := by
    calc w.length + 1 = (w.length + 1) ^ 1 := (pow_one _).symm
      _ ≤ (w.length + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hX : (2 * u.length + 1 + 0 + 1) ^ 3 ≤ 8 * Y := by
    have : 2 * u.length + 1 + 0 + 1 ≤ 2 * (w.length + 1) := by omega
    calc (2 * u.length + 1 + 0 + 1) ^ 3 ≤ (2 * (w.length + 1)) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 * Y := by rw [hY]; ring
  have hP := Nat.mul_le_mul_left (300 + 2 * phiLen N₁) hX
  have hPY : phiLen N₁ ≤ phiLen N₁ * Y := Nat.le_mul_of_pos_right _ (by omega)
  unfold route3Time phiLen at *
  nlinarith

theorem decode_nil : EncodedCNF.decode [] = none := by
  simp [EncodedCNF.decode, EncodedGraph.readUnary]

/-! ## Properties of the routed formula -/

theorem routed4_valid (K : ℕ) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) (w : List Bool) : (routed4 K N₁ w).Valid :=
  AFront.Route.routedFormula_valid hN₁ _

theorem routed4_variables (K N₁ : ℕ) (w : List Bool) : N₁ ≤ (routed4 K N₁ w).variables :=
  AFront.Route.routedFormula_variables _

theorem phiFormula_sparse (K N₁ : ℕ) (hK : 2 ≤ K * N₁) (b : Bool) :
    (Front.phiFormula N₁ b).clauses.length ≤ K * (Front.phiFormula N₁ b).variables := by
  cases b
  · simp [Front.phiFormula]
    omega
  · simp [Front.phiFormula]

/-- The routed formula is ALWAYS `K`-sparse. -/
theorem routed4_sparse (K N₁ : ℕ) (hK : 2 ≤ K * N₁) (w : List Bool) :
    (routed4 K N₁ w).clauses.length ≤ K * (routed4 K N₁ w).variables := by
  unfold routed4 AFront.Route.routedFormula
  cases hs : AFront.Sparse.sparseAnswer K w with
  | false =>
      simp only [selWord]
      exact phiFormula_sparse K N₁ hK false
  | true =>
      obtain ⟨f, hf, hsp⟩ := (AFront.Sparse.sparseAnswer_iff K w).1 hs
      simp only [selWord, if_true, hf]
      split
      · exact phiFormula_sparse K N₁ hK _
      · exact hsp

/-- On a sparse valid formula with at least `N₁` variables the routing is the identity. -/
theorem routed4_encode (K N₁ : ℕ) (Φ : EncodedCNF.Formula) (hv : Φ.Valid)
    (hsp : Φ.clauses.length ≤ K * Φ.variables) (hN : N₁ ≤ Φ.variables) :
    routed4 K N₁ (EncodedCNF.encode Φ) = Φ := by
  have hs : AFront.Sparse.sparseAnswer K (EncodedCNF.encode Φ) = true := by
    rw [AFront.Sparse.sparseAnswer_encode K Φ hv]
    simpa using hsp
  unfold routed4 AFront.Route.routedFormula
  simp only [hs, selWord, if_true, EncodedCNF.decode_encode Φ hv]
  simp [Nat.not_lt.mpr hN]

/-- On EVERY sparse valid formula the routing preserves satisfiability (the finite table). -/
theorem routed4_sat_iff (K : ℕ) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) (Φ : EncodedCNF.Formula) (hv : Φ.Valid)
    (hsp : Φ.clauses.length ≤ K * Φ.variables) :
    EncodedCNF.Satisfiable (routed4 K N₁ (EncodedCNF.encode Φ)) ↔
      EncodedCNF.encode Φ ∈ EncodedCNF.Language := by
  have hs : AFront.Sparse.sparseAnswer K (EncodedCNF.encode Φ) = true := by
    rw [AFront.Sparse.sparseAnswer_encode K Φ hv]
    simpa using hsp
  unfold routed4
  simp only [hs, selWord, if_true]
  exact AFront.Route.routedFormula_sat_iff hN₁ _

/-! ## The inner machine and the total front cut -/

/-- THE fixed inner machine: route, then the frozen a-eth-owner-3 inner machine. -/
def inner4 (K N₁ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (route3 K N₁) Paper2.AEth3.innerMachine

def inner4Time (K N₁ : ℕ) (w : List Bool) : ℕ :=
  route3Time K N₁ w + 2 * (route3Out K N₁ w).length + 2 +
    Paper2.AEth3.innerTime (routed4 K N₁ w)

theorem inner4_outputs (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w : List Bool) :
    (inner4 K N₁).OutputsWithin w (Paper2.AEth3.fOut (routed4 K N₁ w)) (inner4Time K N₁ w) := by
  have h1 := route3_outputs K N₁ hN₁ w
  have h2 := Paper2.AEth3.inner_outputs (routed4 K N₁ w)
  rw [← route3Out_eq] at h2
  exact BitMachineComposition.composition_outputsWithin _ _ h1 h2

/-- THE fixed total front cut. -/
def frontCut4 (K N₁ : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (Paper2.AEth2.Cut.machine (inner4 K N₁) 1 1)
    (Paper2.Unit4Shell.PairMap.machine Paper2.AEth3.Fst.machine)

/-- The front-cut clock: in `|w|` and the routed formula only (never the tape). -/
def frontTime4 (K N₁ : ℕ) (w : List Bool) : ℕ :=
  Paper2.AEth2.Cut.cutTimeG 1 1 (inner4 K N₁).pushBound w.length (inner4Time K N₁ w) +
    2 * (2 * (Paper2.AEth3.fOut (routed4 K N₁ w)).length + 1 +
      Paper2.AEth3.cutLen (routed4 K N₁ w)) + 2 +
    (2 * (Paper2.AEth3.fOut (routed4 K N₁ w)).length +
      (2 * (EncodedCNF.encode (routed4 K N₁ w)).length + 3) +
      2 * (EncodedCNF.encode (routed4 K N₁ w)).length + 6)

/-- **The total physical front cut.** For EVERY word `w` and EVERY raw tape `t` (any length), the fixed
machine `frontCut4 K N₁` prints `pair (encode Φ') (t.take (cutLen Φ'))`, `Φ' = routed4 K N₁ w`, within
`frontTime4 K N₁ w`, which does not depend on `t`. -/
theorem frontCut4_outputs (K N₁ : ℕ) (hN₁ : 1 ≤ N₁) (w t : List Bool) :
    (frontCut4 K N₁).OutputsWithin (EncodedComplexity.pair w t)
      (EncodedComplexity.pair (EncodedCNF.encode (routed4 K N₁ w))
        (t.take (Paper2.AEth3.cutLen (routed4 K N₁ w)))) (frontTime4 K N₁ w) := by
  have h1 := Paper2.AEth2.Cut.cut_outputs_gen (inner4 K N₁) 1 1
    (fun _ => Paper2.AEth3.fOut (routed4 K N₁ w)) (fun _ => inner4Time K N₁ w) w
    (inner4_outputs K N₁ hN₁ w) t
  have hL : 1 * ((Paper2.AEth3.fOut (routed4 K N₁ w)).length + 1) ^ 1 =
      Paper2.AEth3.cutLen (routed4 K N₁ w) := by simp [Paper2.AEth3.cutLen]
  simp only [hL] at h1
  have hF : Paper2.AEth3.Fst.machine.OutputsWithin (Paper2.AEth3.fOut (routed4 K N₁ w))
      (EncodedCNF.encode (routed4 K N₁ w))
      (2 * (EncodedCNF.encode (routed4 K N₁ w)).length + 3) :=
    Paper2.AEth3.Fst.machine_outputs (EncodedCNF.encode (routed4 K N₁ w)) _
  have h2 := Paper2.Unit4Shell.PairMap.machine_outputs (M := Paper2.AEth3.Fst.machine)
    (Paper2.AEth3.fOut (routed4 K N₁ w)) (EncodedCNF.encode (routed4 K N₁ w))
    (t.take (Paper2.AEth3.cutLen (routed4 K N₁ w))) _ hF
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  refine BitMachine.outputsWithin_mono _ hC ?_
  have htk : (t.take (Paper2.AEth3.cutLen (routed4 K N₁ w))).length ≤
      Paper2.AEth3.cutLen (routed4 K N₁ w) := List.length_take_le _ _
  simp only [frontTime4, EncodedComplexity.pair_length]
  omega

end Paper2.AEth4

end

#print axioms Paper2.AEth4.Select.outputs
#print axioms Paper2.AEth4.route3_outputs
#print axioms Paper2.AEth4.decode_nil
#print axioms Paper2.AEth4.routed4_valid
#print axioms Paper2.AEth4.routed4_variables
#print axioms Paper2.AEth4.routed4_sparse
#print axioms Paper2.AEth4.routed4_encode
#print axioms Paper2.AEth4.routed4_sat_iff
#print axioms Paper2.AEth4.inner4_outputs
#print axioms Paper2.AEth4.frontCut4_outputs
