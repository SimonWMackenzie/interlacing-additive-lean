import Paper2.AFrontTransducer
import Paper2.A4PairMap
import EthInapproximability.CurrentPaper.FrontSpec

/-!
# WP-U18a (iii): the all-input front of the composed decider (lane `owner:a-front-1`)

Private lane module, 27 September 2026. Paper A, lock v12. Author decisions of 27 September 2026
(`AUTHOR_DECISIONS_2026-09-27.md`): D-A1 (the decider is a deterministic `BitMachine` on
`pair input tape`) and D-A2 (the language is Paper B's `EncodedCNF.Language`, with the shared
all-input validator `CNFValidator*`).

Lock text covered (v12 `appendices/C-parameters.tex:204-206`, inside the proof of the
gap-colouring source lemma): "Empty or trivially decided input formulas can be sent directly
to fixed YES or NO graphs.  Every step is polynomial-time."

Two fixed machines, both built from ADMITTED production machines only
(`CNFValidator.machine`, `Front.scanMachine`, `BitMachineComposition.composition`,
`Paper2.Unit4Shell.PairMap.machine`) and the private generic transducer of `AFrontTransducer`:

* `frontReject`: on `pair w tape` it prints `pair w tape` unchanged (the reduction's input)
  when `w` is the canonical encoding of a valid formula, and the fixed reject word `[false]`
  otherwise. `[false]` is never a formula pair (`reject_ne_pair`).
* `frontRoute N`: on `pair w tape` it prints `pair (Front.scanTarget N w) tape`, i.e. malformed
  `w` goes to the fixed NO formula `phi N false`, valid formulas with fewer than `N` variables
  ("trivially decided": the admitted finite-control scanner `SmallArm` decides them) go to the
  fixed YES/NO formula `phi N (satAnswer w)`, and all other valid formulas pass unchanged. The
  routed first field is ALWAYS a valid formula with at least `N` variables, and its SAT answer
  equals that of `w`.

Every handoff is charged by `BitMachineComposition.composition_outputsWithin` and
`PairMap.machine_outputs`. No ledger row is closed by this module.
-/

namespace AFront.Route

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCNF
open AFront.Transducer

/-! ## The flag-strip transducer -/

inductive SS
  | start | tag | copy | sink
  deriving DecidableEq, Fintype

/-- Reads `field r ++ tape` for `r = CNFValidator.result w`. `field (true :: w) = true :: true ::
field w`: after the two tag bits it copies the rest verbatim. `field [false] = [true, false,
false]`: on the second bit `false` it emits the fixed reject word `[false]` and absorbs the rest. -/
def stripSpec : Spec SS where
  step s b _ := match s, b with
    | .start, true => .tag
    | .start, false => .sink
    | .tag, true => .copy
    | .tag, false => .sink
    | .copy, _ => .copy
    | .sink, _ => .sink
  emit s b := match s, b with
    | .tag, false => [false]
    | .copy, b => [b]
    | _, _ => []
  op _ _ := .keep
  fin _ := []
  incBy := 0
  bound := 1
  emit_le s b := by cases s <;> cases b <;> simp
  fin_le _ := by simp

theorem strip_copy (c : ℕ) (l : List Bool) : stripSpec.out .copy c l = l := by
  induction l with
  | nil => rw [Spec.out_nil]; rfl
  | cons b l ih =>
      rw [Spec.out_cons]
      show [b] ++ stripSpec.out .copy c l = b :: l
      rw [ih]; rfl

theorem strip_sink (c : ℕ) (l : List Bool) : stripSpec.out .sink c l = [] := by
  induction l with
  | nil => rw [Spec.out_nil]; rfl
  | cons b l ih =>
      rw [Spec.out_cons]
      show [] ++ stripSpec.out .sink c l = []
      rw [ih]; rfl

/-- The routing target of `frontReject`. -/
noncomputable def rejectTarget (w tape : List Bool) : List Bool :=
  if (EncodedCNF.decode w).isSome then EncodedComplexity.pair w tape else [false]

theorem strip_out (w tape : List Bool) :
    stripSpec.out .start 0 (EncodedComplexity.pair (CNFValidator.result w) tape) =
      rejectTarget w tape := by
  cases h : (EncodedCNF.decode w).isSome
  · have hr : CNFValidator.result w = [false] := by simp [CNFValidator.result, h]
    have ht : rejectTarget w tape = [false] := by simp [rejectTarget, h]
    rw [hr, ht]
    show stripSpec.out .start 0 (true :: false :: false :: tape) = [false]
    rw [Spec.out_cons, Spec.out_cons]
    show [] ++ ([false] ++ stripSpec.out .sink 0 (false :: tape)) = [false]
    rw [strip_sink]; rfl
  · have hr : CNFValidator.result w = true :: w := by simp [CNFValidator.result, h]
    have ht : rejectTarget w tape = EncodedComplexity.pair w tape := by simp [rejectTarget, h]
    rw [hr, ht]
    show stripSpec.out .start 0
      (true :: true :: (EncodedCommunication.field w ++ tape)) = EncodedCommunication.field w ++ tape
    rw [Spec.out_cons, Spec.out_cons]
    show [] ++ ([] ++ stripSpec.out .copy 0 (EncodedCommunication.field w ++ tape)) = _
    rw [strip_copy]; rfl

/-- The fixed reject word is never a formula pair. -/
theorem reject_ne_pair (w tape : List Bool) (hw : (EncodedCNF.decode w).isSome) :
    ([false] : List Bool) ≠ EncodedComplexity.pair w tape := by
  intro h
  cases w with
  | nil => simp [EncodedCNF.decode, EncodedGraph.readUnary] at hw
  | cons b w => simp [EncodedComplexity.pair, EncodedCommunication.field] at h

/-! ## `frontReject` -/

/-- THE fixed all-input front with a fixed reject output. -/
noncomputable def frontReject : BitMachine.Machine :=
  BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine CNFValidator.machine)
    (Transducer.machine stripSpec SS.start)

theorem result_length (w : List Bool) : (CNFValidator.result w).length ≤ w.length + 1 := by
  unfold CNFValidator.result; split <;> simp

/-- **All-input front, reject form (exact, charged).** For EVERY word `w` and EVERY tape, the
fixed machine `frontReject` prints on `pair w tape` exactly `pair w tape` if `w` decodes to a
(valid) formula and `[false]` otherwise, within the stated clock. -/
theorem frontReject_outputs (w tape : List Bool) :
    frontReject.OutputsWithin (EncodedComplexity.pair w tape) (rejectTarget w tape)
      ((2 * w.length + 250 * (w.length + 1) ^ 3 + 2 * (CNFValidator.result w).length + 6) +
        2 * (EncodedComplexity.pair (CNFValidator.result w) tape).length + 2 +
        (stripSpec.bound + 2) * ((EncodedComplexity.pair (CNFValidator.result w) tape).length + 1)) := by
  have h1 := Paper2.Unit4Shell.PairMap.machine_outputs CNFValidator.machine w
    (CNFValidator.result w) tape _ (CNFValidator.Runtime.outputs w)
  have h2 := Transducer.machine_outputs_linear stripSpec SS.start
    (EncodedComplexity.pair (CNFValidator.result w) tape)
  rw [strip_out] at h2
  exact BitMachineComposition.composition_outputsWithin _ _ h1 h2

/-- The same with a single cubic clock in the input length `X = |pair w tape|`. -/
theorem frontReject_outputs_poly (w tape : List Bool) :
    frontReject.OutputsWithin (EncodedComplexity.pair w tape) (rejectTarget w tape)
      (300 * ((EncodedComplexity.pair w tape).length + 1) ^ 3) := by
  apply BitMachine.outputsWithin_mono _ (frontReject_outputs w tape)
  have hr := result_length w
  have hX := EncodedComplexity.pair_length w tape
  have hY := EncodedComplexity.pair_length (CNFValidator.result w) tape
  set X := (EncodedComplexity.pair w tape).length
  have hb : stripSpec.bound = 1 := rfl
  have hw1 : w.length + 1 ≤ X + 1 := by omega
  have hc : (w.length + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left hw1 3
  have hl : X + 1 ≤ (X + 1) ^ 3 := by
    calc X + 1 = (X + 1) ^ 1 := (pow_one _).symm
      _ ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [hb]
  omega

/-- Membership reading of the reject form: on a formula pair the front passes the word
unchanged, and otherwise the output is the fixed reject word. -/
theorem rejectTarget_of_decode {w : List Bool} {f : Formula} (h : EncodedCNF.decode w = some f)
    (tape : List Bool) : rejectTarget w tape = EncodedComplexity.pair (encode f) tape := by
  simp [rejectTarget, h, (EncodedCNF.decode_spec h).2]

theorem rejectTarget_of_malformed {w : List Bool} (h : EncodedCNF.decode w = none)
    (tape : List Bool) : rejectTarget w tape = [false] := by
  simp [rejectTarget, h]

/-! ## `frontRoute N`: the lock sentence C-parameters.tex:204-206 -/

/-- THE fixed all-input routing front for threshold `N`. -/
noncomputable def frontRoute (N : ℕ) : BitMachine.Machine :=
  Paper2.Unit4Shell.PairMap.machine
    (BitMachineComposition.composition CNFValidator.machine (Front.scanMachine N))

/-- **All-input routing front (exact, charged).** For `N ≥ 1`, EVERY word `w` and EVERY tape,
the fixed machine `frontRoute N` prints on `pair w tape` exactly
`pair (Front.scanTarget N w) tape`. -/
theorem frontRoute_outputs {N : ℕ} (hN : 1 ≤ N) (w tape : List Bool) :
    (frontRoute N).OutputsWithin (EncodedComplexity.pair w tape)
      (EncodedComplexity.pair (Front.scanTarget N w) tape)
      (2 * w.length + (250 * (w.length + 1) ^ 3 + 2 * (CNFValidator.result w).length + 2 +
        (2 * w.length + 3)) + 2 * (Front.scanTarget N w).length + 6) := by
  have hc := BitMachineComposition.composition_outputsWithin CNFValidator.machine
    (Front.scanMachine N) (CNFValidator.Runtime.outputs w) (Front.scan_outputs hN w)
  exact Paper2.Unit4Shell.PairMap.machine_outputs _ w (Front.scanTarget N w) tape _ hc

/-- The same with one cubic clock in `X = |pair w tape|` plus the fixed-word constant. -/
theorem frontRoute_outputs_poly {N : ℕ} (hN : 1 ≤ N) (w tape : List Bool) :
    (frontRoute N).OutputsWithin (EncodedComplexity.pair w tape)
      (EncodedComplexity.pair (Front.scanTarget N w) tape)
      ((300 + 2 * ((Front.phi N true).length + (Front.phi N false).length)) *
        ((EncodedComplexity.pair w tape).length + 1) ^ 3) := by
  apply BitMachine.outputsWithin_mono _ (frontRoute_outputs hN w tape)
  have hr := result_length w
  have hs := Front.scanTarget_length hN w
  have hX := EncodedComplexity.pair_length w tape
  set X := (EncodedComplexity.pair w tape).length
  set K := (Front.phi N true).length + (Front.phi N false).length
  have hw1 : w.length + 1 ≤ X + 1 := by omega
  have hc : (w.length + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left hw1 3
  have hl : X + 1 ≤ (X + 1) ^ 3 := by
    calc X + 1 = (X + 1) ^ 1 := (pow_one _).symm
      _ ≤ (X + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (X + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hK : K ≤ K * (X + 1) ^ 3 := Nat.le_mul_of_pos_right K h1
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-! ### What the routing does (the lock's case split) -/

theorem scanTarget_malformed {N : ℕ} {w : List Bool} (h : EncodedCNF.decode w = none) :
    Front.scanTarget N w = Front.phi N false := by
  simp [Front.scanTarget, h]

theorem scanTarget_small {N : ℕ} {w : List Bool} {f : Formula}
    (h : EncodedCNF.decode w = some f) (hs : f.variables < N) :
    Front.scanTarget N w = Front.phi N (EncodedETHTail.satAnswer w) := by
  simp [Front.scanTarget, h, hs]

theorem scanTarget_large {N : ℕ} {w : List Bool} {f : Formula}
    (h : EncodedCNF.decode w = some f) (hl : N ≤ f.variables) :
    Front.scanTarget N w = w := by
  simp [Front.scanTarget, h, Nat.not_lt.mpr hl]

/-- The formula carried by the routed first field. -/
noncomputable def routedFormula (N : ℕ) (w : List Bool) : Formula :=
  match EncodedCNF.decode w with
  | none => Front.phiFormula N false
  | some f => if f.variables < N then Front.phiFormula N (EncodedETHTail.satAnswer w) else f

theorem routedFormula_valid {N : ℕ} (hN : 1 ≤ N) (w : List Bool) :
    (routedFormula N w).Valid := by
  unfold routedFormula
  cases h : EncodedCNF.decode w with
  | none => exact Front.phiFormula_valid hN false
  | some f =>
      simp only
      split
      · exact Front.phiFormula_valid hN _
      · exact (EncodedCNF.decode_spec h).1

theorem routedFormula_variables {N : ℕ} (w : List Bool) :
    N ≤ (routedFormula N w).variables := by
  unfold routedFormula
  cases h : EncodedCNF.decode w with
  | none => simp [Front.phiFormula]
  | some f =>
      simp only
      split
      · rename_i hs
        cases EncodedETHTail.satAnswer w <;> simp [Front.phiFormula]
      · omega

/-- The routed first field is the canonical encoding of the routed formula. -/
theorem scanTarget_eq_encode (N : ℕ) (w : List Bool) :
    Front.scanTarget N w = encode (routedFormula N w) := by
  unfold Front.scanTarget routedFormula
  cases h : EncodedCNF.decode w with
  | none => rfl
  | some f =>
      simp only
      split
      · rfl
      · exact (EncodedCNF.decode_spec h).2.symm

/-- The routing preserves the SAT answer on EVERY word. -/
theorem satAnswer_scanTarget {N : ℕ} (hN : 1 ≤ N) (w : List Bool) :
    EncodedETHTail.satAnswer (Front.scanTarget N w) = EncodedETHTail.satAnswer w := by
  unfold Front.scanTarget
  cases h : EncodedCNF.decode w with
  | none => simp only; rw [Front.satAnswer_phi hN, EncodedETHTail.satAnswer_malformed h]
  | some f =>
      simp only
      split
      · exact Front.satAnswer_phi hN _
      · rfl

/-- Language form: `scanTarget N w ∈ EncodedCNF.Language ↔ w ∈ EncodedCNF.Language`. -/
theorem scanTarget_mem_iff {N : ℕ} (hN : 1 ≤ N) (w : List Bool) :
    Front.scanTarget N w ∈ EncodedCNF.Language ↔ w ∈ EncodedCNF.Language := by
  have h := satAnswer_scanTarget hN w
  unfold EncodedETHTail.satAnswer at h
  exact decide_eq_decide.mp h

theorem routedFormula_sat_iff {N : ℕ} (hN : 1 ≤ N) (w : List Bool) :
    Satisfiable (routedFormula N w) ↔ w ∈ EncodedCNF.Language := by
  rw [← scanTarget_mem_iff hN w, scanTarget_eq_encode,
    EncodedCNF.encode_mem_iff _ (routedFormula_valid hN w)]

#print axioms frontReject_outputs
#print axioms frontReject_outputs_poly
#print axioms reject_ne_pair
#print axioms frontRoute_outputs
#print axioms frontRoute_outputs_poly
#print axioms routedFormula_valid
#print axioms routedFormula_variables
#print axioms scanTarget_eq_encode
#print axioms scanTarget_mem_iff
#print axioms routedFormula_sat_iff

end AFront.Route
