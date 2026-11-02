import Paper2.NPTruncRun
import Paper2.AModelTape

/-!
An advice-free random-tape model with exactly the author's D-A1 quantifiers.
One finite Boolean-stack machine is required to halt in fixed polynomial time
on every prescribed pair, but no behaviour on malformed or non-prescribed
pair words is assumed. The physical pullback uses the admitted truncation
program and charges its run, intermediate copying, and the inner run.
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace Paper2.SelectedTape

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

structure Algorithm where
  cR : ℕ
  dR : ℕ
  cT : ℕ
  dT : ℕ
  machine : BitMachine.Machine
  output : List Bool → List Bool → List Bool
  runs : ∀ x (t : Fin (cR * (x.length + 1) ^ dR) → Bool),
    machine.OutputsWithin (pair x (List.ofFn t)) (output x (List.ofFn t))
      (cT * (x.length + 1) ^ dT)

def Algorithm.tapeLength (A : Algorithm) (x : List Bool) : ℕ :=
  A.cR * (x.length + 1) ^ A.dR

noncomputable def Algorithm.prob (A : Algorithm) (x : List Bool)
    (E : List Bool → Prop) : ℝ :=
  (Paper2.Unit4Shell.Definitions.uniformTape (A.tapeLength x)).prob
    (fun t => E (A.output x (List.ofFn t)))

def Algorithm.Decides (A : Algorithm) (L : BinaryLanguage) (err : ℝ) : Prop :=
  ∀ x, (x ∈ L → 1 - err ≤ A.prob x (· = [true])) ∧
    (x ∉ L → A.prob x (· = [true]) ≤ err)

def InBPP (L : BinaryLanguage) : Prop :=
  ∃ A : Algorithm, A.Decides L (1 / 3)

private noncomputable def sourceMachine {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) : BitMachine.Machine := Classical.choose hf
private noncomputable def sourceC {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) : ℕ := Classical.choose (Classical.choose_spec hf)
private noncomputable def sourceD {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec hf))
private theorem sourceRuns {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) :
    (sourceMachine hf).ComputesWithin f
      (fun n => sourceC hf * (n + 1) ^ sourceD hf) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hf))

private noncomputable def outputC {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) : ℕ :=
  Classical.choose (ComplexityReductionClosure.polytime_output_length hf)
private noncomputable def outputD {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) : ℕ :=
  Classical.choose (Classical.choose_spec
    (ComplexityReductionClosure.polytime_output_length hf))
private theorem outputBound {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (x : List Bool) :
    (f x).length ≤ outputC hf * (x.length + 1) ^ outputD hf :=
  Classical.choose_spec (Classical.choose_spec
    (ComplexityReductionClosure.polytime_output_length hf)) x

private def sourceSize {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (n : ℕ) : ℕ :=
  outputC hf * (n + 1) ^ outputD hf

private def outerTape (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (n : ℕ) : ℕ :=
  (A.cR * (outputC hf + 1) ^ A.dR) * (n + 1) ^ ((outputD hf + 1) * A.dR)

theorem inner_le_outer (f : List Bool → List Bool) (hf : BitMachine.Polytime f)
    (A : Algorithm) (x : List Bool) :
    A.tapeLength (f x) ≤ outerTape A hf x.length := by
  let cF := outputC hf
  let dF := outputD hf
  change A.cR * ((f x).length + 1) ^ A.dR ≤
    (A.cR * (cF + 1) ^ A.dR) * (x.length + 1) ^ ((dF + 1) * A.dR)
  let N := x.length + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hNp : N ^ dF ≤ N ^ (dF + 1) := Nat.pow_le_pow_right hN (by omega)
  have hfx : (f x).length + 1 ≤ (cF + 1) * N ^ (dF + 1) := by
    have hlen := outputBound hf x
    change (f x).length ≤ cF * N ^ dF at hlen
    have hN1 : 1 ≤ N ^ (dF + 1) := Nat.one_le_pow _ _ hN
    calc
      (f x).length + 1 ≤ cF * N ^ dF + 1 := by omega
      _ ≤ cF * N ^ (dF + 1) + N ^ (dF + 1) := by
        have hc := Nat.mul_le_mul_left cF hNp
        omega
      _ = (cF + 1) * N ^ (dF + 1) := by ring
  calc
    A.cR * ((f x).length + 1) ^ A.dR ≤
        A.cR * ((cF + 1) * N ^ (dF + 1)) ^ A.dR := by gcongr
    _ = (A.cR * (cF + 1) ^ A.dR) * N ^ ((dF + 1) * A.dR) := by
      rw [mul_pow, ← pow_mul]; ring

private def codeSize (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (n : ℕ) : ℕ :=
  2 * n + 1 + outerTape A hf n

private def preTime (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (n : ℕ) : ℕ :=
  NPOwner1.Trunc.timeBound A.cR A.dR (sourceC hf) (sourceD hf)
    (sourceMachine hf).pushBound (codeSize A hf n)

private def fullTime (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (n : ℕ) : ℕ :=
  preTime A hf n +
    2 * (codeSize A hf n + preTime A hf n *
      (NPOwner1.Trunc.machine (sourceMachine hf) A.cR A.dR).pushBound) + 2 +
    A.cT * (sourceSize hf n + 1) ^ A.dT

private theorem fullTime_poly (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) :
    Paper2.Unit4Shell.Poly.PolyIn id (fullTime A hf) := by
  have hsource : Paper2.Unit4Shell.Poly.PolyIn id (sourceSize hf) := by
    unfold sourceSize
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  have hcode : Paper2.Unit4Shell.Poly.PolyIn id (codeSize A hf) := by
    unfold codeSize outerTape
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  have hraw : Paper2.Unit4Shell.Poly.PolyIn id
      (fun N => NPOwner1.Trunc.timeBound A.cR A.dR
        (sourceC hf) (sourceD hf) (sourceMachine hf).pushBound N) := by
    unfold NPOwner1.Trunc.timeBound
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  obtain ⟨C, D, hCD⟩ := hraw
  have hpreIn : Paper2.Unit4Shell.Poly.PolyIn (codeSize A hf) (preTime A hf) :=
    ⟨C, D, fun n => hCD (codeSize A hf n)⟩
  have hpre : Paper2.Unit4Shell.Poly.PolyIn id (preTime A hf) :=
    Paper2.Unit4Shell.Poly.transfer hcode hpreIn
  unfold fullTime
  repeat (first
    | exact hpre
    | exact hcode
    | exact hsource
    | exact Paper2.Unit4Shell.Poly.self
    | exact Paper2.Unit4Shell.Poly.const _
    | apply Paper2.Unit4Shell.Poly.add
    | apply Paper2.Unit4Shell.Poly.mul
    | apply Paper2.Unit4Shell.Poly.pow)

private def prefixFn (t : List Bool) (r : ℕ) (h : r ≤ t.length) : Fin r → Bool :=
  fun i => (t.take r)[i.val]'(by rw [List.length_take, Nat.min_eq_left h]; exact i.isLt)

private theorem ofFn_prefixFn (t : List Bool) (r : ℕ) (h : r ≤ t.length) :
    List.ofFn (prefixFn t r h) = t.take r := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [prefixFn]

private noncomputable def timeC (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) : ℕ := Classical.choose (fullTime_poly A hf)
private noncomputable def timeD (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) : ℕ :=
  Classical.choose (Classical.choose_spec (fullTime_poly A hf))
private theorem timeBound (A : Algorithm) {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (n : ℕ) :
    fullTime A hf n ≤ timeC A hf * (n + 1) ^ timeD A hf :=
  Classical.choose_spec (Classical.choose_spec (fullTime_poly A hf)) n

private theorem pullbackRuns (f : List Bool → List Bool) (hf : BitMachine.Polytime f)
    (A : Algorithm) :
    ∀ x (tape : Fin (outerTape A hf x.length) → Bool),
      (BitMachineComposition.composition
        (NPOwner1.Trunc.machine (sourceMachine hf) A.cR A.dR) A.machine).OutputsWithin
        (pair x (List.ofFn tape))
        (A.output (f x) ((List.ofFn tape).take (A.tapeLength (f x))))
        (timeC A hf * (x.length + 1) ^ timeD A hf) := by
  intro x tape
  let outer := List.ofFn tape
  have houter : outer.length = outerTape A hf x.length := by
    simp [outer, outerTape]
  have hinner : A.tapeLength (f x) ≤ outer.length := by
    rw [houter]
    exact inner_le_outer f hf A x
  let inner := prefixFn outer (A.tapeLength (f x)) hinner
  have hword : List.ofFn inner = outer.take (A.tapeLength (f x)) :=
    ofFn_prefixFn outer (A.tapeLength (f x)) hinner
  have hpre := NPOwner1.Trunc.machine_outputs (sourceMachine hf) A.cR A.dR
    f (sourceC hf) (sourceD hf) (sourceRuns hf) (pair x outer)
  have hcode : (pair x outer).length = codeSize A hf x.length := by
    rw [pair_length, houter]
    rfl
  rw [hcode] at hpre
  have hmid := BitMachine.output_length_bound
    (NPOwner1.Trunc.machine (sourceMachine hf) A.cR A.dR) hpre
  have htarget : A.machine.OutputsWithin
      (pair (f x) (outer.take (A.tapeLength (f x))))
      (A.output (f x) (outer.take (A.tapeLength (f x))))
      (A.cT * ((f x).length + 1) ^ A.dT) := by
    let P := fun w : List Bool => A.machine.OutputsWithin (pair (f x) w)
      (A.output (f x) w) (A.cT * ((f x).length + 1) ^ A.dT)
    exact (congrArg P hword).mp (A.runs (f x) inner)
  have hresult : NPOwner1.Trunc.result A.cR A.dR f (pair x outer) =
      pair (f x) (outer.take (A.tapeLength (f x))) := by
    simpa [Algorithm.tapeLength] using NPOwner1.Trunc.result_pair A.cR A.dR f x outer
  rw [hresult] at hpre hmid
  have hcomp := BitMachineComposition.composition_outputsWithin
    (NPOwner1.Trunc.machine (sourceMachine hf) A.cR A.dR) A.machine hpre htarget
  have hfl := outputBound hf x
  have hsource : (f x).length ≤ sourceSize hf x.length := hfl
  have hinnerTime : A.cT * ((f x).length + 1) ^ A.dT ≤
      A.cT * (sourceSize hf x.length + 1) ^ A.dT := by gcongr
  have hmidBound : (pair (f x) (outer.take (A.tapeLength (f x)))).length ≤
      codeSize A hf x.length + preTime A hf x.length *
        (NPOwner1.Trunc.machine (sourceMachine hf) A.cR A.dR).pushBound := by
    simpa [hcode] using hmid
  have htotal : preTime A hf x.length +
      2 * (pair (f x) (outer.take (A.tapeLength (f x)))).length + 2 +
      A.cT * ((f x).length + 1) ^ A.dT ≤ fullTime A hf x.length := by
    unfold fullTime
    omega
  exact BitMachine.outputsWithin_mono _ hcomp ((htotal.trans (timeBound A hf x.length)))

/-- One physical composition; the fixed tape and clock coefficients are chosen
once from the reduction's code and time witnesses, before any input is seen. -/
noncomputable def pullback (f : List Bool → List Bool) (hf : BitMachine.Polytime f)
    (A : Algorithm) : Algorithm :=
    { cR := A.cR * (outputC hf + 1) ^ A.dR
      dR := (outputD hf + 1) * A.dR
      cT := timeC A hf
      dT := timeD A hf
      machine := BitMachineComposition.composition
        (NPOwner1.Trunc.machine (sourceMachine hf) A.cR A.dR) A.machine
      output := fun x tape => A.output (f x) (tape.take (A.tapeLength (f x)))
      runs := pullbackRuns f hf A }

theorem pullback_output (f : List Bool → List Bool) (hf : BitMachine.Polytime f)
    (A : Algorithm) (x tape : List Bool) :
    (pullback f hf A).output x tape =
      A.output (f x) (tape.take (A.tapeLength (f x))) := by
  rfl

theorem pullback_prob (f : List Bool → List Bool) (hf : BitMachine.Polytime f)
    (A : Algorithm) (x : List Bool) (E : List Bool → Prop) :
    (pullback f hf A).prob x E = A.prob (f x) E := by
  unfold Algorithm.prob
  have hlen := inner_le_outer f hf A x
  simp only [pullback_output]
  exact Paper2.AModel.uniformTape_take_prob hlen
    (fun tape => E (A.output (f x) tape))

theorem pullback_decides {L K : BinaryLanguage}
    (f : List Bool → List Bool) (hf : BitMachine.Polytime f)
    (hc : ∀ x, x ∈ L ↔ f x ∈ K) (A : Algorithm)
    (hA : A.Decides K (1 / 3)) :
    (pullback f hf A).Decides L (1 / 3) := by
  intro x
  rw [pullback_prob]
  exact ⟨fun h => (hA (f x)).1 ((hc x).mp h),
    fun h => (hA (f x)).2 (fun h' => h ((hc x).mpr h'))⟩

theorem reductionClosed :
    Paper2.Unit4Shell.ClassLemmas.ReductionClosed InBPP := by
  intro L K hred hK
  obtain ⟨f, hf, hc⟩ := hred
  obtain ⟨A, hA⟩ := hK
  exact ⟨pullback f hf A, pullback_decides f hf hc A hA⟩

theorem np_subset_inBPP {K : BinaryLanguage} (hK : NPHard K)
    (hmem : InBPP K) : ∀ L, InNP L → InBPP L :=
  Paper2.Unit4Shell.ClassLemmas.np_subset_of_hard_mem InBPP reductionClosed hK hmem

end Paper2.SelectedTape

#print axioms Paper2.SelectedTape.pullback_prob
#print axioms Paper2.SelectedTape.reductionClosed
#print axioms Paper2.SelectedTape.np_subset_inBPP
