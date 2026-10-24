import Paper2.SelectedTape

/-!
Image-qualified randomized pullback in the selected-tape model. The second
finite machine need run only on actual outputs of the deterministic
preprocessor `f`, but the resulting algorithm runs on every original input
and every selected outer tape. No advice and no arbitrary-tape runtime premise.
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace Paper2.ImagePullback

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- One fixed second-stage finite machine, with a fixed monomial tape and
clock, required to run only on the image of the deterministic map `f`. -/
structure Stage (f : List Bool → List Bool) where
  cR : ℕ
  dR : ℕ
  cT : ℕ
  dT : ℕ
  machine : BitMachine.Machine
  output : List Bool → List Bool → List Bool
  runs : ∀ x (t : Fin (cR * ((f x).length + 1) ^ dR) → Bool),
    machine.OutputsWithin (pair (f x) (List.ofFn t))
      (output (f x) (List.ofFn t)) (cT * ((f x).length + 1) ^ dT)

def Stage.tapeLength {f : List Bool → List Bool} (A : Stage f) (y : List Bool) : ℕ :=
  A.cR * (y.length + 1) ^ A.dR

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

private def outerTape {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) (n : ℕ) : ℕ :=
  (A.cR * (outputC hf + 1) ^ A.dR) *
    (n + 1) ^ ((outputD hf + 1) * A.dR)

theorem inner_le_outer {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) (x : List Bool) :
    A.tapeLength (f x) ≤ outerTape hf A x.length := by
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

private def prepPoly {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) : BitMachine.Polytime (NPOwner1.Trunc.result A.cR A.dR f) :=
  NPOwner1.Trunc.polytime_result hf A.cR A.dR
private noncomputable def prepMachine {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) : BitMachine.Machine :=
  Classical.choose (prepPoly hf A)
private noncomputable def prepC {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) : ℕ :=
  Classical.choose (Classical.choose_spec (prepPoly hf A))
private noncomputable def prepD {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (prepPoly hf A)))
private theorem prepRuns {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) :
    (prepMachine hf A).ComputesWithin (NPOwner1.Trunc.result A.cR A.dR f)
      (fun n => prepC hf A * (n + 1) ^ prepD hf A) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (prepPoly hf A)))

private def codeSize {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) (n : ℕ) : ℕ := 2 * n + 1 + outerTape hf A n
private def preTime {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) (n : ℕ) : ℕ :=
  prepC hf A * (codeSize hf A n + 1) ^ prepD hf A
private def fullTime {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) (n : ℕ) : ℕ :=
  preTime hf A n +
    2 * (codeSize hf A n + preTime hf A n * (prepMachine hf A).pushBound) + 2 +
    A.cT * (sourceSize hf n + 1) ^ A.dT

private theorem fullTime_poly {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) :
    Paper2.Unit4Shell.Poly.PolyIn id (fullTime hf A) := by
  have hsource : Paper2.Unit4Shell.Poly.PolyIn id (sourceSize hf) := by
    unfold sourceSize
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  have hcode : Paper2.Unit4Shell.Poly.PolyIn id (codeSize hf A) := by
    unfold codeSize outerTape
    repeat (first
      | exact Paper2.Unit4Shell.Poly.self
      | exact Paper2.Unit4Shell.Poly.const _
      | apply Paper2.Unit4Shell.Poly.add
      | apply Paper2.Unit4Shell.Poly.mul
      | apply Paper2.Unit4Shell.Poly.pow)
  have hpre : Paper2.Unit4Shell.Poly.PolyIn id (preTime hf A) := by
    unfold preTime
    exact Paper2.Unit4Shell.Poly.mul (Paper2.Unit4Shell.Poly.const _)
      (Paper2.Unit4Shell.Poly.pow (Paper2.Unit4Shell.Poly.add hcode
        (Paper2.Unit4Shell.Poly.const 1)) _)
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

private noncomputable def timeC {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) : ℕ :=
  Classical.choose (fullTime_poly hf A)
private noncomputable def timeD {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) : ℕ :=
  Classical.choose (Classical.choose_spec (fullTime_poly hf A))
private theorem timeBound {f : List Bool → List Bool}
    (hf : BitMachine.Polytime f) (A : Stage f) (n : ℕ) :
    fullTime hf A n ≤ timeC hf A * (n + 1) ^ timeD hf A :=
  Classical.choose_spec (Classical.choose_spec (fullTime_poly hf A)) n

private def prefixFn (t : List Bool) (r : ℕ) (h : r ≤ t.length) : Fin r → Bool :=
  fun i => (t.take r)[i.val]'(by rw [List.length_take, Nat.min_eq_left h]; exact i.isLt)
private theorem ofFn_prefixFn (t : List Bool) (r : ℕ) (h : r ≤ t.length) :
    List.ofFn (prefixFn t r h) = t.take r := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [prefixFn]

private theorem imageRuns {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) :
    ∀ x (tape : Fin (outerTape hf A x.length) → Bool),
      (BitMachineComposition.composition (prepMachine hf A) A.machine).OutputsWithin
        (pair x (List.ofFn tape))
        (A.output (f x) ((List.ofFn tape).take (A.tapeLength (f x))))
        (timeC hf A * (x.length + 1) ^ timeD hf A) := by
  intro x tape
  let outer := List.ofFn tape
  have houter : outer.length = outerTape hf A x.length := by simp [outer]
  have hinner : A.tapeLength (f x) ≤ outer.length := by
    rw [houter]
    exact inner_le_outer hf A x
  let inner := prefixFn outer (A.tapeLength (f x)) hinner
  have hword : List.ofFn inner = outer.take (A.tapeLength (f x)) :=
    ofFn_prefixFn outer (A.tapeLength (f x)) hinner
  have hpre := prepRuns hf A (pair x outer)
  have hcode : (pair x outer).length = codeSize hf A x.length := by
    rw [pair_length, houter]
    rfl
  rw [hcode] at hpre
  have hmid := BitMachine.output_length_bound (prepMachine hf A) hpre
  have htarget : A.machine.OutputsWithin
      (pair (f x) (outer.take (A.tapeLength (f x))))
      (A.output (f x) (outer.take (A.tapeLength (f x))))
      (A.cT * ((f x).length + 1) ^ A.dT) := by
    let P := fun w : List Bool => A.machine.OutputsWithin (pair (f x) w)
      (A.output (f x) w) (A.cT * ((f x).length + 1) ^ A.dT)
    exact (congrArg P hword).mp (A.runs x inner)
  have hresult : NPOwner1.Trunc.result A.cR A.dR f (pair x outer) =
      pair (f x) (outer.take (A.tapeLength (f x))) := by
    simpa [Stage.tapeLength] using NPOwner1.Trunc.result_pair A.cR A.dR f x outer
  rw [hresult] at hpre hmid
  have hcomp := BitMachineComposition.composition_outputsWithin
    (prepMachine hf A) A.machine hpre htarget
  have hfl := outputBound hf x
  have hsource : (f x).length ≤ sourceSize hf x.length := hfl
  have hinnerTime : A.cT * ((f x).length + 1) ^ A.dT ≤
      A.cT * (sourceSize hf x.length + 1) ^ A.dT := by gcongr
  have hmidBound : (pair (f x) (outer.take (A.tapeLength (f x)))).length ≤
      codeSize hf A x.length + preTime hf A x.length * (prepMachine hf A).pushBound := by
    simpa [hcode] using hmid
  have htotal : preTime hf A x.length +
      2 * (pair (f x) (outer.take (A.tapeLength (f x)))).length + 2 +
      A.cT * ((f x).length + 1) ^ A.dT ≤ fullTime hf A x.length := by
    unfold fullTime
    omega
  exact BitMachine.outputsWithin_mono _ hcomp (htotal.trans (timeBound hf A x.length))

/-- An actual advice-free selected-tape algorithm on every original input. -/
noncomputable def pullback {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) : SelectedTape.Algorithm :=
  { cR := A.cR * (outputC hf + 1) ^ A.dR
    dR := (outputD hf + 1) * A.dR
    cT := timeC hf A
    dT := timeD hf A
    machine := BitMachineComposition.composition (prepMachine hf A) A.machine
    output := fun x tape => A.output (f x) (tape.take (A.tapeLength (f x)))
    runs := imageRuns hf A }

theorem pullback_prob {f : List Bool → List Bool} (hf : BitMachine.Polytime f)
    (A : Stage f) (x : List Bool) (E : List Bool → Prop) :
    (pullback hf A).prob x E =
      (Paper2.Unit4Shell.Definitions.uniformTape (A.tapeLength (f x))).prob
        (fun tape => E (A.output (f x) (List.ofFn tape))) := by
  unfold SelectedTape.Algorithm.prob
  have hlen := inner_le_outer hf A x
  change (Paper2.Unit4Shell.Definitions.uniformTape (outerTape hf A x.length)).prob
    (fun tape => E (A.output (f x) ((List.ofFn tape).take (A.tapeLength (f x))))) = _
  exact Paper2.AModel.uniformTape_take_prob hlen
    (fun tape => E (A.output (f x) tape))

#print axioms pullback
#print axioms pullback_prob

end Paper2.ImagePullback
