import EthInapproximability.CurrentPaper.SamplerMachineProduct

/-!
Semantic certificate for the *arbitrary stored modulus* physical Horner
program. Unlike the old chosen-word theorem, this does not assume the old
exhaustive modulus choice. The numeral-code bridge to `BitPrinter.mul` is a
separate obligation.
-/

namespace CurrentAdditive.FiniteFieldMachine.HornerQuotientSemantics

open EthInapproximability.CurrentPaper
open ExecutableSmallBiasSampler SamplerMachine SamplerMachineProduct

noncomputable def evalAt {n : ℕ} (c : BinaryWord n) :
    BinaryWord n →ₗ[ZMod 2] AdjoinRoot (monicPolynomial n c) :=
  evalWordAt (AdjoinRoot.root (monicPolynomial n c))

theorem root_relation {n : ℕ} (c : BinaryWord n) :
    AdjoinRoot.root (monicPolynomial n c) ^ n + evalAt c c = 0 := by
  have h : (AdjoinRoot.mk (monicPolynomial n c)) (monicPolynomial n c) = 0 :=
    AdjoinRoot.mk_self
  change (AdjoinRoot.mk (monicPolynomial n c))
    (Polynomial.X ^ n + ∑ i : Fin n, Polynomial.monomial i.val (c i)) = 0 at h
  rw [map_add, map_pow, AdjoinRoot.mk_X, map_sum] at h
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X] at h
  simpa only [evalAt, evalWordAt_apply, AdjoinRoot.algebraMap_eq] using h

theorem eval_shiftWith {n : ℕ} (c u : BinaryWord n) :
    evalAt c (SamplerMachineShift.shiftWith c u) =
      AdjoinRoot.root (monicPolynomial n c) * evalAt c u := by
  cases n with
  | zero => simp [SamplerMachineShift.shiftWith, evalAt, evalWordAt_apply]
  | succ k =>
      have hs : SamplerMachineShift.shiftWith c u =
          (Fin.cons 0 (fun j : Fin k => u j.castSucc) : BinaryWord (k + 1)) -
            wordScale (u (Fin.last k)) c := rfl
      rw [hs]
      simp only [evalAt]
      rw [map_sub, evalWordAt_scale, evalWordAt_rawShift]
      have hroot := root_relation c
      change AdjoinRoot.root (monicPolynomial (k + 1) c) ^ (k + 1) +
        evalWordAt (AdjoinRoot.root (monicPolynomial (k + 1) c)) c = 0 at hroot
      linear_combination -algebraMap (ZMod 2) (AdjoinRoot (monicPolynomial (k + 1) c))
        (u (Fin.last k)) * hroot

theorem eval_hornerStep {n : ℕ} (c u a : BinaryWord n) (b : Bool) :
    evalAt c (hornerStep c u a b) =
      AdjoinRoot.root (monicPolynomial n c) * evalAt c a +
      algebraMap (ZMod 2) (AdjoinRoot (monicPolynomial n c))
        (SamplerHorner.decodeBit b) * evalAt c u := by
  change evalAt c (SamplerMachineShift.shiftWith c a +
    wordScale (SamplerHorner.decodeBit b) u) = _
  rw [map_add, eval_shiftWith]
  congr 1
  exact evalWordAt_scale _ _ _

theorem eval_horner_reverse {n : ℕ} (c u a : BinaryWord n) (bs : List Bool) :
    evalAt c (bs.reverse.foldl (hornerStep c u) a) =
      AdjoinRoot.root (monicPolynomial n c) ^ bs.length * evalAt c a +
        evalAt c u * SamplerHorner.evalBits (AdjoinRoot.root (monicPolynomial n c)) bs := by
  induction bs generalizing a with
  | nil => simp [SamplerHorner.evalBits]
  | cons b bs ih =>
      rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [eval_hornerStep]
      rw [ih]
      simp only [List.length_cons, SamplerHorner.evalBits, List.foldr_cons, pow_succ]
      ring

theorem eval_horner_mul {n : ℕ} (c u v : BinaryWord n) :
    evalAt c ((encodeWord v).reverse.foldl (hornerStep c u) (fun _ => 0)) =
      evalAt c u * evalAt c v := by
  have hz : evalAt c (fun _ : Fin n => 0) = 0 := map_zero (evalAt c)
  rw [eval_horner_reverse, SamplerHorner.evalBits_encodeWord, hz]
  simp [evalAt]

#print axioms eval_shiftWith
#print axioms eval_horner_mul

end CurrentAdditive.FiniteFieldMachine.HornerQuotientSemantics
