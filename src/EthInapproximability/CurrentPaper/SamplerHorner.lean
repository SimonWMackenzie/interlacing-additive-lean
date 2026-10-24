import EthInapproximability.CurrentPaper.SamplerMachine

/-!
# Reverse-coefficient Horner evaluation for the binary sampler

Source: locked v8 `E-exact-details.tex`, the finite-field coefficient arithmetic
used in the explicit construction of `lem:exact-families`. This module proves a
semantic identity for the finite controller's shift-and-add order. It makes no
machine-runtime assertion.
-/

namespace EthInapproximability.CurrentPaper.SamplerHorner

open SamplerMachine ExecutableSmallBiasSampler

def decodeBit (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] theorem decodeBit_encodeBit (a : ZMod 2) : decodeBit (encodeBit a) = a := by
  fin_cases a <;> decide

@[simp] theorem encodeBit_decodeBit (b : Bool) : encodeBit (decodeBit b) = b := by
  cases b <;> decide

/-- Read coefficients high-to-low, updating a fixed-width accumulator. -/
def horner {n : ℕ} (u : BinaryWord n) (bs : List Bool) (a : BinaryWord n) :
    BinaryWord n :=
  bs.foldl (fun a b => wordAdd (wordShift n a) (wordScale (decodeBit b) u)) a

/-- Polynomial value of a low-to-high Boolean coefficient list. -/
noncomputable def evalBits {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    (r : K) (bs : List Bool) : K :=
  bs.foldr (fun b z => algebraMap (ZMod 2) K (decodeBit b) + r * z) 0

theorem evalBits_encodeWord {K : Type*} [CommRing K] [Algebra (ZMod 2) K]
    (r : K) {m : ℕ} (v : BinaryWord m) : evalBits r (encodeWord v) = evalWordAt r v := by
  induction m with
  | zero => simp [encodeWord, evalBits, evalWordAt_apply]
  | succ m ih =>
      rw [encodeWord, List.ofFn_succ]
      change algebraMap (ZMod 2) K (decodeBit (encodeBit (v 0))) +
        r * evalBits r (encodeWord (fun i : Fin m => v i.succ)) = _
      rw [decodeBit_encodeBit, ih]
      simp only [evalWordAt_apply]
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring

theorem wordEval_horner_step {n : ℕ} (u a : BinaryWord n) (b : Bool) :
    wordEval n (wordAdd (wordShift n a) (wordScale (decodeBit b) u)) =
      AdjoinRoot.root (chosenPolynomial n) * wordEval n a +
        algebraMap (ZMod 2) (BinaryExtension n) (decodeBit b) * wordEval n u := by
  change wordEval n (wordShift n a + wordScale (decodeBit b) u) = _
  rw [map_add, wordEval_shift]
  congr 1
  exact evalWordAt_scale _ _ _

theorem wordEval_horner_reverse {n : ℕ} (u : BinaryWord n) (bs : List Bool)
    (a : BinaryWord n) :
    wordEval n (horner u bs.reverse a) =
      AdjoinRoot.root (chosenPolynomial n) ^ bs.length * wordEval n a +
        wordEval n u * evalBits (AdjoinRoot.root (chosenPolynomial n)) bs := by
  induction bs generalizing a with
  | nil => simp [horner, evalBits]
  | cons b bs ih =>
      rw [List.reverse_cons]
      simp only [horner, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [wordEval_horner_step]
      change AdjoinRoot.root (chosenPolynomial n) *
        wordEval n (horner u bs.reverse a) + _ = _
      rw [ih]
      simp only [List.length_cons, evalBits, List.foldr_cons, pow_succ]
      ring

/-- The high-to-low controller computes exactly the original multiplication
function, including the zero-dimensional total case. -/
theorem horner_encodeWord_reverse {n : ℕ} (u v : BinaryWord n) :
    horner u (encodeWord v).reverse (fun _ => 0) = wordMul n u v := by
  apply (wordEval_bijective n).injective
  rw [wordEval_horner_reverse, evalBits_encodeWord, wordEval_mul]
  change _ * wordEval n (0 : BinaryWord n) + wordEval n u * wordEval n v = _
  simp

end EthInapproximability.CurrentPaper.SamplerHorner
