import EthInapproximability.CurrentPaper.SamplerExactPayloadOrder
import EthInapproximability.CurrentPaper.SamplerMachineBlockReverse

/-!
# Exact physical arrays for both sampler call sites

The table controller writes bits low-first within each alphabet symbol. The
exact-NP payload stores each second-family symbol most-significant-bit first.
This file identifies the literal lists, not just their indexed values.
-/

namespace EthInapproximability.CurrentPaper.SamplerExactPayloadArrays

open ExecutableSmallBiasSampler SamplerMachine
open SamplerSeedEnumeration SamplerExactPayloadOrder

private theorem reverse_ofFn {α : Type*} {a : ℕ} (f : Fin a → α) :
    (List.ofFn f).reverse = List.ofFn (fun j : Fin a => f j.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.rev]
    omega

private theorem rowMajor_nested {α : Type*} {m n : ℕ}
    (f : Fin m → Fin n → α) :
    MatrixMaterialization.rowMajor f =
      (List.ofFn fun x : Fin m => List.ofFn fun y : Fin n => f x y).flatten := by
  unfold MatrixMaterialization.rowMajor
  exact ofFn_pair_labels (fun p => f p.1 p.2)

private theorem indexedTraceBits_cast {L L' B : ℕ} (h : L = L')
    (seed : Fin ((2 ^ SmallBiasSampler.fieldExponent L B) ^ 2)) (i : Fin L) :
    indexedTraceBits L B seed i =
      indexedTraceBits L' B
        (Fin.cast (by rw [h]) seed) (Fin.cast h i) := by
  cases h
  rfl

def secondBlocks (a t d : ℕ) : List (List Bool) :=
  MatrixMaterialization.rowMajor (fun z : Fin (SmallBiasSampler.exactSecondSize a t d) =>
    fun α : Fin d => List.ofFn fun j : Fin a =>
      encodeBit (indexedTraceBits (d * a)
        (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t) z
        (finProdFinEquiv (α, j))))

theorem secondBlocks_width (a t d : ℕ) :
    ∀ b ∈ secondBlocks a t d, b.length = a := by
  intro b hb
  simp only [secondBlocks, MatrixMaterialization.rowMajor, List.mem_ofFn] at hb
  obtain ⟨k, rfl⟩ := hb
  simp

theorem secondBlocks_length (a t d : ℕ) :
    (secondBlocks a t d).length = SmallBiasSampler.exactSecondSize a t d * d := by
  exact MatrixMaterialization.rowMajor_length _

theorem secondBlocks_reverse_flatten_length (a t d : ℕ) :
    ((secondBlocks a t d).reverse.flatten).length =
      SmallBiasSampler.exactSecondSize a t d * d * a := by
  simp [secondBlocks, MatrixMaterialization.rowMajor,
    List.length_flatten, List.map_ofFn, Function.comp_def]

theorem secondPayload_stepCount (a t d : ℕ) :
    (secondBlocks a t d).length * SamplerMachineBlockReverse.blockStep a +
      ((secondBlocks a t d).reverse.flatten).length + 2 =
    SmallBiasSampler.exactSecondSize a t d * d * (3 * a + 3) + 2 := by
  rw [secondBlocks_length, secondBlocks_reverse_flatten_length]
  unfold SamplerMachineBlockReverse.blockStep
  ring

theorem secondBlocks_trace (a t d : ℕ) :
    (secondBlocks a t d).flatten =
      SamplerSeedEnumeration.counterTraceTable
        (SmallBiasSampler.fieldExponent (d * a)
          (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t)) (d * a) := by
  rw [counterTraceTable_indexed]
  unfold secondBlocks
  rw [rowMajor_nested]
  simp only [SmallBiasSampler.exactSecondSize, SmallBiasSampler.samplerSize]
  rw [List.flatten_flatten]
  simp only [List.map_ofFn, Function.comp_def]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext z
  simpa only [Equiv.apply_symm_apply] using (ofFn_pair_labels (fun p : Fin d × Fin a =>
    encodeBit (indexedTraceBits (d * a)
      (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t) z
      (finProdFinEquiv p)))).symm

theorem secondBlocks_stored (a t₁ t₂ d n : ℕ) (v : Fin n → Fin d → Bool) :
    ((secondBlocks a t₂ d).map List.reverse).flatten =
      (MatrixMaterialization.storeBits
        (exactFirstFamily a t₁ d) (exactSecondFamily a t₂ d) v).second := by
  change ((MatrixMaterialization.rowMajor
    (fun z : Fin (SmallBiasSampler.exactSecondSize a t₂ d) =>
      fun α : Fin d => List.ofFn fun j : Fin a =>
        encodeBit (indexedTraceBits (d * a)
          (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂) z
          (finProdFinEquiv (α, j))))).map List.reverse).flatten =
    MatrixMaterialization.rowMajor
      (fun k : Fin (SmallBiasSampler.exactSecondSize a t₂ d * d) =>
        fun j : Fin a =>
          (MatrixMaterialization.wordCode a).symm
            (exactSecondFamily a t₂ d (finProdFinEquiv.symm k).1
              (finProdFinEquiv.symm k).2) j)
  rw [MatrixMaterialization.rowMajor_map, rowMajor_nested, rowMajor_nested]
  have hn := ofFn_pair_labels (fun p :
      Fin (SmallBiasSampler.exactSecondSize a t₂ d) × Fin d =>
    (List.ofFn fun j : Fin a =>
      encodeBit (indexedTraceBits (d * a)
        (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂) p.1
        (finProdFinEquiv (p.2, j)))).reverse)
  rw [← hn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext k
  rw [reverse_ofFn]
  apply congrArg List.ofFn
  funext j
  exact (wordCode_block a
    (fun r => indexedTraceBits (d * a)
      (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv ((finProdFinEquiv.symm k).2, r))) j).symm

theorem firstTrace_stored (a t₁ t₂ d n : ℕ) (v : Fin n → Fin d → Bool) :
    SamplerSeedEnumeration.counterTraceTable
      (SmallBiasSampler.fieldExponent (ExactConstruction.prefixLength a + 3)
        (SmallBiasSampler.exactDenominator d * (2 ^ 1) ^ t₁))
      (ExactConstruction.prefixLength a + 3) =
    (MatrixMaterialization.storeBits
      (exactFirstFamily a t₁ d) (exactSecondFamily a t₂ d) v).first := by
  rw [counterTraceTable_indexed]
  change _ = MatrixMaterialization.rowMajor (exactFirstFamily a t₁ d)
  rw [rowMajor_nested]
  simp only [SmallBiasSampler.exactFirstSize, SmallBiasSampler.samplerSize, mul_one]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext z
  apply congrArg List.ofFn
  funext i
  let z' : Fin (SmallBiasSampler.exactFirstSize a t₁ d) :=
    Fin.cast (by simp [SmallBiasSampler.exactFirstSize, SmallBiasSampler.samplerSize]) z
  have h := (first_family_bit a t₁ d z' i).symm
  have hL : (ExactConstruction.prefixLength a + 3) * 1 =
      ExactConstruction.prefixLength a + 3 := by omega
  have ht := indexedTraceBits_cast hL z' (finProdFinEquiv (i, (0 : Fin 1)))
  rw [ht] at h
  have hi : (Fin.cast hL (finProdFinEquiv (i, (0 : Fin 1)))) = i := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val]
  rw [hi] at h
  simpa only [z', Fin.cast] using h

theorem run_secondPayload (a t₁ t₂ d n : ℕ) (ha : 0 < a)
    (v : Fin n → Fin d → Bool) :
    SamplerMachineBlockReverse.run
      ((secondBlocks a t₂ d).length * SamplerMachineBlockReverse.blockStep a +
        ((secondBlocks a t₂ d).reverse.flatten).length + 2)
      (SamplerMachineBlockReverse.cfg (some .check)
        SamplerMachineBlockReverse.initial
        (SamplerSeedEnumeration.counterTraceTable
          (SmallBiasSampler.fieldExponent (d * a)
            (SmallBiasSampler.exactDenominator d * (2 ^ a) ^ t₂)) (d * a))
        (List.replicate a true) [] [] [] []) =
    SamplerMachineBlockReverse.cfg none SamplerMachineBlockReverse.initial
      [] (List.replicate a true) [] [] []
      (MatrixMaterialization.storeBits
        (exactFirstFamily a t₁ d) (exactSecondFamily a t₂ d) v).second := by
  have h := SamplerMachineBlockReverse.run_blocks a ha
    (secondBlocks a t₂ d) (secondBlocks_width a t₂ d)
  rw [secondBlocks_trace, secondBlocks_stored] at h
  exact h

end EthInapproximability.CurrentPaper.SamplerExactPayloadArrays
