import CurrentAdditive.ZeroPadIdentity
import CurrentAdditive.V38PaddedBank
import CurrentAdditive.CanonicalPackedFieldBits

namespace CurrentAdditive.V38ZeroPad

open CurrentAdditive.SmallBias CurrentAdditive.V38Machine
open CurrentAdditive.V38Executable
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable

set_option maxHeartbeats 1000000

theorem ofFn_prod {α : Type*} (A B : ℕ) (f : Fin (A * B) → α) :
    List.ofFn f =
      (List.ofFn fun a : Fin A => List.ofFn fun b : Fin B =>
        f (finProdFinEquiv (a, b))).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext a
  apply congrArg List.ofFn
  funext b
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem blockBits_comp_prod (A B : ℕ) (f : Fin (A * B) → Bool) :
    blockBits A B (fun a b => f (finProdFinEquiv (a, b))) = List.ofFn f := by
  unfold blockBits
  congr 1
  funext z
  change f (finProdFinEquiv (finProdFinEquiv.symm z)) = f z
  simp only [Equiv.apply_symm_apply]

theorem nested_blockBits (L H K : ℕ)
    (f : Fin L → Fin (H * K) → Bool) :
    blockBits L (H * K) f =
      blockBits (L * H) K (fun q p =>
        let la := finProdFinEquiv.symm q
        f la.1 (finProdFinEquiv (la.2, p))) := by
  rw [blockBits_eq_flatten, blockBits_eq_flatten]
  rw [ofFn_prod L H]
  simp only [Equiv.symm_apply_apply]
  rw [List.flatten_flatten, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext l
  change List.ofFn (f l) =
    (List.ofFn fun a : Fin H => List.ofFn fun p : Fin K =>
      f l (finProdFinEquiv (a, p))).flatten
  exact ofFn_prod H K (f l)

theorem padded_comp_prod (L H K : ℕ)
    (f : Fin L → Fin H → Fin K → Bool) :
    blockBits L (H * (K + 1)) (fun l ap =>
      let ap' := finProdFinEquiv.symm ap
      Fin.cases false (f l ap'.1) ap'.2) =
      paddedBlockBits (L * H) K (fun q p =>
        let la := finProdFinEquiv.symm q
        f la.1 la.2 p) := by
  rw [nested_blockBits]
  unfold blockBits paddedBlockBits
  congr 1
  funext z
  simp only [Equiv.symm_apply_apply]

def genuineBlock (b t d modulus : ℕ) :
    Fin (((2 ^ d) ^ 2) * 2 ^ b) → Fin (2 ^ t * 2 ^ t) → Bool :=
  fun q p =>
    let la := finProdFinEquiv.symm q
    v38PrintedPairWord b t d modulus la.1 (la.2, p)

theorem packed_eq_blocks (b t d modulus : ℕ) :
    packedFieldBits d modulus (v38PositionCount b t) =
      blockBits (((2 ^ d) ^ 2) * 2 ^ b) (2 ^ t * 2 ^ t)
        (genuineBlock b t d modulus) := by
  change blockBits ((2 ^ d) ^ 2) (2 ^ b * (2 ^ t * 2 ^ t))
    (fun l j =>
      let xy := (printerPairLabel d).symm l
      FiniteFieldConstructor.BitPrinter.bit d modulus xy.1.val xy.2.val j.val) = _
  rw [nested_blockBits]
  rfl

theorem wordAtPosition_eq_cases {H K n : ℕ}
    (W : Fin n → Fin H × Fin K → Bool)
    (l : Fin n) (a : Fin H) (p : Fin (K + 1)) :
    wordAtPosition W l a p = Fin.cases false (fun i => W l (a, i)) p := by
  cases p using Fin.cases with
  | zero => simp [wordAtPosition]
  | succ i => simp [wordAtPosition]

theorem padded_eq_blocks (b t d modulus : ℕ) :
    paddedBits b t d modulus =
      paddedBlockBits (((2 ^ d) ^ 2) * 2 ^ b) (2 ^ t * 2 ^ t)
        (genuineBlock b t d modulus) := by
  change blockBits ((2 ^ d) ^ 2) (2 ^ b * (2 ^ t * 2 ^ t + 1))
    (fun l ap => let ap' := finProdFinEquiv.symm ap
      wordAtPosition (v38PrintedPairWord b t d modulus) l ap'.1 ap'.2) = _
  simp only [wordAtPosition_eq_cases]
  exact padded_comp_prod ((2 ^ d) ^ 2) (2 ^ b) (2 ^ t * 2 ^ t)
    (fun l a i => v38PrintedPairWord b t d modulus l (a, i))

theorem actual_padded_identity (b t d modulus : ℕ) :
    padFrom (⟨0, by positivity⟩ : Fin (2 ^ t * 2 ^ t))
      (packedFieldBits d modulus (v38PositionCount b t)) =
      paddedBits b t d modulus := by
  rw [packed_eq_blocks, padFrom_blockBits, padded_eq_blocks]

theorem actual_padded_machine (b t d modulus : ℕ) :
    (machine (2 ^ t * 2 ^ t) (by positivity)).OutputsWithin
      (packedFieldBits d modulus (v38PositionCount b t))
      (paddedBits b t d modulus)
      (3 * (((2 ^ d) ^ 2) * v38PositionCount b t) + 2) := by
  have h := machine_outputs (2 ^ t * 2 ^ t) (by positivity)
    (packedFieldBits d modulus (v38PositionCount b t))
  rw [actual_padded_identity, packedFieldBits_length] at h
  exact h

#print axioms actual_padded_identity
#print axioms actual_padded_machine

end CurrentAdditive.V38ZeroPad
