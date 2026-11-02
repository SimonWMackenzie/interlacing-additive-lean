import CurrentAdditive.ZeroPadMachine
import Mathlib.Data.List.OfFn

namespace CurrentAdditive.V38ZeroPad

set_option maxHeartbeats 1000000

theorem next_iterate_val {K : ℕ} (p : Fin K) (n : ℕ) :
    ((next^[n]) p).val = (p.val + n) % K := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt p.isLt]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [next, ih]
      rw [Nat.mod_add_mod]
      simp only [Nat.add_assoc]

theorem padFrom_append {K : ℕ} (p : Fin K) (xs ys : List Bool) :
    padFrom p (xs ++ ys) = padFrom p xs ++
      padFrom ((next^[xs.length]) p) ys := by
  induction xs generalizing p with
  | nil => simp [padFrom]
  | cons b bs ih =>
      simp only [List.cons_append, padFrom, List.length_cons]
      rw [ih]
      simp [List.append_assoc, Function.iterate_succ_apply]

theorem padFrom_no_wrap {K : ℕ} (p : Fin K) (bits : List Bool)
    (hp : 0 < p.val) (h : p.val + bits.length ≤ K) :
    padFrom p bits = bits := by
  induction bits generalizing p with
  | nil => rfl
  | cons b bs ih =>
      by_cases hn : bs = []
      · subst bs
        simp [padFrom, Nat.ne_of_gt hp]
      · have hlen : 0 < bs.length := List.length_pos_iff.mpr hn
        have hnext : (next p).val = p.val + 1 := by
          exact Nat.mod_eq_of_lt (by simpa using (show p.val + 1 < K by
            simp only [List.length_cons] at h; omega))
        simp only [padFrom, Nat.ne_of_gt hp, ↓reduceIte, List.nil_append]
        have htail : (next p).val + bs.length ≤ K := by
          simp only [hnext]
          simp only [List.length_cons] at h
          omega
        rw [ih (next p) (by omega) htail]

theorem padFrom_block {K : ℕ} (hK : 0 < K) (bits : List Bool)
    (hlen : bits.length = K) :
    padFrom (⟨0, hK⟩ : Fin K) bits = false :: bits := by
  cases bits with
  | nil => simp at hlen; omega
  | cons b bs =>
      by_cases hn : bs = []
      · subst bs
        simp [padFrom]
      · have hlen' : 0 < bs.length := List.length_pos_iff.mpr hn
        have hK' : 1 < K := by simp only [List.length_cons] at hlen; omega
        have hnext : (next (⟨0, hK⟩ : Fin K)).val = 1 :=
          Nat.mod_eq_of_lt hK'
        simp only [padFrom, ↓reduceIte, List.singleton_append]
        rw [padFrom_no_wrap _ bs (by omega) (by
          simp only [hnext, List.length_cons] at *; omega)]

theorem padFrom_blocks {K : ℕ} (hK : 0 < K) (rows : List (List Bool))
    (hlen : ∀ row ∈ rows, row.length = K) :
    padFrom (⟨0, hK⟩ : Fin K) rows.flatten =
      (rows.map (fun row => false :: row)).flatten := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hrow := hlen row (by simp)
      have hreset : (next^[row.length]) (⟨0, hK⟩ : Fin K) = ⟨0, hK⟩ := by
        apply Fin.ext
        rw [next_iterate_val, hrow]
        simp
      simp only [List.flatten_cons, List.map_cons]
      rw [padFrom_append, padFrom_block hK row hrow, hreset]
      rw [ih (by intro r hr; exact hlen r (by simp [hr]))]

def blockBits (B K : ℕ) (f : Fin B → Fin K → Bool) : List Bool :=
  List.ofFn fun z : Fin (B * K) =>
    let ij := finProdFinEquiv.symm z
    f ij.1 ij.2

def paddedBlockBits (B K : ℕ) (f : Fin B → Fin K → Bool) : List Bool :=
  List.ofFn fun z : Fin (B * (K + 1)) =>
    let ij := finProdFinEquiv.symm z
    Fin.cases false (f ij.1) ij.2

theorem blockBits_eq_flatten (B K : ℕ) (f : Fin B → Fin K → Bool) :
    blockBits B K f = (List.ofFn fun i => List.ofFn (f i)).flatten := by
  rw [blockBits, List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have heq : (⟨i.val * K + j.val, by nlinarith [i.isLt, j.isLt]⟩ : Fin (B * K)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  rw [heq, Equiv.symm_apply_apply]

theorem paddedBlockBits_eq_flatten (B K : ℕ) (f : Fin B → Fin K → Bool) :
    paddedBlockBits B K f =
      (List.ofFn fun i => false :: List.ofFn (f i)).flatten := by
  rw [paddedBlockBits, List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  have heq : (fun j : Fin (K + 1) =>
      let ij := finProdFinEquiv.symm
        (⟨i.val * (K + 1) + j.val, by nlinarith [i.isLt, j.isLt]⟩ : Fin (B * (K + 1)))
      Fin.cases false (f ij.1) ij.2) =
      Fin.cases false (f i) := by
    funext j
    have hh : (⟨i.val * (K + 1) + j.val, by nlinarith [i.isLt, j.isLt]⟩ : Fin (B * (K + 1))) =
        finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [hh, Equiv.symm_apply_apply]
  rw [heq, List.ofFn_succ]
  simp

theorem padFrom_blockBits (B K : ℕ) (hK : 0 < K)
    (f : Fin B → Fin K → Bool) :
    padFrom (⟨0, hK⟩ : Fin K) (blockBits B K f) = paddedBlockBits B K f := by
  rw [blockBits_eq_flatten, paddedBlockBits_eq_flatten]
  rw [padFrom_blocks hK]
  · congr 1
    simp only [List.map_ofFn, Function.comp_def]
  · intro row hrow
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hrow
    simp

#print axioms padFrom_blockBits

end CurrentAdditive.V38ZeroPad
