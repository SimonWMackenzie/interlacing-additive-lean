import CurrentAdditive.V40RandomizedETHArithmetic
import CurrentAdditive.V40RandomPermittedFamily
import Paper2.SubexpBudget

/-! Exact current-table request lengths and effective-tape fit. These bounds
use the literal requested midpoint and the same sampled row-major payload. -/
namespace CurrentAdditive.V40RandomizedETHEndpoint
noncomputable section
open Paper2
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open V39PublicSchedule
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def requestedWord (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) : List Bool :=
  natField (V40RandomPermittedFamily.numerator L k) ++
    V40RandomPermittedFamily.matrixWord L k f

theorem requestedWord_length (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    (requestedWord L k f).length + 1 ≤ 9*sampleEntries L k+4 := by
  have hm := V40RandomPermittedFamily.side_pos L k
  have hn := V40RandomPermittedFamily.numerator_le_entries L k
  have hf := Paper2.YaoClockPoly.natField_length_le
    (V40RandomPermittedFamily.numerator L k)
  have hs := Paper2.YaoClockPoly.natField_length_le (sampleSide L k)
  have hmT : sampleSide L k ≤ sampleSide L k^2 := by nlinarith
  simp only [requestedWord,V40RandomPermittedFamily.matrixWord,AModel.matrixWord,
    List.length_append,MatrixMaterialization.rowMajor_length]
  unfold sampleEntries
  nlinarith

theorem requestedWord_source_power (n k : ℕ) (hn : 1 ≤ n)
    (f : Fin (sampleSide (Nat.clog 2 n) k) →
      Fin (sampleSide (Nat.clog 2 n) k) → Bool) :
    (requestedWord (Nat.clog 2 n) k f).length+1 ≤
      (n+2)^(1004*(k+1)) := by
  have hw := requestedWord_length (Nat.clog 2 n) k f
  have ht := V39ETHArithmetic.sample_entries_polynomial n k hn
  have hx : 1 ≤ (n+2)^(1000*(k+1)) := Nat.one_le_pow _ _ (by omega)
  have h13 : 13 ≤ (n+2)^(4*(k+1)) := by
    have hbase : 3^4 ≤ (n+2)^4 := Nat.pow_le_pow_left (by omega) 4
    have hexp : (n+2)^4 ≤ (n+2)^(4*(k+1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hbase
    omega
  calc
    _ ≤ 13*(n+2)^(1000*(k+1)) := by omega
    _ ≤ (n+2)^(4*(k+1))*(n+2)^(1000*(k+1)) :=
      Nat.mul_le_mul_right _ h13
    _ = _ := by rw [←pow_add]; congr 1; ring

theorem requestedWord_power_fits (p d : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      ∀ f : Fin (sampleSide (Nat.clog 2 n) (kOf N)) →
        Fin (sampleSide (Nat.clog 2 n) (kOf N)) → Bool,
      ((requestedWord (Nat.clog 2 n) (kOf N) f).length+1)^d ≤
        Paper2.AEth.expLen N := by
  obtain ⟨N₀,h⟩ := Paper2.AEth.budget_numeric (1004*d) p
  refine ⟨N₀,?_⟩
  intro N hN n hn hs f
  have hw := requestedWord_source_power n (kOf N) hn f
  calc
    _ ≤ ((n+2)^(1004*(kOf N+1)))^d := Nat.pow_le_pow_left hw _
    _ = (n+2)^((1004*d)*(kOf N+1)) := by
      rw [←pow_mul]; congr 1; ring
    _ ≤ _ := h N hN n N hs le_rfl
      ((show N ≤ N+2 by omega).trans (Nat.le_self_pow (by decide) (N+2)))

/-- The actual amplified classifier's tape and run fit the twoCut block
budget on every sampled current table, uniformly over every payload. -/
theorem classifier_fits (C : SelectedTape.Algorithm) (p : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      ∀ f : Fin (sampleSide (Nat.clog 2 n) (kOf N)) →
        Fin (sampleSide (Nat.clog 2 n) (kOf N)) → Bool,
      C.tapeLength (requestedWord (Nat.clog 2 n) (kOf N) f) ≤
          C.cR*Paper2.AEth.expLen N ∧
      C.cT*((requestedWord (Nat.clog 2 n) (kOf N) f).length+1)^C.dT ≤
          C.cT*Paper2.AEth.expLen N := by
  obtain ⟨NR,hR⟩ := requestedWord_power_fits p C.dR
  obtain ⟨NT,hT⟩ := requestedWord_power_fits p C.dT
  refine ⟨max NR NT,?_⟩
  intro N hN n hn hs f
  constructor
  · exact Nat.mul_le_mul_left _ (hR N ((le_max_left _ _).trans hN) n hn hs f)
  · exact Nat.mul_le_mul_left _ (hT N ((le_max_right _ _).trans hN) n hn hs f)

#print axioms requestedWord_length
#print axioms requestedWord_source_power
#print axioms requestedWord_power_fits
#print axioms classifier_fits
end
end CurrentAdditive.V40RandomizedETHEndpoint
