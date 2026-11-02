import CurrentAdditive.V42ETHAsymptotics
import CurrentAdditive.V42RandomPermittedFamily
import Paper2.SubexpBudget

namespace CurrentAdditive.V42RandomizedETHEndpoint
noncomputable section
open Paper2 V42PublicSchedule
open Paper2.Unit4Shell.Asymptotics
open EthInapproximability.CurrentPaper EncodedCommunication
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536

/-- A deliberately coarse bound valid even below the public source cutoff.
It is used only for machine resources; sharp error separation uses coefficient
four from the exact public-size theorem. -/
theorem sample_entries_polynomial (n k : ℕ) (hn : 1 ≤ n) :
    sampleEntries (Nat.clog 2 n) k ≤ (n+2)^(10000*(k+1)) := by
  let L := Nat.clog 2 n
  have he : ell L ≤ L+1 := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have hB : B L k ≤ (37*L+620)*(k+1) := by
    have hm := Nat.mul_le_mul_left k he
    unfold B seedCost fullOverhead fullExponent
    nlinarith
  have hc : Nat.clog 2 (B L k+2) ≤ B L k+2 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  have ht := sampleEntries_clog_upper L k
  have hclog : Nat.clog 2 (sampleEntries L k) ≤ 5000*(k+1)*(L+1) := by
    nlinarith
  have hround := V39PublicSchedule.pow2Ceil_lt_twice n (by omega)
  change 2^L < 2*n at hround
  have hpow : 2^(L+1) ≤ (n+2)^2 := by rw [pow_succ]; nlinarith
  calc
    _ ≤ 2^(5000*(k+1)*(L+1)) := (Nat.le_pow_clog (by decide) _).trans
      (Nat.pow_le_pow_right (by decide) hclog)
    _ = (2^(L+1))^(5000*(k+1)) := by rw [←pow_mul]; congr 1; ring
    _ ≤ ((n+2)^2)^(5000*(k+1)) := Nat.pow_le_pow_left hpow _
    _ = _ := by rw [←pow_mul]; congr 1; ring

def requestedWord (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) : List Bool :=
  natField (V42RandomPermittedFamily.numerator L k) ++
    V42RandomPermittedFamily.matrixWord L k f

theorem requestedWord_length (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    (requestedWord L k f).length + 1 ≤ 9*sampleEntries L k+4 := by
  have hm := V42RandomPermittedFamily.side_pos L k
  have hn := V42RandomPermittedFamily.numerator_le_entries L k
  have hf := Paper2.YaoClockPoly.natField_length_le
    (V42RandomPermittedFamily.numerator L k)
  have hs := Paper2.YaoClockPoly.natField_length_le (sampleSide L k)
  have hmT : sampleSide L k ≤ sampleSide L k^2 := by nlinarith
  simp only [requestedWord,V42RandomPermittedFamily.matrixWord,AModel.matrixWord,
    List.length_append,MatrixMaterialization.rowMajor_length]
  unfold sampleEntries
  nlinarith

theorem requestedWord_source_power (n k : ℕ) (hn : 1 ≤ n)
    (f : Fin (sampleSide (Nat.clog 2 n) k) →
      Fin (sampleSide (Nat.clog 2 n) k) → Bool) :
    (requestedWord (Nat.clog 2 n) k f).length+1 ≤
      (n+2)^(10004*(k+1)) := by
  have hw := requestedWord_length (Nat.clog 2 n) k f
  have ht := sample_entries_polynomial n k hn
  have hx : 1 ≤ (n+2)^(10000*(k+1)) := Nat.one_le_pow _ _ (by omega)
  have h13 : 13 ≤ (n+2)^(4*(k+1)) := by
    have hbase : 3^4 ≤ (n+2)^4 := Nat.pow_le_pow_left (by omega) 4
    have hexp : (n+2)^4 ≤ (n+2)^(4*(k+1)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    norm_num at hbase
    omega
  calc
    _ ≤ 13*(n+2)^(10000*(k+1)) := by omega
    _ ≤ (n+2)^(4*(k+1))*(n+2)^(10000*(k+1)) :=
      Nat.mul_le_mul_right _ h13
    _ = _ := by rw [←pow_add]; congr 1; ring

theorem requestedWord_power_fits (p d : ℕ) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ n,
      1 ≤ n → n ≤ N*(Nat.clog 2 (N+2))^p →
      ∀ f : Fin (sampleSide (Nat.clog 2 n) (kOf N)) →
        Fin (sampleSide (Nat.clog 2 n) (kOf N)) → Bool,
      ((requestedWord (Nat.clog 2 n) (kOf N) f).length+1)^d ≤
        Paper2.AEth.expLen N := by
  obtain ⟨N₀,h⟩ := Paper2.AEth.budget_numeric (10004*d) p
  refine ⟨N₀,?_⟩
  intro N hN n hn hs f
  have hw := requestedWord_source_power n (kOf N) hn f
  calc
    _ ≤ ((n+2)^(10004*(kOf N+1)))^d := Nat.pow_le_pow_left hw _
    _ = (n+2)^((10004*d)*(kOf N+1)) := by
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
end CurrentAdditive.V42RandomizedETHEndpoint


