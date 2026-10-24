import CurrentAdditive.YaoRendererOutput
import CurrentAdditive.GeneralPolynomialClockBound

noncomputable section
namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.YaoLookup Paper2.YaoSourceCodec
open Paper2.YaoClockPoly
open CurrentAdditive.SmallBias

private theorem nat_le_two_pow (c : ℕ) : c ≤ 2^c := by
  induction c with
  | zero => simp
  | succ c ih =>
      have hpos : 1 ≤ 2^c := by
        have hp : 0 < (2:ℕ)^c := pow_pos (by omega) c
        omega
      calc
        c+1 ≤ 2^c+2^c := by omega
        _ = 2^(c+1) := by rw [pow_succ]; omega

private theorem source_budget_le_fuel (c k n : ℕ) :
    c*(n+1)^k ≤ (n+2)^(c+k+1) := by
  have hc : c ≤ (n+2)^c :=
    (nat_le_two_pow c).trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ n+2) c)
  have hq : (n+1)^k ≤ (n+2)^k :=
    Nat.pow_le_pow_left (by omega : n+1 ≤ n+2) k
  have hb : 0 < n+2 := by omega
  calc
    c*(n+1)^k ≤ (n+2)^c*(n+2)^k := Nat.mul_le_mul hc hq
    _ = (n+2)^(c+k) := by rw [pow_add]
    _ ≤ (n+2)^(c+k+1) :=
      Nat.pow_le_pow_right hb (by omega)

theorem renderer_clocked_polytime (t : ℕ) (ht : 4 ≤ t) :
    ∃ f : List Bool → List Bool,
      BitMachine.Polytime f ∧
      ∀ x : YaoSource t, f (encode x) = rendererWord x := by
  obtain ⟨c, k, hbudget⟩ := poly_rendererBudget t ht
  let degree := c+k
  let M := rendererMachine t
  let f := GeneralPolynomialClock.result degree M
  refine ⟨f, GeneralPolynomialClock.polytime degree M, ?_⟩
  intro x
  have hvalid := renderer_outputs_valid t ht x
  have hclock : rendererBudget x ≤
      GeneralPolynomialFuelPrefix.clockLength (degree := degree) (encode x) := by
    calc
      rendererBudget x ≤ c*((encode x).length+1)^k := hbudget x
      _ ≤ ((encode x).length+2)^(c+k+1) :=
        source_budget_le_fuel c k (encode x).length
      _ = GeneralPolynomialFuelPrefix.clockLength (degree := degree) (encode x) := by
        rfl
  have hresult := GeneralPolynomialClock.outputs_valid degree M
    (encode x) (rendererWord x)
    (BitMachine.outputsWithin_mono M hvalid hclock)
  have hall := GeneralPolynomialClock.outputs_all degree M (encode x)
  exact BitMachine.outputsWithin_unique (GeneralPolynomialClock.machine degree M)
    hall hresult

#print axioms renderer_clocked_polytime

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
