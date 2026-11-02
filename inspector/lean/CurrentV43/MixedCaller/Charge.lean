import CurrentV43.MixedCaller.Caller

namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
set_option maxHeartbeats 1500000

/-- A pointwise form suitable for promises such as sufficiently large sparse
formulas. No global polynomial bound on the gap schedule is required. -/
theorem full_cost_charge (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (ci di ct dt : ℕ) :
    ∃ c d : ℕ, ∀ (w : List Bool) (S : ℕ), 1≤S →
      w.length≤ci*S^di → P.clock w≤ct*S^dt →
      (tapeProducer P C).clock w+finiteTime P C w≤c*S^d := by
  let sz:=fun w : List Bool=>w.length+P.clock w
  have hi:Unit4Shell.Poly.PolyIn sz List.length:=
    Unit4Shell.Poly.mono (by intro w; dsimp [sz]; omega) Unit4Shell.Poly.self
  have ht:Unit4Shell.Poly.PolyIn sz P.clock:=
    Unit4Shell.Poly.mono (by intro w; dsimp [sz]; omega) Unit4Shell.Poly.self
  obtain ⟨c,d,h⟩:=full_cost_poly sz P C hi ht
  refine ⟨c*(ci+ct+1)^d,(di+dt+1)*d,?_⟩
  intro w S hS hlen hclock
  have hpow (i:ℕ) (hi:i≤di+dt+1): S^i≤S^(di+dt+1):=
    Nat.pow_le_pow_right hS hi
  have hlen':w.length≤ci*S^(di+dt+1):=
    hlen.trans (Nat.mul_le_mul_left _ (hpow di (by omega)))
  have hclock':P.clock w≤ct*S^(di+dt+1):=
    hclock.trans (Nat.mul_le_mul_left _ (hpow dt (by omega)))
  have hp:1≤S^(di+dt+1):=Nat.one_le_pow _ _ hS
  have hs:sz w+1≤(ci+ct+1)*S^(di+dt+1):=by dsimp [sz];nlinarith
  calc
    _≤c*(sz w+1)^d:=h w
    _≤c*((ci+ct+1)*S^(di+dt+1))^d:=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs d)
    _=c*(ci+ct+1)^d*S^((di+dt+1)*d):=by rw [mul_pow,←pow_mul];ring

/-- The fixed machine and actual carrier printer are bounded by S^O(1)
whenever the concrete deterministic requester has its proved S^O(1) bound.
The constructor, estimator and arbitrary schedule precede this bound. -/
theorem actual_cost_charge
    (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (G : ParametricSource.Schedule) (A : V39PermittedNumericalExtraction.PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) (ci di ct dt : ℕ) :
    ∃ c d : ℕ, ∀ (w : List Bool) (S : ℕ), 1≤S →
      w.length≤ci*S^di → (sourceRequest D B G cs cutoff hcut).clock w≤ct*S^dt →
      (actualTapeProducer D B G A cs cutoff hcut).clock w+
        actualTime D B G A cs cutoff hcut w≤c*S^d :=
  full_cost_charge _ _ ci di ct dt

#print axioms full_cost_charge
#print axioms actual_cost_charge
end
end CurrentV43.MixedCaller
