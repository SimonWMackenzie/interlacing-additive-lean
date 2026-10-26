import EthInapproximability.CurrentPaper.SourceClauseGenericPrimitivePolynomial

/-!
Uniform fixed-arity quadratic bounds for one physically cleaned source-clause
unit or gate call.  Cleanup is charged through the actual run-growth theorem.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseGenericCallPolynomial

open scoped Classical
open SourceClauseGenericCallback SourceClauseGenericCircuitClock
open SourceClauseGenericCallbackPolynomial SourceClauseGenericPrimitivePolynomial

private theorem finite_image_bound {α : Type} [Fintype α]
    (f : α → ℕ) : ∃ C, ∀ x, f x ≤ C := by
  classical
  exact ⟨Finset.univ.sup f, fun x => Finset.le_sup
    (f := f) (Finset.mem_univ x)⟩

noncomputable def unitStepMax (a q : ℕ) : ℕ :=
  Classical.choose (finite_image_bound
    (fun x : Fin (a ^ q) × Fin (q + 2) × Bool =>
      unitPerStep x.1 x.2.1.val x.2.2))

theorem unit_perStep_le {a q : ℕ} (k : Fin (a ^ q))
    (ell : ℕ) (hell : ell ≤ q + 1) (sign : Bool) :
    unitPerStep k ell sign ≤ unitStepMax a q := by
  classical
  have h : ell < q + 2 := by omega
  exact (Classical.choose_spec (finite_image_bound
    (fun x : Fin (a ^ q) × Fin (q + 2) × Bool =>
      unitPerStep x.1 x.2.1.val x.2.2))) (k, ⟨ell, h⟩, sign)

noncomputable def gateStepMax (a q : ℕ) : ℕ :=
  Classical.choose (finite_image_bound
    (fun x : Fin q × Fin (a ^ q) × Fin a × Fin (q + 2) × Bool =>
      gatePerStep x.1 x.2.1 x.2.2.1.val
        x.2.2.2.1.val x.2.2.2.2))

theorem gate_perStep_le {a q : ℕ} (j : Fin q) (k : Fin (a ^ q))
    (s t : ℕ) (hs : s < a) (ht : t ≤ q + 1) (sign : Bool) :
    gatePerStep j k s t sign ≤ gateStepMax a q := by
  classical
  have hs' : s < a := by omega
  have ht' : t < q + 2 := by omega
  exact (Classical.choose_spec (finite_image_bound
    (fun x : Fin q × Fin (a ^ q) × Fin a × Fin (q + 2) × Bool =>
      gatePerStep x.1 x.2.1 x.2.2.1.val
        x.2.2.2.1.val x.2.2.2.2)))
    (j, k, ⟨s, hs'⟩, ⟨t, ht'⟩, sign)

noncomputable def unitCallCoefficient (a q : ℕ) : ℕ :=
  unitPreCoefficient a q * (1 + workCount q * unitStepMax a q) +
    2 * workCount q + 3

noncomputable def gateCallCoefficient (a q : ℕ) : ℕ :=
  gatePreCoefficient a q * (1 + workCount q * gateStepMax a q) +
    2 * workCount q + 3

theorem unit_call_le_quadratic {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q)) (ell : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hell : ell ≤ q + 1)
    (hinit : ∀ x, (SourceClauseRowWriterBlank.bank row n r
      saved output count x).length ≤ H) :
    unitCost row n r k ell sign saved output count ≤
      unitCallCoefficient a q * (H + 1) ^ 2 := by
  let M := H + 1
  have hM : M ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hpre := unit_pre_cost_le_quadratic k n r H ell hn hr hell
  have hstep := unit_perStep_le k ell hell sign
  have hgrowth := unit_cost_le_growth row n r k ell sign
    saved output count H hinit
  have hmul := Nat.mul_le_mul hstep hpre
  have hH : H ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hsum : H + unitPerStep k ell sign * unitPreCost n r k ell ≤
      (1 + unitStepMax a q * unitPreCoefficient a q) * M ^ 2 := by
    dsimp [M] at *
    nlinarith
  have hmass := Nat.mul_le_mul_left (workCount q) hsum
  have hpre' := Nat.mul_le_mul_left
    (1 + workCount q * unitStepMax a q) hpre
  have hconstant := Nat.mul_le_mul_left (2 * workCount q + 3) hM
  dsimp [unitCallCoefficient, M] at *
  nlinarith

theorem gate_call_le_quadratic {a q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (k : Fin (a ^ q)) (s t : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : (row (.inl (j, 1))).length ≤ H)
    (hs : s < a) (ht : t ≤ q + 1)
    (hquery : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (hinit : ∀ x, (SourceClauseRowWriterBlank.bank row n r
      saved output count x).length ≤ H) :
    gateCost j row n r k s t sign saved output count ≤
      gateCallCoefficient a q * (H + 1) ^ 2 := by
  let M := H + 1
  have hM : M ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hpre := gate_pre_cost_le_quadratic j row n r H k s t sign
    hn hr hrow hs ht
  have hstep := gate_perStep_le j k s t hs ht sign
  have hgrowth := gate_cost_le_growth j row n r k s t sign
    saved output count H hquery hinit
  have hmul := Nat.mul_le_mul hstep hpre
  have hH : H ≤ M ^ 2 := by dsimp [M]; nlinarith
  have hsum : H + gatePerStep j k s t sign *
      gatePreCost j row n r k s t sign ≤
      (1 + gateStepMax a q * gatePreCoefficient a q) * M ^ 2 := by
    dsimp [M] at *
    nlinarith
  have hmass := Nat.mul_le_mul_left (workCount q) hsum
  have hpre' := Nat.mul_le_mul_left
    (1 + workCount q * gateStepMax a q) hpre
  have hconstant := Nat.mul_le_mul_left (2 * workCount q + 3) hM
  dsimp [gateCallCoefficient, M] at *
  nlinarith

end EthInapproximability.CurrentPaper.SourceClauseGenericCallPolynomial
