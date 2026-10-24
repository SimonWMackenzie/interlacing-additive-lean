import EthInapproximability.CurrentPaper.SourceClauseGenericCircuitClock
import EthInapproximability.CurrentPaper.SourceClauseCallbackPolynomial

namespace EthInapproximability.CurrentPaper.SourceClauseGenericCallbackPolynomial

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseCallbackPolynomial (blank_words_le work_mass_le)
open SourceClauseGenericCallback (width)
open SourceClauseGenericCircuitClock (unitCost gateCost)

noncomputable def unitPreCost {a q : ℕ}
    (n r : ℕ) (k : Fin (a ^ q)) (ell : ℕ) : ℕ :=
  SourceClauseRowWriterUnitReady.stageCost q n r a k.val (width a q) ell +
  SourceClauseRowUnitMachine.cost n r a q k.val (width a q) ell + 1

noncomputable def gatePreCost {a q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (s t : ℕ) (sign : Bool) : ℕ :=
  SourceClauseRowWriterGateRun.stageCost j row n r a k.val s t (width a q) +
  SourceClauseRowIndexedGate.cost q n r a k.val
    (row (.inl (j, 1))).length s t (width a q) sign + 1

noncomputable def unitPerStep {a q : ℕ} (k : Fin (a ^ q))
    (ell : ℕ) (sign : Bool) : ℕ :=
  @BitMachineStackGrowth.perStep
    (SourceClauseRowWriterOperands.Stack q) _ _ _
    (SourceClauseRowWriterUnitReady.program a k.val (width a q) ell sign)

noncomputable def gatePerStep {a q : ℕ} (j : Fin q)
    (k : Fin (a ^ q)) (s t : ℕ) (sign : Bool) : ℕ :=
  @BitMachineStackGrowth.perStep
    (SourceClauseRowWriterOperands.Stack q) _ _ _
    (SourceClauseRowWriterGateRun.program j a k.val s t (width a q) sign)

noncomputable def workCount (q : ℕ) : ℕ :=
  SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q)

theorem unit_cost_le_growth {a q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (ell : ℕ) (sign : Bool)
    (saved output count : List Bool) (H : ℕ)
    (hinit : ∀ x, (SourceClauseRowWriterBlank.bank row n r
      saved output count x).length ≤ H) :
    unitCost row n r k ell sign saved output count ≤
      unitPreCost n r k ell +
      workCount q * (H + unitPerStep k ell sign *
        unitPreCost n r k ell) + workCount q + 3 := by
  classical
  obtain ⟨t, ht, hr⟩ := SourceClauseRowWriterUnitReady.run
    row n r a k.val (width a q) ell sign saved output count
  obtain ⟨t', ht', hr'⟩ := SourceClauseGenericCircuitClock.bounded_irrel
    (SourceClauseRowWriterUnitReady.program a k.val (width a q) ell sign)
    _ _ _ _ (unitPreCost n r k ell) ⟨t, ht, hr⟩
  have hm := work_mass_le
    (SourceClauseRowWriterUnitReady.program a k.val (width a q) ell sign)
    _ _
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterUnitReady.unitFinalBank row n r a k.val
      (width a q) ell sign saved output count)
    t' (unitPreCost n r k ell) H (workCount q)
    (SourceClauseClearExcept.workBank (SourceClauseRowWriterCleanup.keep q))
    ht' hr' hinit
  let mass := ∑ i : Fin (workCount q),
    (SourceClauseRowWriterUnitReady.unitFinalBank row n r a k.val
      (width a q) ell sign saved output count
      (SourceClauseClearExcept.workBank
        (SourceClauseRowWriterCleanup.keep q) i)).length
  have hmass : mass ≤ workCount q *
      (H + unitPerStep k ell sign * unitPreCost n r k ell) := by
    simpa only [mass, unitPerStep, workCount] using hm
  have hclear : SourceClauseRowWriterUnitClean.clearCost
      (SourceClauseRowWriterUnitReady.unitFinalBank row n r a k.val
        (width a q) ell sign saved output count) =
      mass + workCount q + 2 := by
    rfl
  unfold unitCost
  rw [hclear]
  dsimp only [unitPreCost] at hmass ⊢
  omega

theorem gate_cost_le_growth {a q : ℕ}
    (j : Fin q) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q)) (s t : ℕ) (sign : Bool)
    (saved output count : List Bool) (H : ℕ)
    (hquery : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true)
    (hinit : ∀ x, (SourceClauseRowWriterBlank.bank row n r
      saved output count x).length ≤ H) :
    gateCost j row n r k s t sign saved output count ≤
      gatePreCost j row n r k s t sign +
      workCount q * (H + gatePerStep j k s t sign *
        gatePreCost j row n r k s t sign) + workCount q + 3 := by
  classical
  obtain ⟨u, hu, hr⟩ := SourceClauseRowWriterGateRun.run
    j row n r a k.val s t (width a q) sign
    saved output count hquery
  obtain ⟨u', hu', hr'⟩ := SourceClauseGenericCircuitClock.bounded_irrel
    (SourceClauseRowWriterGateRun.program j a k.val s t (width a q) sign)
    _ _ _ _ (gatePreCost j row n r k s t sign) ⟨u, hu, hr⟩
  have hm := work_mass_le
    (SourceClauseRowWriterGateRun.program j a k.val s t (width a q) sign)
    _ _
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterGateRun.result j row n r a k.val
      s t (width a q) sign saved output count)
    u' (gatePreCost j row n r k s t sign) H (workCount q)
    (SourceClauseClearExcept.workBank (SourceClauseRowWriterCleanup.keep q))
    hu' hr' hinit
  let mass := ∑ i : Fin (workCount q),
    (SourceClauseRowWriterGateRun.result j row n r a k.val
      s t (width a q) sign saved output count
      (SourceClauseClearExcept.workBank
        (SourceClauseRowWriterCleanup.keep q) i)).length
  have hmass : mass ≤ workCount q *
      (H + gatePerStep j k s t sign *
        gatePreCost j row n r k s t sign) := by
    simpa only [mass, gatePerStep, workCount] using hm
  have hclear : SourceClauseRowWriterGateClean.clearCost
      (SourceClauseRowWriterGateRun.result j row n r a k.val
        s t (width a q) sign saved output count) =
      mass + workCount q + 2 := by
    rfl
  unfold gateCost
  rw [hclear]
  dsimp only [gatePreCost] at hmass ⊢
  omega

end EthInapproximability.CurrentPaper.SourceClauseGenericCallbackPolynomial
