import EthInapproximability.CurrentPaper.SourceClauseCircuitClock
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-!
Input-size majorants for the exact clause callback clocks.  The first stage
controls cleanup from actual preceding runs, not from assumed final-bank sizes.
-/

namespace EthInapproximability.CurrentPaper.SourceClauseCallbackPolynomial

open Turing BitMachineEncoding
open scoped Classical
open SourceClauseCallback SourceClauseCircuitClock

theorem blank_words_le {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r H : ℕ) (saved output count : List Bool)
    (hn : n ≤ H) (hr : r ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H)
    (houtput : output.length ≤ H)
    (hcount : count.length ≤ H) :
    ∀ x, (SourceClauseRowWriterBlank.bank row n r
      saved output count x).length ≤ H := by
  intro x
  cases x with
  | inl x =>
      cases x with
      | inl c =>
          cases c with
          | inl y => simpa [SourceClauseRowWriterBlank.bank,
              SourceClauseRowWriterBlank.master,
              SourceClauseRowWriterBlank.core] using hrow y
          | inr i =>
              fin_cases i <;>
                simp [SourceClauseRowWriterBlank.bank,
                  SourceClauseRowWriterBlank.master,
                  SourceClauseRowWriterBlank.core,
                  hsaved, houtput, hcount]
      | inr z =>
          simp [SourceClauseRowWriterBlank.bank,
            SourceClauseRowWriterBlank.master]
  | inr i =>
      fin_cases i <;>
        simp [SourceClauseRowWriterBlank.bank, hn, hr]

theorem work_mass_le {K L V : Type} [Fintype L]
    (P : L → Turing.TM2.Stmt (fun _ : K => Bool) L V)
    (l : L) (v : V) (S U : K → List Bool)
    (t B H m : ℕ) (work : Fin m → K)
    (ht : t ≤ B)
    (hr : ((advance P)^[t])
      (⟨some l, v, S⟩ : Turing.TM2.Cfg (fun _ : K => Bool) L V) =
      ⟨none, v, U⟩)
    (hinit : ∀ x, (S x).length ≤ H) :
    (∑ i : Fin m, (U (work i)).length) ≤
      m * (H + BitMachineStackGrowth.perStep P * B) := by
  have hi (i : Fin m) :
      (U (work i)).length ≤
        H + BitMachineStackGrowth.perStep P * B := by
    have hg := BitMachineStackGrowth.run_growth P
      (⟨some l, v, S⟩ : Turing.TM2.Cfg (fun _ : K => Bool) L V)
      t (work i)
    have hg' : (U (work i)).length ≤
        (S (work i)).length + BitMachineStackGrowth.perStep P * t := by
      simpa only [hr] using hg
    have hs := hinit (work i)
    have hmul := Nat.mul_le_mul_left
      (BitMachineStackGrowth.perStep P) ht
    omega
  calc
    (∑ i : Fin m, (U (work i)).length) ≤
        ∑ _i : Fin m, (H + BitMachineStackGrowth.perStep P * B) := by
          apply Finset.sum_le_sum
          intro i _
          exact hi i
    _ = m * (H + BitMachineStackGrowth.perStep P * B) := by simp

noncomputable def unitPreCost {q : ℕ}
    (n r : ℕ) (k : Fin (2 ^ q)) (ell : ℕ) : ℕ :=
  SourceClauseRowWriterUnitReady.stageCost q n r 2 k.val (width q) ell +
  SourceClauseRowUnitMachine.cost n r 2 q k.val (width q) ell + 1

noncomputable def gatePreCost {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (s t : ℕ) (sign : Bool) : ℕ :=
  SourceClauseRowWriterGateRun.stageCost j row n r 2 k.val s t (width q) +
  SourceClauseRowIndexedGate.cost q n r 2 k.val
    (row (.inl (j, 1))).length s t (width q) sign + 1

noncomputable def unitPerStep {q : ℕ} (k : Fin (2 ^ q))
    (ell : ℕ) (sign : Bool) : ℕ :=
  @BitMachineStackGrowth.perStep
    (SourceClauseRowWriterOperands.Stack q) _ _ _
    (SourceClauseRowWriterUnitReady.program 2 k.val (width q) ell sign)

noncomputable def gatePerStep {q : ℕ} (j : Fin q)
    (k : Fin (2 ^ q)) (s t : ℕ) (sign : Bool) : ℕ :=
  @BitMachineStackGrowth.perStep
    (SourceClauseRowWriterOperands.Stack q) _ _ _
    (SourceClauseRowWriterGateRun.program j 2 k.val s t (width q) sign)

noncomputable def workCount (q : ℕ) : ℕ :=
  SourceClauseClearExcept.workCount (SourceClauseRowWriterCleanup.keep q)

theorem unit_cost_le_growth {q : ℕ}
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (ell : ℕ) (sign : Bool)
    (saved output count : List Bool) (H : ℕ)
    (hinit : ∀ x, (SourceClauseRowWriterBlank.bank row n r
      saved output count x).length ≤ H) :
    unitCost row n r k ell sign saved output count ≤
      unitPreCost n r k ell +
      workCount q * (H + unitPerStep k ell sign *
        unitPreCost n r k ell) + workCount q + 3 := by
  classical
  obtain ⟨t, ht, hr⟩ := SourceClauseRowWriterUnitReady.run
    row n r 2 k.val (width q) ell sign saved output count
  obtain ⟨t', ht', hr'⟩ := SourceClauseCircuitClock.bounded_irrel
    (SourceClauseRowWriterUnitReady.program 2 k.val (width q) ell sign)
    _ _ _ _ (unitPreCost n r k ell) ⟨t, ht, hr⟩
  have hm := work_mass_le
    (SourceClauseRowWriterUnitReady.program 2 k.val (width q) ell sign)
    _ _
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterUnitReady.unitFinalBank row n r 2 k.val
      (width q) ell sign saved output count)
    t' (unitPreCost n r k ell) H (workCount q)
    (SourceClauseClearExcept.workBank (SourceClauseRowWriterCleanup.keep q))
    ht' hr' hinit
  let mass := ∑ i : Fin (workCount q),
    (SourceClauseRowWriterUnitReady.unitFinalBank row n r 2 k.val
      (width q) ell sign saved output count
      (SourceClauseClearExcept.workBank
        (SourceClauseRowWriterCleanup.keep q) i)).length
  have hmass : mass ≤ workCount q *
      (H + unitPerStep k ell sign * unitPreCost n r k ell) := by
    simpa only [mass, unitPerStep, workCount] using hm
  have hclear : SourceClauseRowWriterUnitClean.clearCost
      (SourceClauseRowWriterUnitReady.unitFinalBank row n r 2 k.val
        (width q) ell sign saved output count) =
      mass + workCount q + 2 := by
    rfl
  unfold unitCost
  rw [hclear]
  dsimp only [unitPreCost] at hmass ⊢
  omega

theorem gate_cost_le_growth {q : ℕ}
    (j : Fin q) (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q)) (s t : ℕ) (sign : Bool)
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
    j row n r 2 k.val s t (width q) sign
    saved output count hquery
  obtain ⟨u', hu', hr'⟩ := SourceClauseCircuitClock.bounded_irrel
    (SourceClauseRowWriterGateRun.program j 2 k.val s t (width q) sign)
    _ _ _ _ (gatePreCost j row n r k s t sign) ⟨u, hu, hr⟩
  have hm := work_mass_le
    (SourceClauseRowWriterGateRun.program j 2 k.val s t (width q) sign)
    _ _
    (SourceClauseRowWriterBlank.bank row n r saved output count)
    (SourceClauseRowWriterGateRun.result j row n r 2 k.val
      s t (width q) sign saved output count)
    u' (gatePreCost j row n r k s t sign) H (workCount q)
    (SourceClauseClearExcept.workBank (SourceClauseRowWriterCleanup.keep q))
    hu' hr' hinit
  let mass := ∑ i : Fin (workCount q),
    (SourceClauseRowWriterGateRun.result j row n r 2 k.val
      s t (width q) sign saved output count
      (SourceClauseClearExcept.workBank
        (SourceClauseRowWriterCleanup.keep q) i)).length
  have hmass : mass ≤ workCount q *
      (H + gatePerStep j k s t sign *
        gatePreCost j row n r k s t sign) := by
    simpa only [mass, gatePerStep, workCount] using hm
  have hclear : SourceClauseRowWriterGateClean.clearCost
      (SourceClauseRowWriterGateRun.result j row n r 2 k.val
        s t (width q) sign saved output count) =
      mass + workCount q + 2 := by
    rfl
  unfold gateCost
  rw [hclear]
  dsimp only [gatePreCost] at hmass ⊢
  omega

end EthInapproximability.CurrentPaper.SourceClauseCallbackPolynomial
