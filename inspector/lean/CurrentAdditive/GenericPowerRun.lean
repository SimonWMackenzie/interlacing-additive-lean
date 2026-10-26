import CurrentAdditive.HornerNatBridge
import EthInapproximability.CurrentPaper.SamplerMachinePower
import CurrentAdditive.PowerQuotientSemantics

/-!
The old finite power controller is operationally generic in its stored
modulus, even though its published theorem names the old selected word.
This private theorem instantiates its actual program with any candidate
`2^d+tail` and the new Nat-bit multiplication semantics.
-/

namespace CurrentAdditive.FiniteFieldMachine.GenericPowerRun

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineComposition
open EthInapproximability.CurrentPaper.SamplerMachine
open CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
open CurrentAdditive.FiniteFieldConstructor.BitPrinter
open CurrentAdditive.FiniteFieldMachine.HornerNatBridge

def modulus (d tail : ℕ) : ℕ :=
  CurrentAdditive.FiniteFieldConstructor.TrialSearch.monicBits d tail

def step (d tail : ℕ) (y a : Fin (2 ^ d))
    (htail : tail < 2 ^ d) : Fin (2 ^ d) :=
  ⟨mul d (modulus d tail) y.val a.val,
    mul_lt d (modulus d tail) y.val a.val
      (monicBits_lt d tail htail) (monicBits_topBit d tail htail) a.isLt⟩

private theorem run_succ {c e : SamplerMachinePower.Config}
    (h : TM2.step SamplerMachinePower.program c = some e) (t : ℕ) :
    SamplerMachinePower.run (t + 1) c = SamplerMachinePower.run t e := by
  simp only [SamplerMachinePower.run, Function.iterate_succ_apply,
    advance, h, Option.getD_some]

private theorem step_loop_cons (s : SamplerMachinePower.Control) (b : Bool)
    (a u c fuel : List Bool) :
    TM2.step SamplerMachinePower.program
      (SamplerMachinePower.cfg (some (.inr .loop)) s a u [] [] c [] (b :: fuel)) =
    some (SamplerMachinePower.cfg (some (.inr .move)) SamplerMachinePower.initial
      a u [] [] c [] fuel) := by
  dsimp only [TM2.step, TM2.stepAux, SamplerMachinePower.program,
    SamplerMachinePower.cfg, SamplerMachinePower.initial, Sum.elim_inr]
  simp only [List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

private theorem step_loop_nil (s : SamplerMachinePower.Control)
    (a u c : List Bool) :
    TM2.step SamplerMachinePower.program
      (SamplerMachinePower.cfg (some (.inr .loop)) s a u [] [] c [] []) =
    some (SamplerMachinePower.cfg none SamplerMachinePower.initial
      a u [] [] c [] []) := by
  dsimp only [TM2.step, TM2.stepAux, SamplerMachinePower.program,
    SamplerMachinePower.cfg, SamplerMachinePower.initial, Sum.elim_inr]
  simp only [List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, Option.some.injEq]
  congr 1
  funext k
  rcases k with k | k <;> rfl

theorem product_call (d tail : ℕ) (htail : tail < 2 ^ d) (hd : 0 < d)
    (y a : Fin (2 ^ d)) (fuel : List Bool) :
    ∃ t ≤ d * (4 * d + 5) + 1,
      SamplerMachinePower.run t
        (SamplerMachinePower.cfg (some (.inl (.inr (.inr ()))))
          SamplerMachinePower.initial
          (encodeWord (fun _ : Fin d => (0 : ZMod 2)))
          (encodeWord (xBits d y)) [] []
          (encodeWord (lowerWord d (modulus d tail)))
          (encodeWord (xBits d a)).reverse fuel) =
      SamplerMachinePower.cfg (some (.inr .loop)) SamplerMachinePower.initial
        (encodeWord (xBits d (step d tail y a htail)))
        (encodeWord (xBits d y)) [] []
        (encodeWord (lowerWord d (modulus d tail))) [] fuel := by
  obtain ⟨t, ht, hr⟩ := run_bitPrinter_mul d tail htail hd y a
  have hh : (SamplerMachineProduct.run t
      (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
        (encodeWord (fun _ : Fin d => (0 : ZMod 2)))
        (encodeWord (xBits d y)) [] []
        (encodeWord (lowerWord d (modulus d tail)))
        (encodeWord (xBits d a)).reverse)).l = none := by
    dsimp only [modulus]
    rw [hr]
    rfl
  obtain ⟨t', ht', hrun⟩ := BitMachineSubroutine.lift_outputs
    SamplerMachineProduct.program SamplerMachinePower.program (some .loop)
    (fun _ => rfl) (none : Option Bool) (fun _ : Unit => fuel)
    (SamplerMachineProduct.cfg (some (.inr (.inr ()))) SamplerMachineProduct.initial
      (encodeWord (fun _ : Fin d => (0 : ZMod 2)))
      (encodeWord (xBits d y)) [] []
      (encodeWord (lowerWord d (modulus d tail)))
      (encodeWord (xBits d a)).reverse) t hh
  dsimp only [modulus] at hrun ⊢
  change ∃ t' ≤ _, SamplerMachinePower.run t' _ = _
  refine ⟨t', ht'.trans ht, ?_⟩
  change ((advance SamplerMachinePower.program)^[t']) _ = _
  change ((advance SamplerMachinePower.program)^[t']) _ =
    liftCfg (some .loop) none (fun _ : Unit => fuel)
      (SamplerMachineProduct.run t _) at hrun
  rw [hr] at hrun
  simpa only [step, modulus, xBits, lowerWord] using hrun

theorem round_run (d tail : ℕ) (htail : tail < 2 ^ d) (hd : 0 < d)
    (s : SamplerMachinePower.Control) (y a : Fin (2 ^ d))
    (b : Bool) (fuel : List Bool) :
    ∃ t ≤ d * (4 * d + 5) + 2 * d + 4,
      SamplerMachinePower.run t
        (SamplerMachinePower.cfg (some (.inr .loop)) s
          (encodeWord (xBits d a)) (encodeWord (xBits d y)) [] []
          (encodeWord (lowerWord d (modulus d tail))) [] (b :: fuel)) =
      SamplerMachinePower.cfg (some (.inr .loop)) SamplerMachinePower.initial
        (encodeWord (xBits d (step d tail y a htail)))
        (encodeWord (xBits d y)) [] []
        (encodeWord (lowerWord d (modulus d tail))) [] fuel := by
  obtain ⟨t, ht, hr⟩ := product_call d tail htail hd y a fuel
  refine ⟨t + (2 * d + 2) + 1, by omega, ?_⟩
  rw [run_succ
    (step_loop_cons s b (encodeWord (xBits d a))
      (encodeWord (xBits d y))
      (encodeWord (lowerWord d (modulus d tail))) fuel)]
  simp only [SamplerMachinePower.run, Function.iterate_add_apply]
  have hp := SamplerMachinePower.prepare_run SamplerMachinePower.initial
    (encodeWord (xBits d a)) (encodeWord (xBits d y))
    (encodeWord (lowerWord d (modulus d tail))) fuel
  simp only [encodeWord_length, ← SamplerMachinePower.encodeWord_zero] at hp
  change SamplerMachinePower.run t (SamplerMachinePower.run (2 * d + 2) _) = _
  rw [hp, hr]

theorem run_iterated_mul (d tail : ℕ) (htail : tail < 2 ^ d) (hd : 0 < d)
    (s : SamplerMachinePower.Control) (y a : Fin (2 ^ d))
    (fuel : List Bool) :
    ∃ t ≤ fuel.length * (d * (4 * d + 5) + 2 * d + 4) + 1,
      SamplerMachinePower.run t
        (SamplerMachinePower.cfg (some (.inr .loop)) s
          (encodeWord (xBits d a)) (encodeWord (xBits d y)) [] []
          (encodeWord (lowerWord d (modulus d tail))) [] fuel) =
      SamplerMachinePower.cfg none SamplerMachinePower.initial
        (encodeWord (xBits d (((step d tail y · htail)^[fuel.length]) a)))
        (encodeWord (xBits d y)) [] []
        (encodeWord (lowerWord d (modulus d tail))) [] [] := by
  induction fuel generalizing s a with
  | nil =>
      refine ⟨1, by simp, ?_⟩
      exact run_succ (step_loop_nil s (encodeWord (xBits d a))
        (encodeWord (xBits d y))
        (encodeWord (lowerWord d (modulus d tail)))) 0
  | cons b fuel ih =>
      obtain ⟨ts, hts, hs⟩ := round_run d tail htail hd s y a b fuel
      obtain ⟨tr, htr, hr⟩ := ih SamplerMachinePower.initial (step d tail y a htail)
      refine ⟨tr + ts, ?_, ?_⟩
      · simp only [List.length_cons]
        nlinarith
      · simp only [SamplerMachinePower.run, Function.iterate_add_apply]
        change SamplerMachinePower.run tr (SamplerMachinePower.run ts _) = _
        rw [hs, hr]
        simp only [List.length_cons, Function.iterate_succ_apply]

theorem bitMul_comm (d tail : ℕ) (htail : tail < 2 ^ d) (hd : 0 < d)
    (a b : Fin (2 ^ d)) :
    mul d (modulus d tail) a.val b.val =
      mul d (modulus d tail) b.val a.val := by
  have hmod := monicBits_lt d tail htail
  have htop := monicBits_topBit d tail htail
  have hmonic := monicBits_monic d tail htail
  have hdegree := monicBits_degree d tail htail
  have hab := mul_lt d (modulus d tail) a.val b.val hmod htop b.isLt
  have hba := mul_lt d (modulus d tail) b.val a.val hmod htop a.isLt
  have hqab := mul_quotient d (modulus d tail) a.val b.val hd hmod htop b.isLt
  have hqba := mul_quotient d (modulus d tail) b.val a.val hd hmod htop a.isLt
  have heq : (⟨mul d (modulus d tail) a.val b.val, hab⟩ : Fin (2 ^ d)) =
      ⟨mul d (modulus d tail) b.val a.val, hba⟩ :=
    (quotientCode_injective d (modulus d tail) hmonic hdegree)
      (hqab.trans ((mul_comm _ _).trans hqba.symm))
  exact congrArg Fin.val heq

def oneLabel (d : ℕ) (hd : 0 < d) : Fin (2 ^ d) :=
  ⟨1, Nat.one_lt_two_pow (by omega : d ≠ 0)⟩

theorem iterated_step_eq_power (d tail : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (y : Fin (2 ^ d)) (j : ℕ) :
    ((step d tail y · htail)^[j]) (oneLabel d hd) =
      ⟨power d (modulus d tail) y.val j,
        power_lt d (modulus d tail) y.val j hd
          (monicBits_lt d tail htail) (monicBits_topBit d tail htail) y.isLt⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Fin.ext
      simp only [step, power]
      exact bitMul_comm d tail htail hd y
        ⟨power d (modulus d tail) y.val j,
          power_lt d (modulus d tail) y.val j hd
            (monicBits_lt d tail htail) (monicBits_topBit d tail htail) y.isLt⟩

/-- Exact physical repeated multiplication with the constructor's actual
Nat-bit power, charged once per exponent increment rather than recomputed
from scratch. The current result only exposes the final power. -/
theorem run_bitPrinter_power (d tail : ℕ) (htail : tail < 2 ^ d)
    (hd : 0 < d) (y : Fin (2 ^ d)) (fuel : List Bool) :
    ∃ t ≤ fuel.length * (d * (4 * d + 5) + 2 * d + 4) + 1,
      SamplerMachinePower.run t
        (SamplerMachinePower.cfg (some (.inr .loop)) SamplerMachinePower.initial
          (encodeWord (xBits d (oneLabel d hd))) (encodeWord (xBits d y)) [] []
          (encodeWord (lowerWord d (modulus d tail))) [] fuel) =
      SamplerMachinePower.cfg none SamplerMachinePower.initial
        (encodeWord (lowerWord d (power d (modulus d tail) y.val fuel.length)))
        (encodeWord (xBits d y)) [] []
        (encodeWord (lowerWord d (modulus d tail))) [] [] := by
  obtain ⟨t, ht, hr⟩ := run_iterated_mul d tail htail hd
    SamplerMachinePower.initial y (oneLabel d hd) fuel
  refine ⟨t, ht, ?_⟩
  rw [iterated_step_eq_power d tail htail hd y fuel.length] at hr
  simpa only [xBits, lowerWord] using hr

#print axioms run_iterated_mul
#print axioms iterated_step_eq_power
#print axioms run_bitPrinter_power

end CurrentAdditive.FiniteFieldMachine.GenericPowerRun
