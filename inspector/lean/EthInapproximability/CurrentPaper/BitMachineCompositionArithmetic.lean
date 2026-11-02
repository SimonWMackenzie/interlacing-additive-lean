import EthInapproximability.CurrentPaper.BitMachine

/-!
# First halting times and polynomial composition budgets

Source: v8 `06-eth.tex` and `B-effectivity-details.tex`, the fixed bit-machine
convention and encoded runtime composition. These lemmas use actual runs and
the proved stack-length bound. They do not assert that a composite machine
exists; its concrete transition program and simulation are separate.
-/

namespace EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic

open BitMachine

/-- An actual bounded output has a first halting transition, with the same
output. Before that transition, its control label is present. -/
theorem first_halt (M : Machine) {input output : List Bool} {time : ℕ}
    (h : M.OutputsWithin input output time) :
    ∃ t ≤ time, (M.run t (M.init input)).l = none ∧
      (M.run t (M.init input)).stk M.output = output ∧
      ∀ k < t, (M.run k (M.init input)).l ≠ none := by
  classical
  obtain ⟨u, hu, hhalt, hout⟩ := h
  have hex : ∃ n, (M.run n (M.init input)).l = none := ⟨u, hhalt⟩
  let t := Nat.find hex
  have ht : t ≤ u := Nat.find_min' hex hhalt
  have hfirst : (M.run t (M.init input)).l = none := Nat.find_spec hex
  have hout' : (M.run t (M.init input)).stk M.output = output := by
    apply outputsWithin_unique M
      (show M.OutputsWithin input ((M.run t (M.init input)).stk M.output) t from
        ⟨t, le_rfl, hfirst, rfl⟩)
    exact ⟨u, hu, hhalt, hout⟩
  refine ⟨t, ht.trans hu, hfirst, hout', ?_⟩
  intro k hk
  exact Nat.find_min hex hk

/-- A concrete polynomial bound for sequential execution with a two-pass
stack transfer. `p` is the first machine's fixed push bound, and `L` is the
actual intermediate output length. -/
theorem composition_time_bound (n cf df cg dg p L : ℕ)
    (hL : L ≤ n + cf * (n + 1) ^ df * p) :
    cf * (n + 1) ^ df + 2 * L + 2 + cg * (L + 1) ^ dg ≤
      (cf + 2 * (cf * p + 1) + cg * (cf * p + 1) ^ dg) *
        (n + 1) ^ ((df + 1) * (dg + 1)) := by
  have hbase : 1 ≤ n + 1 := by omega
  have hpow : (n + 1) ^ df ≤ (n + 1) ^ (df + 1) :=
    Nat.pow_le_pow_right hbase (by omega)
  have hn : n + 1 ≤ (n + 1) ^ (df + 1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1 ≤ df + 1 by omega)
  have hL' : L + 1 ≤ (cf * p + 1) * (n + 1) ^ (df + 1) := by
    have hh := Nat.mul_le_mul_left (cf * p) hpow
    nlinarith
  have htransfer : 2 * L + 2 ≤ 2 * (cf * p + 1) * (n + 1) ^ (df + 1) := by
    nlinarith
  have hsecond : cg * (L + 1) ^ dg ≤
      cg * (cf * p + 1) ^ dg * (n + 1) ^ ((df + 1) * dg) := by
    calc
      _ ≤ cg * ((cf * p + 1) * (n + 1) ^ (df + 1)) ^ dg := by gcongr
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hfirstPower : (n + 1) ^ df ≤ (n + 1) ^ ((df + 1) * (dg + 1)) :=
    Nat.pow_le_pow_right hbase (by nlinarith)
  have htransferPower : (n + 1) ^ (df + 1) ≤ (n + 1) ^ ((df + 1) * (dg + 1)) :=
    Nat.pow_le_pow_right hbase (by nlinarith)
  have hsecondPower : (n + 1) ^ ((df + 1) * dg) ≤
      (n + 1) ^ ((df + 1) * (dg + 1)) :=
    Nat.pow_le_pow_right hbase (by nlinarith)
  have h1 := Nat.mul_le_mul_left cf hfirstPower
  have h2 := htransfer.trans (Nat.mul_le_mul_left (2 * (cf * p + 1)) htransferPower)
  have h3 := hsecond.trans (Nat.mul_le_mul_left (cg * (cf * p + 1) ^ dg) hsecondPower)
  nlinarith

/-- Once a separately proved concrete machine has the sequential execution
bound, the actual output-length theorem supplies a polynomial in the
original input length. This is only arithmetic transport, not a compiler. -/
theorem polytime_of_composition_bound (Mf Mc : Machine)
    (f g : List Bool → List Bool) (cf df cg dg : ℕ)
    (hf : Mf.ComputesWithin f (fun n => cf * (n + 1) ^ df))
    (hcomp : ∀ input, Mc.OutputsWithin input (g (f input))
      (cf * (input.length + 1) ^ df + 2 * (f input).length + 2 +
        cg * ((f input).length + 1) ^ dg)) :
    Polytime (g ∘ f) := by
  refine ⟨Mc, cf + 2 * (cf * Mf.pushBound + 1) +
      cg * (cf * Mf.pushBound + 1) ^ dg, (df + 1) * (dg + 1), ?_⟩
  intro input
  apply outputsWithin_mono Mc (hcomp input)
  exact composition_time_bound input.length cf df cg dg Mf.pushBound (f input).length
    (output_length_bound Mf (hf input))

end EthInapproximability.CurrentPaper.BitMachineCompositionArithmetic
