import EthInapproximability.CurrentPaper.SamplerMachineSearch

/-!
# Exhaustive counter mapping with actual finite callbacks

Source: locked v8 Appendix E, `lem:exact-families`, ordered sampler-table
enumeration. The literal search controller is reused with acceptance
constantly false. Its callback is allowed to prepend a payload to one output
stack while restoring every other bank. The counter scan, overflow test,
and increment are the already implemented operations, not list oracles.

This generic composition theorem keeps its concrete callback correctness
and runtime contract explicit. Installing an implemented row callback is
a separate obligation; this module alone does not assert sampler runtime.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineCounterMap

open Turing BitMachineEncoding BitMachineComposition
open SamplerMachineIncrement SamplerEnumeration

variable {K L V : Type*} [DecidableEq K]

abbrev Stack (K : Type*) := SamplerMachineSearch.Stack K
abbrev Label (L : Type*) := SamplerMachineSearch.Label L
abbrev Control (V : Type*) := SamplerMachineSearch.Control V
abbrev Config (K L V : Type*) := SamplerMachineSearch.Config K L V

def program (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (source : K) (start : L) (v0 : V) :=
  SamplerMachineSearch.program P source start v0 (fun _ => false)

def bank (source output : K) (S : K → List Bool) (q out : List Bool) : K → List Bool :=
  Function.update (Function.update S output out) source q

def cfg (source output : K) (S : K → List Bool) (l : Option (Label L))
    (s : Control V) (q out work : List Bool) : Config K L V :=
  SamplerMachineSearch.cfg source (Function.update S output out) l s q work

def run (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (source : K) (start : L) (v0 : V) (t : ℕ) (q : Config K L V) :=
  ((advance (program P source start v0))^[t]) q

/-- Payloads are physically prepended to the output stack at each call. -/
def collected (payload : List Bool → List Bool) : List (List Bool) → List Bool → List Bool
  | [], out => out
  | q :: qs, out => collected payload qs (payload q ++ out)

theorem collected_reverse (row : List Bool → List Bool) (qs : List (List Bool)) (out : List Bool) :
    collected (fun q => (row q).reverse) qs out = (qs.flatMap row).reverse ++ out := by
  induction qs generalizing out with
  | nil => rfl
  | cons q qs ih =>
      simp only [collected, ih, List.flatMap_cons, List.reverse_append, List.append_assoc]

variable (P : L → TM2.Stmt (fun _ : K => Bool) L V)
  (source output : K) (start : L) (v0 : V) (S : K → List Bool)

theorem callback_call (q out out' : List Bool) (v : V) (t : ℕ)
    (h : ((advance P)^[t]) ⟨some start, v0, bank source output S q out⟩ =
      ⟨none, v, bank source output S q out'⟩) :
    ∃ t' ≤ t,
      run P source start v0 t'
        (cfg source output S (some (.inl start)) (v0, false, none) q out []) =
        cfg source output S (some (.inr .check)) (v, false, none) q out' [] := by
  have hh : (((advance P)^[t]) ⟨some start, v0, bank source output S q out⟩).l = none := by
    rw [h]
  obtain ⟨t', ht', hr⟩ := BitMachineSubroutine.lift_outputs P
    (program P source start v0) (some SamplerMachineSearch.Admin.check) (fun _ => rfl)
    (false, (none : Option Bool)) (fun _ : Unit => [])
    ⟨some start, v0, bank source output S q out⟩ t hh
  rw [h] at hr
  exact ⟨t', ht', hr⟩

/-- Every remaining counter is processed, then the actual all-ones test
halts. The output stack may change; all persistent banks are framed. -/
theorem map_suffix (n T : ℕ) (payload : List Bool → List Bool)
    (hP : ∀ q out : List Bool, q.length = n →
      ∃ (t : ℕ) (v : V), t ≤ T ∧
        ((advance P)^[t]) ⟨some start, v0, bank source output S q out⟩ =
          ⟨none, v, bank source output S q (payload q ++ out)⟩)
    (r : ℕ) (q out : List Bool) (hlen : q.length = n)
    (hcount : EncodedCommunication.bitsValue q + r + 1 = 2 ^ n) :
    ∃ (t : ℕ) (v : V), t ≤ (r + 1) * (T + 4 * n + 6) ∧
      run P source start v0 t
        (cfg source output S (some (.inl start)) (v0, false, none) q out []) =
        cfg source output S none (v, true, none) ((increment^[r]) q)
          (collected payload (List.iterate increment q (r + 1)) out) [] := by
  induction r generalizing q out with
  | zero =>
      obtain ⟨t, v, ht, hr⟩ := hP q out hlen
      obtain ⟨tp, htp, hcall⟩ := callback_call P source output start v0 S q out
        (payload q ++ out) v t hr
      have ho : q.all id = true := (SamplerMachineEnumeration.overflow_iff_max q).mpr (by
        rw [hlen]
        simpa using hcount)
      have hx := SamplerMachineSearch.exhausted_run P source start v0 (fun _ => false)
        (Function.update S output (payload q ++ out)) v q rfl ho
      refine ⟨(2 * q.length + 3) + tp, v, by rw [hlen]; omega, ?_⟩
      simp only [run, Function.iterate_add_apply]
      change run P source start v0 (2 * q.length + 3)
        (run P source start v0 tp _) = _
      rw [hcall]
      exact hx
  | succ r ih =>
      obtain ⟨t, v, ht, hr⟩ := hP q out hlen
      obtain ⟨tp, htp, hcall⟩ := callback_call P source output start v0 S q out
        (payload q ++ out) v t hr
      have ho : q.all id = false := by
        cases he : q.all id with
        | false => rfl
        | true =>
            have hm := (SamplerMachineEnumeration.overflow_iff_max q).mp he
            rw [hlen] at hm
            omega
      have hnlen : (increment q).length = n := by rw [increment_length, hlen]
      have hncount : EncodedCommunication.bitsValue (increment q) + r + 1 = 2 ^ n := by
        rw [SamplerMachineEnumeration.increment_value_of_not_overflow q ho]
        omega
      obtain ⟨tr, vr, htr, hrr⟩ := ih (increment q) (payload q ++ out) hnlen hncount
      obtain ⟨ts, hts, hs⟩ := SamplerMachineSearch.reject_run P source start v0 (fun _ => false)
        (Function.update S output (payload q ++ out)) v q rfl ho
      change run P source start v0 ts
        (cfg source output S (some (.inr .check)) (v, false, none) q (payload q ++ out) []) =
        cfg source output S (some (.inl start)) (v0, false, none)
          (increment q) (payload q ++ out) [] at hs
      refine ⟨tr + ts + tp, vr, ?_, ?_⟩
      · rw [hlen] at hts
        nlinarith
      · simp only [run, Function.iterate_add_apply]
        change run P source start v0 tr
          (run P source start v0 ts (run P source start v0 tp _)) = _
        rw [hcall, hs, hrr]
        simp only [List.iterate, collected, Function.iterate_succ_apply,
          Function.iterate_zero_apply]

theorem map_allWords (hdistinct : source ≠ output) (n T : ℕ)
    (row : List Bool → List Bool)
    (hP : ∀ q out : List Bool, q.length = n →
      ∃ (t : ℕ) (v : V), t ≤ T ∧
        ((advance P)^[t]) ⟨some start, v0, bank source output S q out⟩ =
          ⟨none, v, bank source output S q ((row q).reverse ++ out)⟩)
    (out : List Bool) :
    ∃ (t : ℕ) (v : V) (last : List Bool),
      t ≤ 2 ^ n * (T + 4 * n + 6) ∧ last.length = n ∧ last.all id = true ∧
      run P source start v0 t
        (cfg source output S (some (.inl start)) (v0, false, none)
          (List.replicate n false) out []) =
        cfg source output S none (v, true, none) last
          (((counterWords n).flatMap row).reverse ++ out) [] ∧
      (cfg (L := L) source output S none (v, true, none) last
        (((counterWords n).flatMap row).reverse ++ out) []).stk (.inl output) =
          (((counterWords n).flatMap row).reverse ++ out) := by
  have hz (m : ℕ) : EncodedCommunication.bitsValue (List.replicate m false) = 0 := by
    induction m with
    | zero => rfl
    | succ m ih => simp [List.replicate_succ, EncodedCommunication.bitsValue, Nat.bit_val, ih]
  have hpos : 0 < 2 ^ n := by positivity
  have hc : 2 ^ n - 1 + 1 = 2 ^ n := by omega
  obtain ⟨t, v, ht, hr⟩ := map_suffix P source output start v0 S n T
    (fun q => (row q).reverse) hP (2 ^ n - 1) (List.replicate n false) out
    (by simp) (by rw [hz]; omega)
  rw [hc, collected_reverse] at hr
  rw [hc] at ht
  refine ⟨t, v, _, ht, increment_iterate_length n (2 ^ n - 1), ?_, hr, ?_⟩
  · have hm := SamplerMachineEnumeration.overflow_iff_max
      ((increment^[2 ^ n - 1]) (List.replicate n false))
    apply hm.mpr
    rw [increment_iterate_length]
    have hv : ∀ j, j < 2 ^ n →
        EncodedCommunication.bitsValue ((increment^[j]) (List.replicate n false)) = j := by
      intro j hj
      induction j with
      | zero => simpa using hz n
      | succ j ih =>
          rw [Function.iterate_succ_apply', increment_value_mod,
            increment_iterate_length, ih (by omega), Nat.mod_eq_of_lt hj]
    rw [hv _ (by omega)]
    omega
  · simp only [cfg, SamplerMachineSearch.cfg, Sum.elim_inl,
      Function.update_of_ne hdistinct.symm, Function.update_self]

end EthInapproximability.CurrentPaper.SamplerMachineCounterMap
