import CurrentAdditive.BoundedDyadicSearch
import EthInapproximability.CurrentPaper.BitMachineInline
import Mathlib.Tactic

set_option autoImplicit false

namespace CurrentAdditive.V40FirstPassingController

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper BitMachineEncoding
open PublicScheduleBoundedSearch

variable {K LB VB : Type*} [DecidableEq K]

abbrev Label (LB : Type*) := LB ⊕ Unit
abbrev Control (VB : Type*) := VB × Option Bool

/-- The predicate subprogram is called on the current unary counter. On
false its output bit is consumed and the counter is incremented once; on
true that bit is consumed and this fixed finite controller halts. -/
def program (P : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (entry : LB) (initial : VB) (counter flag : K) :
    Label LB → TM2.Stmt (fun _ : K => Bool) (Label LB) (Control VB)
  | .inl l => BitMachineInline.stmt Sum.inl (fun v => (v, none)) Prod.fst
      (some (.inr ())) (P l)
  | .inr _ => pop flag (fun v b => (v.1, b))
      (branch (fun v => v.2 == some true) halt
        (push counter (fun _ => true)
          (load (fun _ => (initial, none)) (goto (fun _ => .inl entry)))))

def bank (B : K → List Bool) (counter flag : K) (L : Nat) : K → List Bool :=
  Function.update (Function.update B counter (List.replicate L true)) flag []

def cfg (entry : LB) (initial : VB) (S : K → List Bool) :
    TM2.Cfg (fun _ : K => Bool) (Label LB) (Control VB) :=
  ⟨some (.inl entry), (initial, none), S⟩

def run (P : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (entry : LB) (initial : VB) (counter flag : K) (t : Nat)
    (c : TM2.Cfg (fun _ : K => Bool) (Label LB) (Control VB)) :=
  ((advance (program P entry initial counter flag))^[t]) c

theorem run_add (P : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (entry : LB) (initial : VB) (counter flag : K) (t u : Nat)
    (c : TM2.Cfg (fun _ : K => Bool) (Label LB) (Control VB)) :
    run P entry initial counter flag (t + u) c =
      run P entry initial counter flag u (run P entry initial counter flag t c) := by
  simpa only [run, Nat.add_comm] using
    Function.iterate_add_apply (advance (program P entry initial counter flag)) u t c

theorem body_to_route (P : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (entry : LB) (initial : VB) (counter flag : K)
    (S T : K → List Bool) (t : Nat)
    (h : ((advance P)^[t])
      (⟨some entry, initial, S⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) =
      ⟨none, initial, T⟩) :
    ∃ u ≤ t, run P entry initial counter flag u (cfg entry initial S) =
      ⟨some (.inr ()), (initial, none), T⟩ := by
  have hh := congrArg (fun c => c.l) h
  obtain ⟨u, hu, hr⟩ := BitMachineInline.outputs Sum.inl
    (fun v => (v, none)) Prod.fst (by intro v; rfl) (some (.inr ()))
    P (program P entry initial counter flag) (by intro l; rfl)
    (⟨some entry, initial, S⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) t hh
  rw [h] at hr
  exact ⟨u, hu, by simpa [run, cfg, BitMachineInline.cfg] using hr⟩

theorem route_true (P : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (entry : LB) (initial : VB) (counter flag : K)
    (S : K → List Bool) (hflag : S flag = []) :
    run P entry initial counter flag 1
      ⟨some (.inr ()), (initial, none), Function.update S flag [true]⟩ =
      ⟨none, (initial, some true), S⟩ := by
  have he : Function.update S flag [] = S := by rw [← hflag, Function.update_eq_self]
  simpa [run, advance, TM2.step, TM2.stepAux, program, Function.update_apply, he]

theorem route_false (P : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (entry : LB) (initial : VB) (counter flag : K) (hne : counter ≠ flag)
    (B : K → List Bool) (L : Nat) :
    run P entry initial counter flag 1
      ⟨some (.inr ()), (initial, none),
        Function.update (bank B counter flag L) flag [false]⟩ =
      cfg entry initial (bank B counter flag (L + 1)) := by
  have hcounter : bank B counter flag L counter = List.replicate L true := by
    simp [bank, hne]
  have hflag : bank B counter flag L flag = [] := by simp [bank]
  have he : Function.update (bank B counter flag L) flag [] = bank B counter flag L := by
    rw [← hflag, Function.update_eq_self]
  have hb : Function.update (bank B counter flag L) counter
      (true :: List.replicate L true) = bank B counter flag (L + 1) := by
    funext k
    by_cases hc : k = counter
    · subst k
      simp [bank, hne, List.replicate_succ]
    · by_cases hf : k = flag
      · subst k
        simp [bank, hne, hc]
      · simp [bank, hc, hf]
  simpa [run, advance, TM2.step, TM2.stepAux, program, cfg,
    Function.update_apply, he, hcounter, hb, hne]

/-- Operational first-passing composition. The supplied predicate run is an
explicit subprogram interface. This generic theorem is not an implementation
of a particular numerical test; that subprogram must be instantiated. -/
theorem firstInRange_run (P : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (entry : LB) (initial : VB) (counter flag : K) (hne : counter ≠ flag)
    (B : K → List Bool) (test : Nat → Bool) (T : Nat) :
    ∀ fuel start L,
      firstInRange test start fuel = some L →
      (∀ x, start ≤ x → x ≤ start + fuel →
        ∃ t ≤ T, ((advance P)^[t])
          (⟨some entry, initial, bank B counter flag x⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) =
          ⟨none, initial, Function.update (bank B counter flag x) flag [test x]⟩) →
      ∃ u ≤ (fuel + 1) * (T + 1),
        run P entry initial counter flag u (cfg entry initial (bank B counter flag start)) =
        ⟨none, (initial, some true), bank B counter flag L⟩ := by
  intro fuel
  induction fuel with
  | zero =>
      intro start L hfirst hbody
      cases ht : test start with
      | false => simp [firstInRange, ht] at hfirst
      | true =>
          have hL : L = start := by simpa [firstInRange, ht] using hfirst.symm
          subst L
          obtain ⟨t, htT, hr⟩ := hbody start le_rfl (by omega)
          obtain ⟨u, hu, he⟩ := body_to_route P entry initial counter flag _ _ t hr
          rw [ht] at he
          refine ⟨u + 1, by omega, ?_⟩
          rw [run_add, he]
          exact route_true P entry initial counter flag _ (by simp [bank])
  | succ fuel ih =>
      intro start L hfirst hbody
      obtain ⟨t, htT, hr⟩ := hbody start le_rfl (by omega)
      obtain ⟨u, hu, he⟩ := body_to_route P entry initial counter flag _ _ t hr
      cases ht : test start with
      | true =>
          have hL : L = start := by simpa [firstInRange, ht] using hfirst.symm
          subst L
          rw [ht] at he
          refine ⟨u + 1, ?_, ?_⟩
          · have hh : T + 1 ≤ (fuel + 1 + 1) * (T + 1) := Nat.le_mul_of_pos_left _ (by omega)
            omega
          · rw [run_add, he]
            exact route_true P entry initial counter flag _ (by simp [bank])
      | false =>
          have htail : firstInRange test (start + 1) fuel = some L := by
            simpa [firstInRange, ht] using hfirst
          obtain ⟨v, hv, hrest⟩ := ih (start + 1) L htail
            (by intro x hx1 hx2; exact hbody x (by omega) (by omega))
          rw [ht] at he
          have hnext : run P entry initial counter flag (u + 1)
              (cfg entry initial (bank B counter flag start)) =
              cfg entry initial (bank B counter flag (start + 1)) := by
            rw [run_add, he]
            exact route_false P entry initial counter flag hne B start
          refine ⟨(u + 1) + v, ?_, ?_⟩
          · have hsum : (fuel + 1 + 1) * (T + 1) = (fuel + 1) * (T + 1) + (T + 1) := by ring
            omega
          · rw [run_add, hnext]
            exact hrest

end CurrentAdditive.V40FirstPassingController
