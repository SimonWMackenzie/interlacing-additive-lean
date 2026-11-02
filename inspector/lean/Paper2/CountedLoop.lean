import EthInapproximability.CurrentPaper.BitMachineInline

/-! A generic counted loop (tool for segments 3–5: the default-word level loop
and the `k`-fold request recursion). ONE fixed program built from a body
program `P`: a test label pops one mark of a unary counter cell; on a mark it
restarts the body from its fixed start label and control, and the body's
halt returns to the test; on an empty counter it halts. `loop_run` composes
`j` checked body runs with an arbitrary per-iteration bank invariant into one
exact run with a charged clock `j * (B + 2) + 1`. Uses the production
`BitMachineInline.stmt`/`outputs` (no new simulation argument). -/

set_option maxHeartbeats 4000000

namespace Paper2.CountedLoop

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K L V : Type*} [DecidableEq K]

def loop (ctr : K) (P : L → TM2.Stmt (fun _ : K => Bool) L V) (p₀ : L) (v₀ : V) :
    Unit ⊕ L → TM2.Stmt (fun _ : K => Bool) (Unit ⊕ L) (Option Bool × V)
  | .inl _ => pop ctr (fun c b => (b, c.2))
      (branch (fun c => c.1.isSome) (load (fun _ => ((none : Option Bool), v₀))
        (goto (fun _ => .inr p₀))) halt)
  | .inr l => BitMachineInline.stmt (fun l => (.inr l : Unit ⊕ L))
      (fun v => ((none : Option Bool), v)) (fun c => c.2) (some (.inl ())) (P l)

theorem test_empty (ctr : K) (P : L → TM2.Stmt (fun _ : K => Bool) L V) (p₀ : L) (v₀ : V)
    (c : Option Bool × V) (S : K → List Bool) (hS : S ctr = []) :
    advance (loop ctr P p₀ v₀) (⟨some (.inl ()), c, S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Unit ⊕ L) (Option Bool × V)) =
      ⟨none, (none, c.2), S⟩ := by
  have hS' : Function.update S ctr [] = S := by rw [← hS]; exact Function.update_eq_self _ _
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, loop, hS, hS']

theorem test_mark (ctr : K) (P : L → TM2.Stmt (fun _ : K => Bool) L V) (p₀ : L) (v₀ : V)
    (c : Option Bool × V) (S : K → List Bool) (rest : List Bool) (hS : S ctr = true :: rest) :
    advance (loop ctr P p₀ v₀) (⟨some (.inl ()), c, S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Unit ⊕ L) (Option Bool × V)) =
      ⟨some (.inr p₀), (none, v₀), Function.update S ctr rest⟩ := by
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, loop, hS]

theorem body_run (ctr : K) (P : L → TM2.Stmt (fun _ : K => Bool) L V) (p₀ : L) (v₀ : V)
    (S T : K → List Bool) (v₁ : V) (t : ℕ)
    (h : ((advance P)^[t]) (⟨some p₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) L V) =
      ⟨none, v₁, T⟩) :
    ∃ n ≤ t, ((advance (loop ctr P p₀ v₀))^[n])
        (⟨some (.inr p₀), ((none : Option Bool), v₀), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (Unit ⊕ L) (Option Bool × V)) =
      ⟨some (.inl ()), ((none : Option Bool), v₁), T⟩ := by
  have hh : (((advance P)^[t]) (⟨some p₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) L V)).l =
      none := by rw [h]
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs (fun l => (.inr l : Unit ⊕ L))
    (fun v => ((none : Option Bool), v)) (fun c => c.2) (fun _ => rfl) (some (.inl ()))
    P (loop ctr P p₀ v₀) (fun _ => rfl)
    (⟨some p₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) L V) t hh
  rw [h] at hr
  exact ⟨n, hn, hr⟩

/-- `j` body runs with a bank invariant `S i` (the counter holds `j - i`
marks in `S i`; the body runs from `S i` with one mark removed to
`S (i+1)`), composed into ONE run of the loop. -/
theorem loop_run (ctr : K) (P : L → TM2.Stmt (fun _ : K => Bool) L V) (p₀ : L) (v₀ : V)
    (j Bd : ℕ) (S : ℕ → K → List Bool)
    (hctr : ∀ i ≤ j, S i ctr = List.replicate (j - i) true)
    (hbody : ∀ i < j, ∃ t ≤ Bd, ∃ v₁,
      ((advance P)^[t]) (⟨some p₀, v₀, Function.update (S i) ctr
        (List.replicate (j - i - 1) true)⟩ : TM2.Cfg (fun _ : K => Bool) L V) =
        ⟨none, v₁, S (i + 1)⟩) (c : Option Bool × V) :
    ∃ t ≤ j * (Bd + 2) + 1, ∃ c',
      ((advance (loop ctr P p₀ v₀))^[t])
        (⟨some (.inl ()), c, S 0⟩ :
          TM2.Cfg (fun _ : K => Bool) (Unit ⊕ L) (Option Bool × V)) =
        ⟨none, c', S j⟩ := by
  suffices H : ∀ m i, i + m = j → ∀ c : Option Bool × V,
      ∃ t ≤ m * (Bd + 2) + 1, ∃ c',
        ((advance (loop ctr P p₀ v₀))^[t])
          (⟨some (.inl ()), c, S i⟩ :
            TM2.Cfg (fun _ : K => Bool) (Unit ⊕ L) (Option Bool × V)) =
          ⟨none, c', S j⟩ by
    exact H j 0 (by omega) c
  intro m
  induction m with
  | zero =>
    intro i hi c
    have hij : i = j := by omega
    subst hij
    refine ⟨1, by omega, (none, c.2), ?_⟩
    rw [Function.iterate_one]
    exact test_empty ctr P p₀ v₀ c (S i) (by rw [hctr i le_rfl]; simp)
  | succ m ih =>
    intro i hi c
    have hlt : i < j := by omega
    obtain ⟨tb, htb, v₁, hb⟩ := hbody i hlt
    have hmark : S i ctr = true :: List.replicate (j - i - 1) true := by
      rw [hctr i (by omega)]
      have hji : j - i = (j - i - 1) + 1 := by omega
      conv_lhs => rw [hji]
      rfl
    have e1 := test_mark ctr P p₀ v₀ c (S i) _ hmark
    obtain ⟨n, hn, hr⟩ := body_run ctr P p₀ v₀ _ _ v₁ tb hb
    obtain ⟨t', ht', c', hrest⟩ := ih (i + 1) (by omega) ((none : Option Bool), v₁)
    refine ⟨t' + n + 1, ?_, c', ?_⟩
    · have : (m + 1) * (Bd + 2) + 1 = (Bd + 2) + (m * (Bd + 2) + 1) := by ring
      omega
    · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, e1,
        hr, hrest]

#print axioms test_empty
#print axioms test_mark
#print axioms body_run
#print axioms loop_run

end Paper2.CountedLoop
