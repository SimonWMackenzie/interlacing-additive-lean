import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Inlining a finite-control program on the same stack bank

Source: frozen v8 `B-effectivity-details.tex`, the concrete bit-model
implementation. This is a syntactic compiler with an exact execution
simulation. A local halt becomes the chosen continuation. Only finite
control is translated; every stack instruction remains a stack instruction.
-/

namespace EthInapproximability.CurrentPaper.BitMachineInline

open Turing BitMachineEncoding BitMachineSubroutine

variable {K L L' V V' : Type*} [DecidableEq K]

def stmt (labels : L → L') (embed : V → V') (read : V' → V)
    (next : Option L') :
    TM2.Stmt (fun _ : K => Bool) L V → TM2.Stmt (fun _ : K => Bool) L' V'
  | .push k b q => .push k (fun v => b (read v)) (stmt labels embed read next q)
  | .peek k f q => .peek k (fun v b => embed (f (read v) b))
      (stmt labels embed read next q)
  | .pop k f q => .pop k (fun v b => embed (f (read v) b))
      (stmt labels embed read next q)
  | .load f q => .load (fun v => embed (f (read v))) (stmt labels embed read next q)
  | .branch f q r => .branch (fun v => f (read v))
      (stmt labels embed read next q) (stmt labels embed read next r)
  | .goto f => .goto (fun v => labels (f (read v)))
  | .halt => match next with | none => .halt | some l => .goto (fun _ => l)

def cfg (labels : L → L') (embed : V → V') (next : Option L')
    (c : TM2.Cfg (fun _ : K => Bool) L V) : TM2.Cfg (fun _ : K => Bool) L' V' :=
  ⟨match c.l with | none => next | some l => some (labels l), embed c.var, c.stk⟩

theorem stepAux (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (q : TM2.Stmt (fun _ : K => Bool) L V) (v : V) (S : K → List Bool) :
    TM2.stepAux (stmt labels embed read next q) (embed v) S =
      cfg labels embed next (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa only [stmt, TM2.stepAux, hread v] using ih v _
  | peek k f q ih => simpa only [stmt, TM2.stepAux, hread v] using ih _ S
  | pop k f q ih => simpa only [stmt, TM2.stepAux, hread v] using ih _ _
  | load f q ih => simpa only [stmt, TM2.stepAux, hread v] using ih _ S
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stmt, TM2.stepAux, hread v, h, cond_false, cond_true] <;> first
      | exact ihq v S
      | exact ihr v S
  | goto f => simp only [stmt, TM2.stepAux, cfg, hread v]
  | halt => cases next <;> rfl

theorem step (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : K => Bool) L' V')
    (hQ : ∀ l, Q (labels l) = stmt labels embed read next (P l))
    (c : TM2.Cfg (fun _ : K => Bool) L V) (hc : c.l ≠ none) :
    advance Q (cfg labels embed next c) = cfg labels embed next (advance P c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
      simpa only [advance, cfg, TM2.step, hQ, Option.getD_some] using
        stepAux labels embed read hread next (P l) v S

theorem run_until (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : K => Bool) L' V')
    (hQ : ∀ l, Q (labels l) = stmt labels embed read next (P l))
    (c : TM2.Cfg (fun _ : K => Bool) L V) (n : ℕ)
    (h : ∀ k < n, (((advance P)^[k]) c).l ≠ none) :
    ((advance Q)^[n]) (cfg labels embed next c) =
      cfg labels embed next (((advance P)^[n]) c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (fun k hk => h k (by omega)),
        step labels embed read hread next P Q hQ _ (h n (by omega)),
        Function.iterate_succ_apply']

/-- The actual first halting run of a local program is executed without
extra transitions and with the exact final contents of every stack. -/
theorem outputs (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : K => Bool) L' V')
    (hQ : ∀ l, Q (labels l) = stmt labels embed read next (P l))
    (c : TM2.Cfg (fun _ : K => Bool) L V) (bound : ℕ)
    (hhalt : (((advance P)^[bound]) c).l = none) :
    ∃ n ≤ bound, ((advance Q)^[n]) (cfg labels embed next c) =
      cfg labels embed next (((advance P)^[bound]) c) := by
  obtain ⟨n, hn, _, heq, hfirst⟩ := first_halt_cfg P c bound hhalt
  exact ⟨n, hn, (run_until labels embed read hread next P Q hQ c n hfirst).trans
    (congrArg (cfg labels embed next) heq)⟩

end EthInapproximability.CurrentPaper.BitMachineInline
