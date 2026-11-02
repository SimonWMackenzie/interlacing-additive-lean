import EthInapproximability.CurrentPaper.BitMachineInline

/-!
# Inlining a finite program into selected ambient stacks

Source: frozen v8 `B-effectivity-details.tex` and `06-eth.tex`, composition
of concrete finite bit programs. Stack locations are embedded injectively;
the finite label/control translation is the existing inline compiler. The
simulation preserves every unselected stack and adds no hidden transition.
`bank` describes the starting configuration, not an uncharged instruction.
-/

namespace EthInapproximability.CurrentPaper.BitMachineStackEmbedding

open Turing BitMachineEncoding BitMachineSubroutine

variable {K J L L' V V' : Type*} [DecidableEq K] [DecidableEq J]

noncomputable def bank (ι : K ↪ J) (foreign : J → List Bool) (S : K → List Bool) : J → List Bool := by
  classical
  exact fun j => if h : ∃ k, ι k = j then S (Classical.choose h) else foreign j

theorem bank_at (ι : K ↪ J) (foreign : J → List Bool) (S : K → List Bool) (k : K) :
    bank ι foreign S (ι k) = S k := by
  classical
  unfold bank
  rw [dif_pos ⟨k, rfl⟩]
  congr 1
  exact ι.injective (Classical.choose_spec (show ∃ l, ι l = ι k from ⟨k, rfl⟩))

theorem bank_outside (ι : K ↪ J) (foreign : J → List Bool) (S : K → List Bool)
    (j : J) (h : ¬ ∃ k, ι k = j) : bank ι foreign S j = foreign j := by
  classical
  exact dif_neg h

theorem bank_restrict (ι : K ↪ J) (S : J → List Bool) :
    bank ι S (fun k => S (ι k)) = S := by
  classical
  funext j
  by_cases h : ∃ k, ι k = j
  · obtain ⟨k, rfl⟩ := h
    exact bank_at ι S _ k
  · exact bank_outside ι S _ j h

theorem bank_eq_self (ι : K ↪ J) (S : J → List Bool) (T : K → List Bool)
    (h : ∀ k, T k = S (ι k)) : bank ι S T = S := by
  have he : T = fun k => S (ι k) := funext h
  rw [he, bank_restrict]

theorem bank_update (ι : K ↪ J) (foreign : J → List Bool) (S : K → List Bool)
    (k : K) (word : List Bool) :
    bank ι foreign (Function.update S k word) = Function.update (bank ι foreign S) (ι k) word := by
  funext j
  by_cases h : ∃ l, ι l = j
  · obtain ⟨l, rfl⟩ := h
    rw [bank_at]
    by_cases he : l = k
    · subst l; simp
    · have hι : ι l ≠ ι k := fun hh => he (ι.injective hh)
      simp only [Function.update_of_ne he, Function.update_of_ne hι, bank_at]
  · have hι : j ≠ ι k := fun he => h ⟨k, he.symm⟩
    rw [bank_outside ι foreign _ j h, Function.update_of_ne hι, bank_outside ι foreign S j h]

def stackStmt (ι : K ↪ J) :
    TM2.Stmt (fun _ : K => Bool) L V → TM2.Stmt (fun _ : J => Bool) L V
  | .push k f q => .push (ι k) f (stackStmt ι q)
  | .peek k f q => .peek (ι k) f (stackStmt ι q)
  | .pop k f q => .pop (ι k) f (stackStmt ι q)
  | .load f q => .load f (stackStmt ι q)
  | .branch f q r => .branch f (stackStmt ι q) (stackStmt ι r)
  | .goto f => .goto f
  | .halt => .halt

noncomputable def stackCfg (ι : K ↪ J) (foreign : J → List Bool)
    (c : TM2.Cfg (fun _ : K => Bool) L V) : TM2.Cfg (fun _ : J => Bool) L V :=
  ⟨c.l, c.var, bank ι foreign c.stk⟩

theorem stack_stepAux (ι : K ↪ J) (foreign : J → List Bool)
    (q : TM2.Stmt (fun _ : K => Bool) L V) (v : V) (S : K → List Bool) :
    TM2.stepAux (stackStmt ι q) v (bank ι foreign S) =
      stackCfg ι foreign (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simpa only [stackStmt, TM2.stepAux, bank_at, ← bank_update] using ih v _
  | peek k f q ih => simpa only [stackStmt, TM2.stepAux, bank_at] using ih _ S
  | pop k f q ih => simpa only [stackStmt, TM2.stepAux, bank_at, ← bank_update] using ih _ _
  | load f q ih => exact ih _ S
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stackStmt, TM2.stepAux, h, cond_false, cond_true] <;> first
      | exact ihq v S
      | exact ihr v S
  | goto f => rfl
  | halt => rfl

def stmt (ι : K ↪ J) (labels : L → L') (embed : V → V') (read : V' → V)
    (next : Option L') (q : TM2.Stmt (fun _ : K => Bool) L V) :
    TM2.Stmt (fun _ : J => Bool) L' V' :=
  stackStmt ι (BitMachineInline.stmt labels embed read next q)

noncomputable def cfg (ι : K ↪ J) (foreign : J → List Bool)
    (labels : L → L') (embed : V → V') (next : Option L')
    (c : TM2.Cfg (fun _ : K => Bool) L V) : TM2.Cfg (fun _ : J => Bool) L' V' :=
  stackCfg ι foreign (BitMachineInline.cfg labels embed next c)

theorem stepAux (ι : K ↪ J) (foreign : J → List Bool)
    (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (q : TM2.Stmt (fun _ : K => Bool) L V) (v : V) (S : K → List Bool) :
    TM2.stepAux (stmt ι labels embed read next q) (embed v) (bank ι foreign S) =
      cfg ι foreign labels embed next (TM2.stepAux q v S) := by
  rw [stmt, stack_stepAux, BitMachineInline.stepAux labels embed read hread next]
  rfl

theorem step (ι : K ↪ J) (foreign : J → List Bool)
    (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : J => Bool) L' V')
    (hQ : ∀ l, Q (labels l) = stmt ι labels embed read next (P l))
    (c : TM2.Cfg (fun _ : K => Bool) L V) (hc : c.l ≠ none) :
    advance Q (cfg ι foreign labels embed next c) =
      cfg ι foreign labels embed next (advance P c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
      simpa only [advance, cfg, stackCfg, BitMachineInline.cfg, TM2.step, hQ, Option.getD_some] using
        stepAux ι foreign labels embed read hread next (P l) v S

theorem run_until (ι : K ↪ J) (foreign : J → List Bool)
    (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : J => Bool) L' V')
    (hQ : ∀ l, Q (labels l) = stmt ι labels embed read next (P l))
    (c : TM2.Cfg (fun _ : K => Bool) L V) (n : ℕ)
    (h : ∀ k < n, (((advance P)^[k]) c).l ≠ none) :
    ((advance Q)^[n]) (cfg ι foreign labels embed next c) =
      cfg ι foreign labels embed next (((advance P)^[n]) c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (fun k hk => h k (by omega)),
        step ι foreign labels embed read hread next P Q hQ _ (h n (by omega)),
        Function.iterate_succ_apply']

/-- Inline any actual terminating local run at selected stack locations.
Every unselected ambient stack retains its old contents throughout. -/
theorem outputs (ι : K ↪ J) (foreign : J → List Bool)
    (labels : L → L') (embed : V → V') (read : V' → V)
    (hread : Function.LeftInverse read embed) (next : Option L')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : J => Bool) L' V')
    (hQ : ∀ l, Q (labels l) = stmt ι labels embed read next (P l))
    (c : TM2.Cfg (fun _ : K => Bool) L V) (bound : ℕ)
    (hhalt : (((advance P)^[bound]) c).l = none) :
    ∃ n ≤ bound, ((advance Q)^[n]) (cfg ι foreign labels embed next c) =
      cfg ι foreign labels embed next (((advance P)^[bound]) c) := by
  obtain ⟨n, hn, _, heq, hfirst⟩ := first_halt_cfg P c bound hhalt
  exact ⟨n, hn, (run_until ι foreign labels embed read hread next P Q hQ c n hfirst).trans
    (congrArg (cfg ι foreign labels embed next) heq)⟩

end EthInapproximability.CurrentPaper.BitMachineStackEmbedding
