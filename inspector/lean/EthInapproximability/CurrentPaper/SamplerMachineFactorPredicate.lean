import EthInapproximability.CurrentPaper.SamplerMachineFactorBody
import EthInapproximability.CurrentPaper.SamplerMachineFactorSplit
import EthInapproximability.CurrentPaper.SamplerFactorEnumeration

/-!
# A bank-preserving finite factor predicate

Source: locked v8 Appendix E, `lem:exact-families`. A single `2*n`-bit
counter names both factors. The finite controller splits and restores that
counter, records nonconstant-factor flags, constructs all arithmetic inputs,
runs coefficient multiplication/comparison, and clears all work. Its terminal
Boolean therefore decides an actual proper factorization without modifying
the candidate or the counter. This is the concrete predicate installed in
the exhaustive finite search controller.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineFactorPredicate

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutineRenaming
open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration

abbrev Stack := SamplerMachineFactorBody.Stack
abbrev Label := SamplerMachineFactorBody.Label ⊕ SamplerMachineFactorSplit.Label
abbrev Control := SamplerMachineFactorBody.Control × SamplerMachineFactorSplit.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := (SamplerMachineFactorBody.initial, SamplerMachineFactorSplit.initial)

def emptyBank : (Stack ⊕ Fin 0) ≃ Stack where
  toFun := Sum.elim id Fin.elim0
  invFun := Sum.inl
  left_inv := by intro k; rcases k with k | k; rfl; exact Fin.elim0 k
  right_inv := by intro k; rfl

def splitStack : (SamplerMachineFactorSplit.Stack ⊕ Fin 4) ≃ Stack where
  toFun := Sum.elim (fun k => match k with
    | .candidate => .inl .candidate | .counter => .inr ()
    | .factorU => .inl .factorU | .factorV => .inl .factorV
    | .savedC => .inl .work | .savedQ => .inl .zeroA)
    (fun i => .inl (if i = 0 then .target else if i = 1 then .paddedU
      else if i = 2 then .reversedV else .zeroM))
  invFun := Sum.elim (fun k => match k with
    | .candidate => .inl .candidate | .factorU => .inl .factorU | .factorV => .inl .factorV
    | .work => .inl .savedC | .zeroA => .inl .savedQ
    | .target => .inr 0 | .paddedU => .inr 1 | .reversedV => .inr 2 | .zeroM => .inr 3)
    (fun _ => .inl .counter)
  left_inv := by intro k; rcases k with k | k; cases k <;> rfl; fin_cases k <;> rfl
  right_inv := by intro k; rcases k with k | k; cases k <;> rfl; cases k; rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt emptyBank (Equiv.refl _) (Equiv.refl _)
      (liftStmt (none : Option SamplerMachineFactorSplit.Label) (SamplerMachineFactorBody.program l))
  | .inr l => renameStmt splitStack (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftStmt (some (.inl .scanC)) (SamplerMachineFactorSplit.program l))

def cfg (l : Option Label) (s : Control)
    (c u v target padded multiplier zeroA zeroM work pair : List Bool) : Config :=
  ⟨l, s, (SamplerMachineFactorBody.cfg none s.1
    c u v target padded multiplier zeroA zeroM work pair).stk⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

def accepts (s : Control) : Bool :=
  s.2.foundU && s.2.foundV && s.1.1.2.2.1

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

theorem split_cfg (l : Option SamplerMachineFactorSplit.Label)
    (s : SamplerMachineFactorSplit.Control) (c pair u v work zeroA : List Bool) :
    renameCfg splitStack (Equiv.sumComm _ _) (Equiv.prodComm _ _)
      (liftCfg (some (.inl .scanC)) SamplerMachineFactorBody.initial (fun _ : Fin 4 => [])
        (SamplerMachineFactorSplit.cfg l s c pair u v work zeroA)) =
      cfg (match l with | none => some (.inl (.inl .scanC)) | some l => some (.inr l))
        (SamplerMachineFactorBody.initial, s) c u v [] [] [] zeroA [] work pair := by
  cases l <;> unfold renameCfg liftCfg cfg SamplerMachineFactorBody.cfg
  all_goals
    congr 1
    funext k
    rcases k with k | k
    · cases k <;> rfl
    · cases k; rfl

theorem split_call {n : ℕ} (c u v : BinaryWord n) :
    ∃ t ≤ 4 * n + 4,
      run t (cfg (some (.inr .scanU)) initial (encodeWord c) [] [] [] [] [] [] [] []
        (encodeWord u ++ encodeWord v)) =
      cfg (some (.inl (.inl .scanC)))
        (SamplerMachineFactorBody.initial,
          SamplerMachineFactorSplit.flags (decide (Nonconstant u)) (decide (Nonconstant v)))
        (encodeWord c) (encodeWord u) (encodeWord v) [] [] [] [] [] []
        (encodeWord u ++ encodeWord v) := by
  have hr := SamplerMachineFactorSplit.split_coefficients c u v
  change SamplerMachineFactorSplit.run (4 * n + 4)
    (SamplerMachineFactorSplit.cfg (some .scanU) SamplerMachineFactorSplit.initial
      (encodeWord c) (encodeWord u ++ encodeWord v) [] [] [] []) = _ at hr
  have hh : (SamplerMachineFactorSplit.run (4 * n + 4)
      (SamplerMachineFactorSplit.cfg (some .scanU) SamplerMachineFactorSplit.initial
        (encodeWord c) (encodeWord u ++ encodeWord v) [] [] [] [])).l = none := by
    rw [hr]; rfl
  obtain ⟨t, ht, h⟩ := lift_outputs_renamed splitStack (Equiv.sumComm _ _) (Equiv.prodComm _ _)
    SamplerMachineFactorSplit.program program (some (.inl .scanC)) (fun _ => rfl)
    SamplerMachineFactorBody.initial (fun _ : Fin 4 => [])
    (SamplerMachineFactorSplit.cfg (some .scanU) SamplerMachineFactorSplit.initial
      (encodeWord c) (encodeWord u ++ encodeWord v) [] [] [] []) (4 * n + 4) hh
  change ((advance program)^[t]) _ = renameCfg _ _ _
    (liftCfg _ _ _ (SamplerMachineFactorSplit.run (4 * n + 4) _)) at h
  rw [hr, split_cfg, split_cfg] at h
  exact ⟨t, ht, h⟩

theorem body_cfg (l : Option SamplerMachineFactorBody.Label)
    (s : SamplerMachineFactorBody.Control) (f : SamplerMachineFactorSplit.Control)
    (c u v target padded multiplier zeroA zeroM work pair : List Bool) :
    renameCfg emptyBank (Equiv.refl _) (Equiv.refl _)
      (liftCfg (none : Option SamplerMachineFactorSplit.Label) f (fun i : Fin 0 => Fin.elim0 i)
        (SamplerMachineFactorBody.cfg l s c u v target padded multiplier zeroA zeroM work pair)) =
      cfg (l.map Sum.inl) (s, f) c u v target padded multiplier zeroA zeroM work pair := by
  cases l <;> rfl

theorem body_call {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n)
    (f : SamplerMachineFactorSplit.Control) (pair : List Bool) :
    ∃ t ≤ 16 * n ^ 2 + 32 * n + 26,
      run t (cfg (some (.inl (.inl .scanC))) (SamplerMachineFactorBody.initial, f)
        (encodeWord c) (encodeWord u) (encodeWord v) [] [] [] [] [] [] pair) =
      cfg none
        (((none, SamplerMachineFactorTest.initial (decide (∀ j : Fin (2 * n),
          monicCoeff n c j.val = rawProductCoeff u v j.val))), none), f)
        (encodeWord c) [] [] [] [] [] [] [] [] pair := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineFactorBody.run_factorBody hn c u v pair
  have hh : (SamplerMachineFactorBody.run t
      (SamplerMachineFactorBody.cfg (some (.inl .scanC)) SamplerMachineFactorBody.initial
        (encodeWord c) (encodeWord u) (encodeWord v) [] [] [] [] [] [] pair)).l = none := by
    rw [hr]; rfl
  obtain ⟨t', ht', h⟩ := lift_outputs_renamed emptyBank (Equiv.refl _) (Equiv.refl _)
    SamplerMachineFactorBody.program program (none : Option SamplerMachineFactorSplit.Label)
    (fun _ => rfl) f (fun i : Fin 0 => Fin.elim0 i)
    (SamplerMachineFactorBody.cfg (some (.inl .scanC)) SamplerMachineFactorBody.initial
      (encodeWord c) (encodeWord u) (encodeWord v) [] [] [] [] [] [] pair) t hh
  change ((advance program)^[t']) _ = renameCfg _ _ _
    (liftCfg _ _ _ (SamplerMachineFactorBody.run t _)) at h
  rw [hr, body_cfg, body_cfg] at h
  exact ⟨t', ht'.trans ht, h⟩

def finalControl {n : ℕ} (c u v : BinaryWord n) : Control :=
  (((none, SamplerMachineFactorTest.initial (decide (∀ j : Fin (2 * n),
    monicCoeff n c j.val = rawProductCoeff u v j.val))), none),
    SamplerMachineFactorSplit.flags (decide (Nonconstant u)) (decide (Nonconstant v)))

/-- Fully implemented proper-factor predicate, with no preparation, local
machine, or runtime assumptions. Its whole input bank is restored. -/
theorem run_factorPredicate {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n) :
    ∃ t ≤ 16 * n ^ 2 + 36 * n + 30,
      run t (cfg (some (.inr .scanU)) initial (encodeWord c) [] [] [] [] [] [] [] []
        (encodeWord u ++ encodeWord v)) =
      cfg none (finalControl c u v) (encodeWord c) [] [] [] [] [] [] [] []
        (encodeWord u ++ encodeWord v) := by
  obtain ⟨ts, hts, hs⟩ := split_call c u v
  obtain ⟨tb, htb, hb⟩ := body_call hn c u v
    (SamplerMachineFactorSplit.flags (decide (Nonconstant u)) (decide (Nonconstant v)))
    (encodeWord u ++ encodeWord v)
  refine ⟨tb + ts, by omega, ?_⟩
  rw [run_add, hs, hb]
  rfl

theorem accepts_final {n : ℕ} (c u v : BinaryWord n) :
    accepts (finalControl c u v) = decide (Nonconstant u ∧ Nonconstant v ∧
      ∀ j : Fin (2 * n), monicCoeff n c j.val = rawProductCoeff u v j.val) := by
  simp [accepts, finalControl, SamplerMachineFactorSplit.flags,
    SamplerMachineFactorTest.initial, Bool.and_assoc]

def inputBank (c : List Bool) : Stack → List Bool :=
  (cfg none initial c [] [] [] [] [] [] [] [] []).stk

theorem inputBank_update (c q : List Bool) :
    Function.update (inputBank c) (.inr ()) q =
      (cfg none initial c [] [] [] [] [] [] [] [] q).stk := by
  funext k
  rcases k with k | k
  · cases k <;> rfl
  · cases k; rfl

/-- Literal all-width-input subroutine contract used by the inner search.
The supplied counter may be any `2*n` bits, and every work stack is restored.
No correctness or runtime of another unimplemented procedure is assumed. -/
theorem predicate_contract {n : ℕ} (hn : 0 < n) (c : BinaryWord n)
    (q : List Bool) (hq : q.length = 2 * n) :
    ∃ (t : ℕ) (s : Control), t ≤ 16 * n ^ 2 + 36 * n + 30 ∧
      ((advance program)^[t])
        ⟨some (.inr .scanU), initial, Function.update (inputBank (encodeWord c)) (.inr ()) q⟩ =
        ⟨none, s, Function.update (inputBank (encodeWord c)) (.inr ()) q⟩ ∧
      accepts s = SamplerFactorEnumeration.factorPredicate n c q := by
  obtain ⟨u, v, hqv⟩ := SamplerFactorEnumeration.exists_counter_decomposition n q hq
  subst q
  obtain ⟨t, ht, hr⟩ := run_factorPredicate hn c u v
  refine ⟨t, finalControl c u v, ht, ?_, ?_⟩
  · rw [inputBank_update]
    exact hr
  · rw [accepts_final, SamplerFactorEnumeration.factorPredicate_encoded]
    simp only [Bool.decide_and, Bool.and_assoc]

end EthInapproximability.CurrentPaper.SamplerMachineFactorPredicate
