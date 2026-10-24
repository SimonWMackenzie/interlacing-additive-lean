import EthInapproximability.CurrentPaper.SamplerMachineFactorPrepare
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-!
# Preparing, testing, and clearing one pair of trial factors

Source: locked v8 Appendix E, `lem:exact-families`. This controller composes
the literal input-preparation and product-comparison programs. It explicitly
clears their data banks before and after multiplication. The source candidate
and the foreign factor-pair counter are preserved. The final comparison flag
stays in finite control for the surrounding exhaustive search.
-/

namespace EthInapproximability.CurrentPaper.SamplerMachineFactorBody

open Turing BitMachineEncoding BitMachineComposition BitMachineSubroutineRenaming
open ExecutableSmallBiasSampler SamplerMachine SamplerEnumeration

inductive Admin where
  | before : Fin 3 → Admin
  | after : Fin 9 → Admin
  | done
  deriving DecidableEq, Fintype

abbrev Stack := SamplerMachineFactorPrepare.Stack ⊕ Unit
abbrev Label := SamplerMachineFactorPrepare.Label ⊕ (SamplerMachineFactorTest.Label ⊕ Admin)
abbrev BaseControl := SamplerMachineFactorPrepare.Control × SamplerMachineFactorTest.Control
abbrev Control := BaseControl × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := ((none, SamplerMachineFactorTest.initial true), none)

def prepControl : (SamplerMachineFactorPrepare.Control × (SamplerMachineFactorTest.Control × Option Bool)) ≃ Control where
  toFun := fun s => ((s.1, s.2.1), s.2.2)
  invFun := fun s => (s.1.1, s.1.2, s.2)
  left_inv := by intro s; rfl
  right_inv := by intro s; rfl

def testStack : (SamplerMachineFactorTest.Stack ⊕ Fin 3) ≃ Stack where
  toFun := Sum.elim
    (Sum.elim (Sum.elim
      (fun i => .inl (if i = 0 then .zeroA else if i = 1 then .paddedU
        else if i = 2 then .factorU else .factorV))
      (fun i => .inl (if i = 0 then .zeroM else .reversedV)))
      (fun _ => .inl .target))
    (fun i => if i = 0 then .inl .candidate else if i = 1 then .inl .work else .inr ())
  invFun := Sum.elim (fun k => match k with
    | .candidate => .inr 0 | .work => .inr 1
    | .zeroA => .inl (.inl (.inl 0)) | .paddedU => .inl (.inl (.inl 1))
    | .factorU => .inl (.inl (.inl 2)) | .factorV => .inl (.inl (.inl 3))
    | .zeroM => .inl (.inl (.inr 0)) | .reversedV => .inl (.inl (.inr 1))
    | .target => .inl (.inr ())) (fun _ => .inr 2)
  left_inv := by
    intro k
    rcases k with ((k | k) | k) | k <;> (try fin_cases k) <;> rfl
  right_inv := by intro k; rcases k with k | k; cases k <;> rfl; cases k; rfl

def testLabel : (SamplerMachineFactorTest.Label ⊕ (SamplerMachineFactorPrepare.Label ⊕ Admin)) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l)) (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv := by intro l; rcases l with l | (l | l) <;> rfl
  right_inv := by intro l; rcases l with l | (l | l) <;> rfl

def testControl : (SamplerMachineFactorTest.Control × (SamplerMachineFactorPrepare.Control × Option Bool)) ≃ Control where
  toFun := fun s => ((s.2.1, s.1), s.2.2)
  invFun := fun s => (s.1.2, s.1.1, s.2)
  left_inv := by intro s; rfl
  right_inv := by intro s; rfl

def beforeBank : Fin 2 → Stack := fun i => .inl (if i = 0 then .factorU else .factorV)

def afterBank : Fin 8 → Stack := fun i => .inl
  (if i = 0 then .factorU else if i = 1 then .factorV else if i = 2 then .target
  else if i = 3 then .paddedU else if i = 4 then .reversedV else if i = 5 then .zeroA
  else if i = 6 then .zeroM else .work)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt (Equiv.refl _) (Equiv.refl _) prepControl
      (liftStmt (some (.inr (.before 0))) (SamplerMachineFactorPrepare.program l))
  | .inr (.inl l) => renameStmt testStack testLabel testControl
      (liftStmt (some (.inr (.after 0))) (SamplerMachineFactorTest.program l))
  | .inr (.inr (.before i)) =>
      if h : i.val < 2 then BitMachineClearBank.clearStep (beforeBank ⟨i.val, h⟩)
        (.inr (.inr (.before i))) (.inr (.inr (.before ⟨i.val + 1, by omega⟩)))
      else BitMachineClearBank.finishStep (fun s => (s.1, SamplerMachineFactorTest.initial true))
        (.inr (.inl (.inl (.inr (.inr ())))))
  | .inr (.inr (.after i)) =>
      if h : i.val < 8 then BitMachineClearBank.clearStep (afterBank ⟨i.val, h⟩)
        (.inr (.inr (.after i))) (.inr (.inr (.after ⟨i.val + 1, by omega⟩)))
      else BitMachineClearBank.finishStep id (.inr (.inr .done))
  | .inr (.inr .done) => .halt

def cfg (l : Option Label) (s : Control)
    (c u v target padded multiplier zeroA zeroM work pair : List Bool) : Config :=
  ⟨l, s, Sum.elim (SamplerMachineFactorPrepare.stackContents c u v target padded multiplier zeroA zeroM work)
    (fun _ => pair)⟩

def run (t : ℕ) (q : Config) := ((advance program)^[t]) q

private theorem run_add (t s : ℕ) (q : Config) : run (t + s) q = run t (run s q) :=
  Function.iterate_add_apply _ _ _ _

theorem prep_cfg (l : Option SamplerMachineFactorPrepare.Label) (s : SamplerMachineFactorPrepare.Control) (st : SamplerMachineFactorTest.Control)
    (c u v target padded multiplier zeroA zeroM work pair : List Bool) :
    renameCfg (Equiv.refl Stack) (Equiv.refl Label) prepControl
      (liftCfg (some (.inr (.before 0))) (st, (none : Option Bool)) (fun _ : Unit => pair)
        (SamplerMachineFactorPrepare.cfg l s c u v target padded multiplier zeroA zeroM work)) =
      cfg (match l with | none => some (.inr (.inr (.before 0))) | some l => some (.inl l))
        ((s, st), none) c u v target padded multiplier zeroA zeroM work pair := by
  cases l <;> rfl

theorem prepare_call {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n) (pair : List Bool) :
    ∃ t ≤ 6 * n + 6,
      run t (cfg (some (.inl .scanC)) initial (encodeWord c) (encodeWord u) (encodeWord v)
        [] [] [] [] [] [] pair) =
      cfg (some (.inr (.inr (.before 0)))) initial (encodeWord c) (encodeWord u) (encodeWord v)
        (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2))) [] pair := by
  have h := SamplerMachineFactorPrepare.prepare_coefficients hn c u v
  have hh : (SamplerMachineFactorPrepare.run (6 * n + 6)
      (SamplerMachineFactorPrepare.cfg (some .scanC) none (encodeWord c) (encodeWord u) (encodeWord v)
        [] [] [] [] [] [])).l = none := by rw [h]; rfl
  obtain ⟨t, ht, hr⟩ := lift_outputs_renamed (Equiv.refl Stack) (Equiv.refl Label) prepControl
    SamplerMachineFactorPrepare.program program (some (.inr (.before 0))) (fun _ => rfl)
    (SamplerMachineFactorTest.initial true, (none : Option Bool)) (fun _ : Unit => pair)
    (SamplerMachineFactorPrepare.cfg (some .scanC) none (encodeWord c) (encodeWord u) (encodeWord v)
      [] [] [] [] [] []) (6 * n + 6) hh
  change ((advance program)^[t]) _ = renameCfg _ _ _
    (liftCfg _ _ _ (SamplerMachineFactorPrepare.run (6 * n + 6) _)) at hr
  rw [h, prep_cfg, prep_cfg] at hr
  exact ⟨t, ht, hr⟩

theorem clear_before (c u v target padded multiplier zeroA zeroM work pair : List Bool) :
    run (u.length + v.length + 3)
      (cfg (some (.inr (.inr (.before 0)))) initial
        c u v target padded multiplier zeroA zeroM work pair) =
      cfg (some (.inr (.inl (.inl (.inr (.inr ())))))) initial
        c [] [] target padded multiplier zeroA zeroM work pair := by
  let S := (cfg none initial c u v target padded multiplier zeroA zeroM work pair).stk
  have hi : Function.Injective beforeBank := by decide
  have hr := BitMachineClearBank.clear_bank_run program
    (fun s : BaseControl => (s.1, SamplerMachineFactorTest.initial true))
    (.inr (.inl (.inl (.inr (.inr ()))))) 2 beforeBank hi
    (fun i => .inr (.inr (.before i)))
    (by intro i; fin_cases i <;> rfl) (by rfl)
    (none, SamplerMachineFactorTest.initial true) S
  have hs : (∑ i : Fin 2, (S (beforeBank i)).length) = u.length + v.length := by
    simp [S, cfg, beforeBank, SamplerMachineFactorPrepare.stackContents, Fin.sum_univ_two]
  rw [hs] at hr
  have hc : BitMachineClearBank.cleared beforeBank S =
      (cfg none initial c [] [] target padded multiplier zeroA zeroM work pair).stk := by
    funext k
    rcases k with k | k
    · cases k <;> simp [BitMachineClearBank.cleared, S, cfg, beforeBank,
        SamplerMachineFactorPrepare.stackContents, Fin.exists_fin_succ]
    · cases k
      simp [BitMachineClearBank.cleared, S, cfg, beforeBank]
  rw [hc] at hr
  exact hr

def testForeign (c work pair : List Bool) : Fin 3 → List Bool :=
  fun i => if i = 0 then c else if i = 1 then work else pair

theorem test_cfg (l : Option SamplerMachineFactorTest.Label)
    (st : SamplerMachineFactorTest.Control)
    (a padded wu wv modulus multiplier target c work pair : List Bool) :
    renameCfg testStack testLabel testControl
      (liftCfg (some (.inr (.after 0))) (none, (none : Option Bool))
        (testForeign c work pair)
        (SamplerMachineFactorTest.cfg l st a padded wu wv modulus multiplier target)) =
      cfg (match l with
        | none => some (.inr (.inr (.after 0)))
        | some l => some (.inr (.inl l))) ((none, st), none)
        c wu wv target padded multiplier a modulus work pair := by
  cases l <;> unfold renameCfg liftCfg cfg SamplerMachineFactorTest.cfg
  all_goals
    congr 1
    funext k
    rcases k with k | k
    · cases k <;> rfl
    · cases k; rfl

theorem test_call {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n) (pair : List Bool) :
    ∃ t ≤ (2 * n) * (4 * (2 * n) + 5) + 4 * n + 3,
      run t (cfg (some (.inr (.inl (.inl (.inr (.inr ())))))) initial
        (encodeWord c) [] []
        (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2))) [] pair) =
      cfg (some (.inr (.inr (.after 0))))
        ((none, SamplerMachineFactorTest.initial (decide (∀ j : Fin (2 * n),
          monicCoeff n c j.val = rawProductCoeff u v j.val))), none)
        (encodeWord c) [] []
        (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val)) [] []
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2))) [] pair := by
  obtain ⟨t, ht, hr⟩ := SamplerMachineFactorTest.run_fixedFactorProduct hn c u v
  have hh : (SamplerMachineFactorTest.run t
      (SamplerMachineFactorTest.cfg (some (.inl (.inr (.inr ()))))
        (SamplerMachineFactorTest.initial true)
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val)) [] []
        (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
        (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
        (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val)))).l = none := by
    rw [hr]; rfl
  obtain ⟨t', ht', hh'⟩ := lift_outputs_renamed testStack testLabel testControl
    SamplerMachineFactorTest.program program (some (.inr (.after 0))) (fun _ => rfl)
    (none, (none : Option Bool)) (testForeign (encodeWord c) [] pair)
    (SamplerMachineFactorTest.cfg (some (.inl (.inr (.inr ()))))
      (SamplerMachineFactorTest.initial true)
      (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
      (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val)) [] []
      (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
      (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
      (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))) t hh
  change ((advance program)^[t']) _ = renameCfg _ _ _
    (liftCfg _ _ _ (SamplerMachineFactorTest.run t _)) at hh'
  rw [hr, test_cfg, test_cfg] at hh'
  exact ⟨t', ht'.trans ht, hh'⟩

theorem clear_after (flag : Bool) (c target padded zeroM pair : List Bool) :
    run (target.length + padded.length + zeroM.length + 10)
      (cfg (some (.inr (.inr (.after 0))))
        ((none, SamplerMachineFactorTest.initial flag), none)
        c [] [] target padded [] [] zeroM [] pair) =
      cfg none ((none, SamplerMachineFactorTest.initial flag), none)
        c [] [] [] [] [] [] [] [] pair := by
  let s : BaseControl := (none, SamplerMachineFactorTest.initial flag)
  let S := (cfg none (s, none) c [] [] target padded [] [] zeroM [] pair).stk
  have hi : Function.Injective afterBank := by decide
  have hr := BitMachineClearBank.clear_bank_run program id (.inr (.inr .done))
    8 afterBank hi (fun i => .inr (.inr (.after i)))
    (by intro i; fin_cases i <;> rfl) (by rfl) s S
  have hs : (∑ i : Fin 8, (S (afterBank i)).length) =
      target.length + padded.length + zeroM.length := by
    simp [S, cfg, afterBank, SamplerMachineFactorPrepare.stackContents, Fin.sum_univ_succ]
    omega
  rw [hs] at hr
  have hc : BitMachineClearBank.cleared afterBank S =
      (cfg none (s, none) c [] [] [] [] [] [] [] [] pair).stk := by
    funext k
    rcases k with k | k
    · cases k <;> simp [BitMachineClearBank.cleared, S, cfg, afterBank,
        SamplerMachineFactorPrepare.stackContents, Fin.exists_fin_succ]
    · cases k
      simp [BitMachineClearBank.cleared, S, cfg, afterBank]
  rw [hc] at hr
  change run (target.length + padded.length + zeroM.length + 8 + 1)
    (cfg (some (.inr (.inr (.after 0))))
      ((none, SamplerMachineFactorTest.initial flag), none)
      c [] [] target padded [] [] zeroM [] pair) =
    cfg (some (.inr (.inr .done)))
      ((none, SamplerMachineFactorTest.initial flag), none)
      c [] [] [] [] [] [] [] [] pair at hr
  have ht : target.length + padded.length + zeroM.length + 10 =
      1 + (target.length + padded.length + zeroM.length + 8 + 1) := by omega
  rw [ht, run_add]
  rw [hr]
  rfl

/-- A single concrete finite program prepares the trial inputs, multiplies,
compares, and clears all work. There is no product-preparation or runtime
premise in this theorem. Original factor words are caller-owned temporary
copies and are consumed; candidate and factor-pair counter are preserved. -/
theorem run_factorBody {n : ℕ} (hn : 0 < n) (c u v : BinaryWord n) (pair : List Bool) :
    ∃ t ≤ 16 * n ^ 2 + 32 * n + 26,
      run t (cfg (some (.inl .scanC)) initial (encodeWord c) (encodeWord u) (encodeWord v)
        [] [] [] [] [] [] pair) =
      cfg none ((none, SamplerMachineFactorTest.initial (decide (∀ j : Fin (2 * n),
        monicCoeff n c j.val = rawProductCoeff u v j.val))), none)
        (encodeWord c) [] [] [] [] [] [] [] [] pair := by
  obtain ⟨tp, htp, hp⟩ := prepare_call hn c u v pair
  have hb := clear_before (encodeWord c) (encodeWord u) (encodeWord v)
    (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))
    (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val))
    (encodeWord (fun i : Fin (2 * n) => rawCoeff v i.val)).reverse
    (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2)))
    (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2))) [] pair
  simp only [encodeWord_length] at hb
  obtain ⟨tt, htt, ht⟩ := test_call hn c u v pair
  have ha := clear_after (decide (∀ j : Fin (2 * n),
      monicCoeff n c j.val = rawProductCoeff u v j.val)) (encodeWord c)
    (encodeWord (fun i : Fin (2 * n) => monicCoeff n c i.val))
    (encodeWord (fun i : Fin (2 * n) => rawCoeff u i.val))
    (encodeWord (fun _ : Fin (2 * n) => (0 : ZMod 2))) pair
  simp only [encodeWord_length] at ha
  refine ⟨(2 * n + 2 * n + 2 * n + 10) + (tt + ((n + n + 3) + tp)), ?_, ?_⟩
  · nlinarith
  · rw [run_add (2 * n + 2 * n + 2 * n + 10) (tt + ((n + n + 3) + tp)),
      run_add tt ((n + n + 3) + tp), run_add (n + n + 3) tp, hp, hb, ht, ha]

end EthInapproximability.CurrentPaper.SamplerMachineFactorBody
