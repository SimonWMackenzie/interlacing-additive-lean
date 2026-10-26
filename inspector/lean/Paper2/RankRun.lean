import Paper2.CanonicalEndpointRankBridge
import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! Unit 3, segment (1): the production endpoint-rank controller
`CanonicalEndpointRankMachine.program` run as ONE fixed physical program whose
finite-control inputs are read from cells and whose activity bit is written
to a cell.

`prog` on a seven-cell bank `RB U V X O T Kd A`:
* setup (at most three charged steps): pop the unary label index `t < 3`
  (cell 4) and the item-kind bit (cell 5, `true` = auxiliary) into the
  controller's `kind`/`item` fields (`t = 0, 1, 2` ↦ edge, left incidence,
  right incidence, the production `optionBoolIndex` order);
* the production controller, reused by name through the production stack
  embedding `stackStmt` (cells 0-3) and the production inliner
  `BitMachineInline.stmt` (its `halt` becomes a jump to the writer);
* one charged push of the controller's activity bit on cell 6.

`rank_run`: exact exit bank; `rank_value`: with `t = a / r % 3` and the
item-kind bit `z.isRight`, the physical output is exactly the value that
`ScanCoordDecode.scan_selected` assigns to the canonical scan. The operand
words themselves (endpoint fetch from the public graph bytes, the item value)
are entry cells here. -/

namespace Paper2.RankRun

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CanonicalEndpointRankMachine

abbrev R := Fin 7

inductive SL where
  | s0 | s1 | s2 | w
  deriving DecidableEq

abbrev WL := SL ⊕ CanonicalEndpointRankMachine.Label

def ιf : Fin 4 → R := ![0, 1, 2, 3]
def ι : Fin 4 ↪ R := ⟨ιf, by unfold ιf; decide⟩

def P' (l : CanonicalEndpointRankMachine.Label) :
    TM2.Stmt (fun _ : R => Bool) CanonicalEndpointRankMachine.Label Control :=
  stackStmt ι (CanonicalEndpointRankMachine.program l)

def startCtl : Control := {kind := .edge, item := .vertex}

def kindOfNat (t : ℕ) : Kind :=
  if t = 0 then .edge else if t = 1 then .leftIncidence else .rightIncidence

def itemOfBool (b : Bool) : ItemKind := if b then .auxiliary else .vertex

def prog : WL → TM2.Stmt (fun _ : R => Bool) WL Control
  | .inl .s0 => pop 4 (fun q b => if b = some true then {q with kind := .leftIncidence} else q)
      (branch (fun q => q.kind == .leftIncidence) (goto (fun _ => .inl .s1))
        (goto (fun _ => .inl .s2)))
  | .inl .s1 => pop 4 (fun q b => if b = some true then {q with kind := .rightIncidence} else q)
      (goto (fun _ => .inl .s2))
  | .inl .s2 => pop 5 (fun q b => if b = some true then {q with item := .auxiliary} else q)
      (goto (fun _ => .inr .scan))
  | .inl .w => push 6 (fun q => q.active) halt
  | .inr l => BitMachineInline.stmt Sum.inr id id (some (.inl .w)) (P' l)

def RB (U V X O T Kd A : List Bool) : R → List Bool := ![U, V, X, O, T, Kd, A]

theorem iter_trans {α : Type*} {f : α → α} {a b c : α} {m n : ℕ}
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[n + m] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

/-! ### Setup: the two finite-control fields from the two cells -/

theorem step_s0_nil (S : R → List Bool) (h : S 4 = []) :
    (advance prog)^[1] (⟨some (.inl .s0), startCtl, S⟩ : TM2.Cfg (fun _ : R => Bool) WL Control) =
      ⟨some (.inl .s2), startCtl, Function.update S 4 []⟩ := by
  rw [Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, prog, h, startCtl] <;> rfl

theorem step_s0_cons (S : R → List Bool) (x : List Bool) (h : S 4 = true :: x) :
    (advance prog)^[1] (⟨some (.inl .s0), startCtl, S⟩ : TM2.Cfg (fun _ : R => Bool) WL Control) =
      ⟨some (.inl .s1), {startCtl with kind := .leftIncidence}, Function.update S 4 x⟩ := by
  rw [Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, prog, h, startCtl] <;> rfl

theorem step_s1_nil (S : R → List Bool) (q : Control) (h : S 4 = []) :
    (advance prog)^[1] (⟨some (.inl .s1), q, S⟩ : TM2.Cfg (fun _ : R => Bool) WL Control) =
      ⟨some (.inl .s2), q, Function.update S 4 []⟩ := by
  rw [Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, prog, h]

theorem step_s1_cons (S : R → List Bool) (q : Control) (x : List Bool) (h : S 4 = true :: x) :
    (advance prog)^[1] (⟨some (.inl .s1), q, S⟩ : TM2.Cfg (fun _ : R => Bool) WL Control) =
      ⟨some (.inl .s2), {q with kind := .rightIncidence}, Function.update S 4 x⟩ := by
  rw [Function.iterate_one]
  simp [advance, TM2.step, TM2.stepAux, prog, h]

theorem step_s2 (S : R → List Bool) (q : Control) (b : Bool) (x : List Bool)
    (h : S 5 = b :: x) :
    (advance prog)^[1] (⟨some (.inl .s2), q, S⟩ : TM2.Cfg (fun _ : R => Bool) WL Control) =
      ⟨some (.inr .scan), (if b then {q with item := .auxiliary} else q),
        Function.update S 5 x⟩ := by
  rw [Function.iterate_one]
  cases b <;> simp [advance, TM2.step, TM2.stepAux, prog, h]

theorem setup_run (t : ℕ) (ht : t < 3) (b : Bool) (U V X O : List Bool) :
    ∃ n ≤ 3,
      (advance prog)^[n] (⟨some (.inl .s0), startCtl,
        RB U V X O (List.replicate t true) [b] []⟩ : TM2.Cfg (fun _ : R => Bool) WL Control) =
        ⟨some (.inr .scan), {kind := kindOfNat t, item := itemOfBool b},
          RB U V X O [] [] []⟩ := by
  interval_cases t
  · refine ⟨1 + 1, by omega, ?_⟩
    refine iter_trans (step_s0_nil _ (by rfl)) ?_
    rw [step_s2 _ _ b [] (by rfl)]
    cases b
    · congr 1; funext j; fin_cases j <;> rfl
    · congr 1; funext j; fin_cases j <;> rfl
  · refine ⟨1 + (1 + 1), by omega, ?_⟩
    refine iter_trans (iter_trans (step_s0_cons _ [] (by rfl)) (step_s1_nil _ _ (by rfl))) ?_
    rw [step_s2 _ _ b [] (by rfl)]
    cases b
    · congr 1; funext j; fin_cases j <;> rfl
    · congr 1; funext j; fin_cases j <;> rfl
  · refine ⟨1 + (1 + 1), by omega, ?_⟩
    refine iter_trans (iter_trans (step_s0_cons _ [true] (by rfl)) (step_s1_cons _ _ [] (by rfl))) ?_
    rw [step_s2 _ _ b [] (by rfl)]
    cases b
    · congr 1; funext j; fin_cases j <;> rfl
    · congr 1; funext j; fin_cases j <;> rfl

/-! ### The production controller, embedded and inlined -/

theorem ctrl_run (kind : Kind) (item : ItemKind) (u v x : ℕ) (T Kd A : List Bool) :
    ∃ n ≤ max u (max v x) + 3,
      (advance prog)^[n] (⟨some (.inr .scan), {kind := kind, item := item},
        RB (unaryWord u) (unaryWord v) (unaryWord x) [] T Kd A⟩ :
          TM2.Cfg (fun _ : R => Bool) WL Control) =
        ⟨some (.inl .w), Control.mk .edge .vertex .eq .eq .eq none none none
            (semanticActive kind item u v x),
          RB [] [] [] (List.replicate (semanticRank kind item u v x) true) T Kd A⟩ := by
  let W := RB (unaryWord u) (unaryWord v) (unaryWord x) [] T Kd A
  have hrun := BitMachineStackRun.run ι W CanonicalEndpointRankMachine.program
    (initial kind item u v x) (max u (max v x) + 3)
  rw [run_exact] at hrun
  have hhalt : (((advance P') ^[max u (max v x) + 3])
      (stackCfg ι W (initial kind item u v x))).l = none := by
    change (((advance (fun l => stackStmt ι (CanonicalEndpointRankMachine.program l)))^[_])
      (stackCfg ι W (initial kind item u v x))).l = none
    rw [hrun]
    rfl
  obtain ⟨n, hn, hr⟩ := BitMachineInline.outputs (K := R) Sum.inr id id (fun _ => rfl)
    (some (.inl .w)) P' prog (fun _ => rfl) (stackCfg ι W (initial kind item u v x))
    (max u (max v x) + 3) hhalt
  refine ⟨n, hn, ?_⟩
  have hrun' : ((advance P')^[max u (max v x) + 3]) (stackCfg ι W (initial kind item u v x)) =
      stackCfg ι W (output kind item u v x) := hrun
  rw [hrun'] at hr
  have hin : bank ι W (contents (unaryWord u) (unaryWord v) (unaryWord x) []) = W := by
    apply bank_eq_self
    intro k
    fin_cases k <;> rfl
  have hout : contents [] [] [] (List.replicate (semanticRank kind item u v x) true) =
      Function.update (Function.update (Function.update (Function.update
        (contents (unaryWord u) (unaryWord v) (unaryWord x) []) 0 []) 1 []) 2 []) 3
        (List.replicate (semanticRank kind item u v x) true) := by
    funext k; fin_cases k <;> rfl
  have hfin : bank ι W (contents [] [] [] (List.replicate (semanticRank kind item u v x) true)) =
      RB [] [] [] (List.replicate (semanticRank kind item u v x) true) T Kd A := by
    rw [hout, bank_update, bank_update, bank_update, bank_update, hin]
    funext j; fin_cases j <;> rfl
  simp only [BitMachineInline.cfg, stackCfg, initial, output,
    CanonicalEndpointRankMachine.cfg, id] at hr
  rw [hin, hfin] at hr
  exact hr

theorem write_step (q : Control) (S : R → List Bool) :
    advance prog (⟨some (.inl .w), q, S⟩ : TM2.Cfg (fun _ : R => Bool) WL Control) =
      ⟨none, q, Function.update S 6 (q.active :: S 6)⟩ := rfl

/-- The whole physical rank step: exact exit bank, explicit clock. -/
theorem rank_run (t : ℕ) (ht : t < 3) (b : Bool) (u v x : ℕ) :
    ∃ n ≤ max u (max v x) + 7, ∃ c,
      (advance prog)^[n] (⟨some (.inl .s0), startCtl,
        RB (unaryWord u) (unaryWord v) (unaryWord x) [] (List.replicate t true) [b] []⟩ :
          TM2.Cfg (fun _ : R => Bool) WL Control) =
        ⟨none, c, RB [] [] []
          (List.replicate (semanticRank (kindOfNat t) (itemOfBool b) u v x) true) [] []
          [semanticActive (kindOfNat t) (itemOfBool b) u v x]⟩ := by
  obtain ⟨n1, hn1, h1⟩ := setup_run t ht b (unaryWord u) (unaryWord v) (unaryWord x) []
  obtain ⟨n2, hn2, h2⟩ := ctrl_run (kindOfNat t) (itemOfBool b) u v x [] [] []
  refine ⟨1 + (n2 + n1), by omega, Control.mk .edge .vertex .eq .eq .eq none none none
    (semanticActive (kindOfNat t) (itemOfBool b) u v x), ?_⟩
  refine iter_trans (iter_trans h1 h2) ?_
  rw [Function.iterate_one, write_step]
  congr 1
  funext j; fin_cases j <;> rfl

/-- Label index to kind: the production `optionBoolIndex` order. -/
theorem kindOfNat_index (t : ℕ) (ht : t < 3) :
    kindOfNat t = CanonicalEndpointRankBridge.kindOfTag
      (CanonicalSourceLabels.optionBoolIndex.symm ⟨t, ht⟩) := by
  interval_cases t <;> rfl

/-- The item-kind bit written by the source-word split is `z.isRight`. -/
theorem itemOfBool_isRight {n k : ℕ} (z : Fin n ⊕ Fin k) :
    itemOfBool z.isRight = CanonicalEndpointRankBridge.itemKindOf z := by
  cases z <;> rfl

/-- Value identity: the two output cells of `rank_run`, at `t = a / r % 3`,
kind bit `z.isRight` and operands `(edge e false).val, (edge e true).val,
itemValue z`, are exactly the activity and the rank that
`ScanCoordDecode.scan_selected` gives the canonical scan. -/
theorem rank_value {s n m : ℕ} (edge : Fin m → Bool → Fin n) (e : Fin m)
    (z : Fin n ⊕ Fin (s - 3)) (t : ℕ) (ht : t < 3) :
    (if semanticActive (kindOfNat t) (itemOfBool z.isRight)
        (edge e false).val (edge e true).val (CanonicalEndpointRankBridge.itemValue z) then
      some (List.replicate (semanticRank (kindOfNat t) (itemOfBool z.isRight)
        (edge e false).val (edge e true).val (CanonicalEndpointRankBridge.itemValue z)) true).length
    else none) =
    (let tag := CanonicalSourceLabels.optionBoolIndex.symm ⟨t, ht⟩
     if semanticActive (CanonicalEndpointRankBridge.kindOfTag tag)
        (CanonicalEndpointRankBridge.itemKindOf z)
        (edge e false).val (edge e true).val (CanonicalEndpointRankBridge.itemValue z) then
      some (semanticRank (CanonicalEndpointRankBridge.kindOfTag tag)
        (CanonicalEndpointRankBridge.itemKindOf z)
        (edge e false).val (edge e true).val (CanonicalEndpointRankBridge.itemValue z))
     else none) := by
  rw [kindOfNat_index t ht, itemOfBool_isRight, List.length_replicate]

#print axioms setup_run
#print axioms ctrl_run
#print axioms rank_run
#print axioms rank_value

end

end Paper2.RankRun
