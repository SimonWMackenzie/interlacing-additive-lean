import EthInapproximability.CurrentPaper.WeightedRawRowsSource
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.SourceOriginalBranchPackets
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.ETHParameterScaleEdgeCandidate
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineLogCopy
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.GraphCountBridge
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineStackGrowth
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.EffectiveIteration

/-! # Raw-word producer: the global bank and generic composition tools

Lane `owner:b-weighted-raw-words` (Paper B, unit 2, map item 1).
One fixed Boolean-stack bank `Global` contains the weighted consumer region
(`WeightedScalarComplete.Stack`, the admitted start bank of
`WeightedRawRowsSource`) and an auxiliary region with the packet input, the
master words and one private region per embedded production machine.
Nothing here is an instruction: these are the bank layout, a guarded
sequential composition (one charged handoff that halts on a rejected parse),
a physical clear program, and bookkeeping lemmas. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

/-- Auxiliary (non-consumer) cells. `input` is the single input stack; the
next nine are the master words; the rest are private scratch regions. -/
inductive Aux where
  | input | N | Gw | C | B | E | Y | Jc | K
  | cs
  | w (i : Fin 8)
  | parse (i : Fin 2)
  | pw (i : Fin 2)
  | mul (i : Fin 3)
  | edge (k : ETHScaleEdgePreparation.Stack)
  | log (k : ETHParameterScaleMachineLogCopy.Stack)
  | graph (k : GraphCountBridge.Stack)
  | nat (r : Fin 4) (i : ℕ)
  deriving DecidableEq

abbrev Cons := WeightedScalarComplete.Stack
abbrev Global := Cons ⊕ Aux

def aux (a : Aux) : Global := .inr a
def cons (x : Cons) : Global := .inl x

/-- The start bank: only the input stack holds the packet. -/
def startBank (packet : List Bool) : Global → List Bool :=
  Function.update (fun _ => []) (aux .input) packet

/-! ## Halting is stationary -/

theorem iterate_halted {K L V : Type*} [DecidableEq K]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (hc : c.l = none) (t : ℕ) :
    ((advance P)^[t]) c = c := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih]
      rcases c with ⟨l, v, S⟩
      cases hc
      rfl

theorem iterate_mono_halted {K L V : Type*} [DecidableEq K]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c d : TM2.Cfg (fun _ : K => Bool) L V) (t u : ℕ) (htu : t ≤ u)
    (h : ((advance P)^[t]) c = d) (hd : d.l = none) :
    ((advance P)^[u]) c = d := by
  rw [show u = (u - t) + t by omega, Function.iterate_add_apply, h,
    iterate_halted P d hd]

/-! ## Region runs: a local run of an embedded program -/

theorem region_run {K J L V : Type*} [DecidableEq K] [DecidableEq J]
    (ι : K ↪ J) (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c c' : TM2.Cfg (fun _ : K => Bool) L V) (t : ℕ)
    (h : ((advance P)^[t]) c = c') (G : J → List Bool)
    (hG : ∀ k, c.stk k = G (ι k)) :
    ((advance (fun l => stackStmt ι (P l)))^[t])
        (⟨c.l, c.var, G⟩ : TM2.Cfg (fun _ : J => Bool) L V) =
      ⟨c'.l, c'.var, bank ι G c'.stk⟩ := by
  have hs : stackCfg ι G c = ⟨c.l, c.var, G⟩ := by
    unfold stackCfg
    rw [bank_eq_self ι G c.stk hG]
  have hr := BitMachineStackRun.run ι G P c t
  rw [hs, h] at hr
  exact hr

/-! ## Guarded sequential composition

The first program's final control is tested once, in the charged handoff
transition. An accepted control resets to the second program's start; a
rejected control halts the whole fixed program there. -/

section Guarded

variable {K LA LB VA VB : Type*} [DecidableEq K]

open BitMachineRawSequence in
def gprogram (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB)
    (ok : VA → Bool) (b₀ : LB) (v₀ : VA) (w₀ : VB) :
    Label LA LB → TM2.Stmt (fun _ : K => Bool) (Label LA LB) (Control VA VB)
  | .inl l => BitMachineInline.stmt leftLabel (fun v => (v, w₀)) Prod.fst
      (some handoff) (A l)
  | .inr (.inl _) => .branch (fun v => ok v.1)
      (.load (fun _ => (v₀, w₀)) (.goto (fun _ => rightLabel b₀))) .halt
  | .inr (.inr l) => BitMachineInline.stmt rightLabel (fun w => (v₀, w))
      Prod.snd none (B l)

open BitMachineRawSequence in
theorem gruns (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (ok : VA → Bool)
    (a₀ : LA) (b₀ : LB) (v₀ v₁ : VA) (w₀ w₁ : VB)
    (S T U : K → List Bool) (ta tb : ℕ)
    (ha : ((advance A)^[ta]) (⟨some a₀, v₀, S⟩ :
      TM2.Cfg (fun _ : K => Bool) LA VA) = ⟨none, v₁, T⟩)
    (hok : ok v₁ = true)
    (hb : ((advance B)^[tb]) (⟨some b₀, w₀, T⟩ :
      TM2.Cfg (fun _ : K => Bool) LB VB) = ⟨none, w₁, U⟩) :
    ∃ t ≤ ta + tb + 1,
      ((advance (gprogram A B ok b₀ v₀ w₀))^[t])
        (⟨some (leftLabel a₀), (v₀, w₀), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
        ⟨none, (v₀, w₁), U⟩ := by
  have hah : (((advance A)^[ta])
      (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA)).l = none := by
    rw [ha]
  have hbh : (((advance B)^[tb])
      (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB)).l = none := by
    rw [hb]
  obtain ⟨a, hat, har⟩ := BitMachineInline.outputs leftLabel (fun v => (v, w₀))
    Prod.fst (fun _ => rfl) (some handoff) A (gprogram A B ok b₀ v₀ w₀)
    (fun _ => rfl) (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) ta hah
  obtain ⟨b, hbt, hbr⟩ := BitMachineInline.outputs rightLabel (fun w => (v₀, w))
    Prod.snd (fun _ => rfl) none B (gprogram A B ok b₀ v₀ w₀) (fun _ => rfl)
    (⟨some b₀, w₀, T⟩ : TM2.Cfg (fun _ : K => Bool) LB VB) tb hbh
  rw [ha] at har
  rw [hb] at hbr
  simp only [BitMachineInline.cfg] at har hbr
  have hh : advance (gprogram A B ok b₀ v₀ w₀)
      (⟨some handoff, (v₁, w₀), T⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨some (rightLabel b₀), (v₀, w₀), T⟩ := by
    simp only [advance, TM2.step, handoff, gprogram, TM2.stepAux, hok,
      cond_true, Option.getD_some]
  refine ⟨a + 1 + b, by omega, ?_⟩
  rw [show a + 1 + b = b + (a + 1) by omega,
    Function.iterate_add_apply, Function.iterate_succ_apply', har, hh]
  exact hbr

open BitMachineRawSequence in
theorem greject (A : LA → TM2.Stmt (fun _ : K => Bool) LA VA)
    (B : LB → TM2.Stmt (fun _ : K => Bool) LB VB) (ok : VA → Bool)
    (a₀ : LA) (b₀ : LB) (v₀ v₁ : VA) (w₀ : VB)
    (S T : K → List Bool) (ta : ℕ)
    (ha : ((advance A)^[ta]) (⟨some a₀, v₀, S⟩ :
      TM2.Cfg (fun _ : K => Bool) LA VA) = ⟨none, v₁, T⟩)
    (hno : ok v₁ = false) :
    ∃ t ≤ ta + 1,
      ((advance (gprogram A B ok b₀ v₀ w₀))^[t])
        (⟨some (leftLabel a₀), (v₀, w₀), S⟩ :
          TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
        ⟨none, (v₁, w₀), T⟩ := by
  have hah : (((advance A)^[ta])
      (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA)).l = none := by
    rw [ha]
  obtain ⟨a, hat, har⟩ := BitMachineInline.outputs leftLabel (fun v => (v, w₀))
    Prod.fst (fun _ => rfl) (some handoff) A (gprogram A B ok b₀ v₀ w₀)
    (fun _ => rfl) (⟨some a₀, v₀, S⟩ : TM2.Cfg (fun _ : K => Bool) LA VA) ta hah
  rw [ha] at har
  simp only [BitMachineInline.cfg] at har
  have hh : advance (gprogram A B ok b₀ v₀ w₀)
      (⟨some handoff, (v₁, w₀), T⟩ :
        TM2.Cfg (fun _ : K => Bool) (Label LA LB) (Control VA VB)) =
      ⟨none, (v₁, w₀), T⟩ := by
    simp only [advance, TM2.step, handoff, gprogram, TM2.stepAux, hno,
      cond_false, Option.getD_some]
  exact ⟨a + 1, by omega, by rw [Function.iterate_succ_apply', har, hh]⟩

end Guarded

/-! ## A standalone physical clear program -/

section Clear

variable {K : Type*} [DecidableEq K]

def clearProgram {n : ℕ} (cells : Fin n → K) :
    Fin (n + 2) → TM2.Stmt (fun _ : K => Bool) (Fin (n + 2)) (Unit × Option Bool) :=
  fun l => if h : l.val < n then
      BitMachineClearBank.clearStep (cells ⟨l.val, h⟩) l ⟨l.val + 1, by omega⟩
    else if l.val = n then
      BitMachineClearBank.finishStep id (Fin.last (n + 1))
    else .halt

theorem clear_run {n : ℕ} (cells : Fin n → K) (hcells : Function.Injective cells)
    (S : K → List Bool) :
    ((advance (clearProgram cells))^[(∑ i, (S (cells i)).length) + n + 2])
      (⟨some 0, ((), none), S⟩ :
        TM2.Cfg (fun _ : K => Bool) (Fin (n + 2)) (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared cells S⟩ := by
  have h := BitMachineClearBank.clear_bank_run (clearProgram cells) id
    (Fin.last (n + 1)) n cells hcells (fun i : Fin (n + 1) => i.castSucc)
    (by
      intro i
      have hi : (i.castSucc.castSucc : Fin (n + 2)).val < n := by simp
      simp only [clearProgram, dif_pos hi]
      congr 1)
    (by
      have hn : ¬ ((Fin.last n).castSucc : Fin (n + 2)).val < n := by simp
      have he : ((Fin.last n).castSucc : Fin (n + 2)).val = n := by simp
      simp only [clearProgram, dif_neg hn, if_pos he])
    () S
  rw [show (∑ i, (S (cells i)).length) + n + 2 =
      1 + ((∑ i, (S (cells i)).length) + n + 1) by omega,
    Function.iterate_add_apply]
  have h0 : ((0 : Fin (n + 1)).castSucc : Fin (n + 2)) = 0 := rfl
  rw [h0] at h
  rw [h]
  have hl : ¬ (Fin.last (n + 1)).val < n := by simp
  have hl' : ¬ (Fin.last (n + 1)).val = n := by simp
  simp [advance, TM2.step, clearProgram, hl, hl', TM2.stepAux]

end Clear

end
end EthInapproximability.CurrentPaper.WeightedRawWords
