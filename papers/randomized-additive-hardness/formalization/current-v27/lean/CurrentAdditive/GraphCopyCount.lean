import CurrentAdditive.GraphCopyMachineStages
import EthInapproximability.CurrentPaper.SourceNormalizationMachineDoubleUnary

/-! Selected v39 sources.tex:69-78. A physical one-token adjustment enters
the existing divider at the actual ceiling formula; a second physical scan
produces the endpoint-field counter. Neither counter is supplied to start. -/

namespace Paper2.CurrentAdditive.GraphCopyCount

open EthInapproximability.CurrentPaper Turing TM2.Stmt BitMachineEncoding
open Paper2.CurrentAdditive.GraphCopyPadding
open Paper2.CurrentAdditive.GraphCopyMachineStages

abbrev Stack := SourceNormalizationMachineCounts.Stack ⊕ Fin 1
abbrev Label := SourceNormalizationMachineCounts.Label ⊕
  (SourceNormalizationMachineDoubleUnary.Phase ⊕ Unit)
abbrev Control := SourceNormalizationMachineCounts.Control × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def countStack : SourceNormalizationMachineCounts.Stack ↪ Stack :=
  ⟨Sum.inl, Sum.inl_injective⟩

def doubleStack : SourceNormalizationMachineDoubleUnary.Stack ↪ Stack where
  toFun k := match k.val with
    | 0 => .inl (.inl 1)
    | 1 => .inl (.inl 2)
    | _ => .inr 0
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def countControl (v : SourceNormalizationMachineCounts.Control) : Control := (v, none)
def doubleControl (v : Option Bool) : Control := ((false, ()), v)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineStackEmbedding.stmt countStack Sum.inl countControl Prod.fst
      (some (.inr (.inl .scan))) (SourceNormalizationMachineCounts.program l)
  | .inr (.inl l) => BitMachineStackEmbedding.stmt doubleStack
      (fun l => .inr (.inl l)) doubleControl Prod.snd none
      (SourceNormalizationMachineDoubleUnary.program l)
  | .inr (.inr _) => pop (.inl (.inr 1)) (fun _ _ => countControl (false, ()))
      (goto (fun _ => .inl (.inr .copyN)))

def run (t : ℕ) (c : Config) := ((advance program)^[t]) c

private theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def countInitial (N m : ℕ) (payload : List Bool) : SourceNormalizationMachineCounts.Config :=
  SourceNormalizationMachineCounts.cfg (some (.inr .copyN)) false
    [] [] [] [] [] [] (List.replicate N true) (List.replicate (m - 1) true) payload

def countFinal (N m : ℕ) (payload : List Bool) : SourceNormalizationMachineCounts.Config :=
  SourceNormalizationMachineCounts.cfg none false [] (List.replicate m true) []
    (List.replicate ((N + (m - 1)) % m) true)
    (List.replicate (copies N m) true) []
    (List.replicate N true) (List.replicate (m - 1) true) payload

def start (N m : ℕ) (payload : List Bool) : Config :=
  ⟨some (.inr (.inr ())), countControl (false, ()),
    Sum.elim
      (SourceNormalizationMachineCounts.cfg none false [] [] [] [] [] []
        (List.replicate N true) (List.replicate m true) payload).stk
      (fun _ => [])⟩

noncomputable def afterPrepare (N m : ℕ) (payload : List Bool) : Config :=
  BitMachineStackEmbedding.cfg countStack (start N m payload).stk Sum.inl countControl
    (some (.inr (.inl .scan))) (countInitial N m payload)

theorem prepare_step (N m : ℕ) (hm : 0 < m) (payload : List Bool) :
    run 1 (start N m payload) = afterPrepare N m payload := by
  have hb := BitMachineStackEmbedding.bank_eq_self countStack
    ((advance program) (start N m payload)).stk (countInitial N m payload).stk (by
      intro k
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k =>
          fin_cases k
          · rfl
          · cases m with
            | zero => omega
            | succ m => rfl
          · rfl)
  have hout : (advance program (start N m payload)).stk =
      BitMachineStackEmbedding.bank countStack (start N m payload).stk
        (countInitial N m payload).stk := by
    funext k
    cases k with
    | inl k =>
        rw [show Sum.inl k = countStack k from rfl, BitMachineStackEmbedding.bank_at]
        exact (congrFun hb (countStack k)).symm.trans
          (BitMachineStackEmbedding.bank_at _ _ _ _)
    | inr k =>
        rw [BitMachineStackEmbedding.bank_outside countStack _ _ _ (by simp [countStack])]
        fin_cases k
        rfl
  change (⟨some (.inl (.inr .copyN)), countControl (false, ()),
    (advance program (start N m payload)).stk⟩ : Config) =
    ⟨some (.inl (.inr .copyN)), countControl (false, ()),
      BitMachineStackEmbedding.bank countStack (start N m payload).stk
        (countInitial N m payload).stk⟩
  rw [hout]

noncomputable def afterCount (N m : ℕ) (payload : List Bool) : Config :=
  BitMachineStackEmbedding.cfg countStack (start N m payload).stk Sum.inl countControl
    (some (.inr (.inl .scan))) (countFinal N m payload)

theorem count_stage (N m : ℕ) (hm : 0 < m) (payload : List Bool) :
    ∃ t ≤ 1 + (10 * N + 13 * (m - 1) + 13),
      run t (start N m payload) = afterCount N m payload := by
  obtain ⟨a, ha, hr⟩ := physical_count_run N m hm payload
  have hr' : SourceNormalizationMachineCounts.run a (countInitial N m payload) =
      countFinal N m payload := hr
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs countStack
    (start N m payload).stk Sum.inl countControl Prod.fst (by intro v; rfl)
    (some (.inr (.inl .scan))) SourceNormalizationMachineCounts.program program
    (by intro l; rfl) (countInitial N m payload) a (by
      change (SourceNormalizationMachineCounts.run _ _).l = none
      rw [hr']; rfl)
  change ((advance SourceNormalizationMachineCounts.program)^[a]) _ = _ at hr'
  rw [hr'] at he
  exact ⟨1 + t, by omega, (run_add (prepare_step N m hm payload) t).trans he⟩

@[simp] theorem afterCount_at (N m : ℕ) (payload : List Bool)
    (k : SourceNormalizationMachineCounts.Stack) :
    (afterCount N m payload).stk (.inl k) = (countFinal N m payload).stk k :=
  BitMachineStackEmbedding.bank_at countStack _ _ k

@[simp] theorem afterCount_extra (N m : ℕ) (payload : List Bool) :
    (afterCount N m payload).stk (.inr 0) = [] := by
  rw [show (afterCount N m payload).stk (.inr 0) = (start N m payload).stk (.inr 0) from
    BitMachineStackEmbedding.bank_outside countStack _ _ _ (by simp [countStack])]
  rfl

def doubleInitial (m : ℕ) : SourceNormalizationMachineDoubleUnary.Config :=
  SourceNormalizationMachineDoubleUnary.cfg (some .scan) none (List.replicate m true) [] []

def doubleFinal (m : ℕ) : SourceNormalizationMachineDoubleUnary.Config :=
  SourceNormalizationMachineDoubleUnary.cfg none none
    (List.replicate m true) [] (List.replicate (2 * m) true)

private theorem double_initial (N m : ℕ) (payload : List Bool) :
    afterCount N m payload = BitMachineStackEmbedding.cfg doubleStack
      (afterCount N m payload).stk (fun l => .inr (.inl l)) doubleControl none (doubleInitial m) := by
  have hb := BitMachineStackEmbedding.bank_eq_self doubleStack (afterCount N m payload).stk
    (doubleInitial m).stk (by
      intro k
      fin_cases k <;> simp [doubleStack, doubleInitial,
        SourceNormalizationMachineDoubleUnary.cfg, countFinal, SourceNormalizationMachineCounts.cfg])
  change (⟨some (.inr (.inl .scan)), doubleControl none, (afterCount N m payload).stk⟩ : Config) =
    ⟨some (.inr (.inl .scan)), doubleControl none,
      BitMachineStackEmbedding.bank doubleStack (afterCount N m payload).stk (doubleInitial m).stk⟩
  rw [hb]

noncomputable def finalHost (N m : ℕ) (payload : List Bool) : Config :=
  BitMachineStackEmbedding.cfg doubleStack (afterCount N m payload).stk
    (fun l => .inr (.inl l)) doubleControl none (doubleFinal m)

theorem preparation_run (N m : ℕ) (hm : 0 < m) (payload : List Bool) :
    ∃ t ≤ 10 * N + 15 * m + 16, run t (start N m payload) = finalHost N m payload := by
  obtain ⟨a, ha, hra⟩ := count_stage N m hm payload
  have hrd : SourceNormalizationMachineDoubleUnary.run (2 * m + 2)
      (doubleInitial m) = doubleFinal m := SourceNormalizationMachineDoubleUnary.double_run m
  obtain ⟨b, hb, hrb⟩ := BitMachineStackEmbedding.outputs doubleStack
    (afterCount N m payload).stk (fun l => .inr (.inl l)) doubleControl Prod.snd
    (by intro v; rfl) none SourceNormalizationMachineDoubleUnary.program program
    (by intro l; rfl) (doubleInitial m) (2 * m + 2) (by
      change (SourceNormalizationMachineDoubleUnary.run _ _).l = none
      rw [hrd]; rfl)
  change ((advance SourceNormalizationMachineDoubleUnary.program)^[2 * m + 2]) _ = _ at hrd
  rw [hrd] at hrb
  exact ⟨a + b, by omega, (run_add hra b).trans
    ((congrArg (run b) (double_initial N m payload)).trans hrb)⟩

def copiesStack : Stack := .inl (.inl 4)
def payloadStack : Stack := .inl (.inr 2)
def originalNStack : Stack := .inl (.inr 0)
def fieldCountStack : Stack := .inr 0

theorem final_fields (N m : ℕ) (payload : List Bool) :
    (finalHost N m payload).stk fieldCountStack = List.replicate (2 * m) true := by
  change BitMachineStackEmbedding.bank doubleStack _ _ (doubleStack 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  rfl

private theorem final_outside (N m : ℕ) (payload : List Bool) (j : Stack)
    (hj : ¬ ∃ k, doubleStack k = j) :
    (finalHost N m payload).stk j = (afterCount N m payload).stk j :=
  BitMachineStackEmbedding.bank_outside doubleStack _ _ j hj

theorem final_copies (N m : ℕ) (payload : List Bool) :
    (finalHost N m payload).stk copiesStack = List.replicate (copies N m) true := by
  have hn : ¬ ∃ k, doubleStack k = copiesStack := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [doubleStack, copiesStack] at hk
  rw [final_outside N m payload _ hn]
  change (afterCount N m payload).stk (.inl (.inl 4)) = _
  rw [afterCount_at]
  rfl

theorem final_payload (N m : ℕ) (payload : List Bool) :
    (finalHost N m payload).stk payloadStack = payload := by
  have hn : ¬ ∃ k, doubleStack k = payloadStack := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [doubleStack, payloadStack] at hk
  rw [final_outside N m payload _ hn]
  change (afterCount N m payload).stk (.inl (.inr 2)) = _
  rw [afterCount_at]
  rfl

theorem final_originalN (N m : ℕ) (payload : List Bool) :
    (finalHost N m payload).stk originalNStack = List.replicate N true := by
  have hn : ¬ ∃ k, doubleStack k = originalNStack := by
    rintro ⟨k, hk⟩
    fin_cases k <;> simp [doubleStack, originalNStack] at hk
  rw [final_outside N m payload _ hn]
  change (afterCount N m payload).stk (.inl (.inr 0)) = _
  rw [afterCount_at]
  rfl

#print axioms preparation_run
#print axioms final_fields
#print axioms final_copies

end Paper2.CurrentAdditive.GraphCopyCount
