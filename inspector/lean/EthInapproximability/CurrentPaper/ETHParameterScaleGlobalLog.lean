import EthInapproximability.CurrentPaper.ETHParameterScaleEdgeCandidate
import EthInapproximability.CurrentPaper.ETHParameterScaleMachineInput

/-! Three disjoint physical logarithm controllers on one fixed bank. The
future six-way maximum sees their actual output cells through an embedding. -/

namespace EthInapproximability.CurrentPaper.ETHScaleGlobalLog

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack := Fin 6 ⊕
  (Fin 13 ⊕ (ETHScaleEdgePreparation.Stack ⊕
    (ETHScaleColumnCandidate.Stack ⊕ ETHScaleColumnCandidate.Stack)))

def raw (j : Fin 6) : Stack := .inl j
def tail (j : Fin 13) : Stack := .inr (.inl j)
def edgePrivate (k : ETHScaleEdgePreparation.Stack) : Stack := .inr (.inr (.inl k))
def columnPrivate (k : ETHScaleColumnCandidate.Stack) : Stack := .inr (.inr (.inr (.inl k)))
def rowPrivate (k : ETHScaleColumnCandidate.Stack) : Stack := .inr (.inr (.inr (.inr k)))

noncomputable def edgeEmbed : ETHScaleEdgePreparation.Stack ↪ Stack where
  toFun k := if k = ETHScaleEdgePreparation.raw then raw 5 else edgePrivate k
  inj' := by
    intro a b h
    by_cases ha : a = ETHScaleEdgePreparation.raw
    · subst a
      by_cases hb : b = ETHScaleEdgePreparation.raw
      · exact hb.symm
      · simp [hb, raw, edgePrivate] at h
    · by_cases hb : b = ETHScaleEdgePreparation.raw
      · subst b
        simp [ha, raw, edgePrivate] at h
      · simpa [ha, hb, edgePrivate] using h

noncomputable def columnEmbed : ETHScaleColumnCandidate.Stack ↪ Stack where
  toFun k := if k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
    then raw 4 else columnPrivate k
  inj' := by
    intro a b h
    by_cases ha : a = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
    · subst a
      by_cases hb : b = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
      · exact hb.symm
      · simp [hb, raw, columnPrivate] at h
    · by_cases hb : b = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
      · subst b
        simp [ha, raw, columnPrivate] at h
      · simpa [ha, hb, columnPrivate] using h

noncomputable def rowEmbed : ETHScaleColumnCandidate.Stack ↪ Stack where
  toFun k := if k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
    then raw 3 else rowPrivate k
  inj' := by
    intro a b h
    by_cases ha : a = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
    · subst a
      by_cases hb : b = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
      · exact hb.symm
      · simp [hb, raw, rowPrivate] at h
    · by_cases hb : b = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
      · subst b
        simp [ha, raw, rowPrivate] at h
      · simpa [ha, hb, rowPrivate] using h

def initial (i : Parameters.Input) : Stack → List Bool
  | .inl k => ETHParameterScaleMachineInput.words i k
  | .inr _ => []

private theorem column_initial_shape (n : ℕ)
    (k : ETHScaleColumnCandidate.Stack) :
    ETHScaleColumnCandidate.initial n k =
      if k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
      then List.replicate n true else [] := by
  classical
  by_cases hk : k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
  · subst k
    simp only [ite_true]
    change bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate n true) [] []).stk
        (ETHParameterScaleMachineLogCopy.copyStack 0) = _
    rw [bank_at]
    rfl
  · rw [if_neg hk]
    cases k with
    | inr x => rfl
    | inl x =>
      change bank ETHParameterScaleMachineLogCopy.copyStack (fun _ => [])
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate n true) [] []).stk x = []
      by_cases hmem : ∃ p : Fin 3, ETHParameterScaleMachineLogCopy.copyStack p = x
      · obtain ⟨p, hp⟩ := hmem
        rw [← hp, bank_at]
        fin_cases p
        all_goals first
          | exact (hk (congrArg Sum.inl (by
              simpa [ETHParameterScaleMachineLogCopy.copyStack] using hp.symm))).elim
          | rfl
      · rw [bank_outside _ _ _ _ hmem]

theorem edgeEmbed_initial (i : Parameters.Input) (k : ETHScaleEdgePreparation.Stack) :
    initial i (edgeEmbed k) = ETHScaleEdgePreparation.initial i.edges k := by
  by_cases hk : k = ETHScaleEdgePreparation.raw
  · subst k
    simp [edgeEmbed, initial, ETHScaleEdgePreparation.initial,
      ETHParameterScaleMachineInput.words, ETHScaleEdgePreparation.raw, raw]
  · change k ≠ (.inl 0 : ETHScaleEdgePreparation.Stack) at hk
    simp [edgeEmbed, hk, initial, ETHScaleEdgePreparation.initial,
      ETHScaleEdgePreparation.raw, raw, edgePrivate]

theorem columnEmbed_initial (i : Parameters.Input) (k : ETHScaleColumnCandidate.Stack) :
    initial i (columnEmbed k) = ETHScaleColumnCandidate.initial i.columns k := by
  rw [column_initial_shape]
  by_cases hk : k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
  · subst k
    simp [columnEmbed, initial, ETHParameterScaleMachineInput.words, raw]
  · simp [columnEmbed, hk, initial, columnPrivate]

theorem rowEmbed_initial (i : Parameters.Input) (k : ETHScaleColumnCandidate.Stack) :
    initial i (rowEmbed k) = ETHScaleColumnCandidate.initial i.rows k := by
  rw [column_initial_shape]
  by_cases hk : k = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
  · subst k
    simp [rowEmbed, initial, ETHParameterScaleMachineInput.words, raw]
  · simp [rowEmbed, hk, initial, rowPrivate]

theorem edge_column_disjoint (a : ETHScaleEdgePreparation.Stack)
    (b : ETHScaleColumnCandidate.Stack) : edgeEmbed a ≠ columnEmbed b := by
  by_cases ha : a = ETHScaleEdgePreparation.raw <;>
    by_cases hb : b = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack) <;>
    simp [edgeEmbed, columnEmbed, ha, hb, raw, edgePrivate, columnPrivate]

theorem edge_row_disjoint (a : ETHScaleEdgePreparation.Stack)
    (b : ETHScaleColumnCandidate.Stack) : edgeEmbed a ≠ rowEmbed b := by
  by_cases ha : a = ETHScaleEdgePreparation.raw <;>
    by_cases hb : b = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack) <;>
    simp [edgeEmbed, rowEmbed, ha, hb, raw, edgePrivate, rowPrivate]

theorem column_row_disjoint (a b : ETHScaleColumnCandidate.Stack) :
    columnEmbed a ≠ rowEmbed b := by
  by_cases ha : a = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack) <;>
    by_cases hb : b = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack) <;>
    simp [columnEmbed, rowEmbed, ha, hb, raw, columnPrivate, rowPrivate]

theorem edge_raw_only (a : ETHScaleEdgePreparation.Stack) (j : Fin 6)
    (h : edgeEmbed a = raw j) : j = 5 := by
  by_cases ha : a = ETHScaleEdgePreparation.raw
  · simpa [edgeEmbed, ha, raw] using h.symm
  · simp [edgeEmbed, ha, raw, edgePrivate] at h

theorem column_raw_only (a : ETHScaleColumnCandidate.Stack) (j : Fin 6)
    (h : columnEmbed a = raw j) : j = 4 := by
  by_cases ha : a = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
  · simpa [columnEmbed, ha, raw] using h.symm
  · simp [columnEmbed, ha, raw, columnPrivate] at h

theorem row_raw_only (a : ETHScaleColumnCandidate.Stack) (j : Fin 6)
    (h : rowEmbed a = raw j) : j = 3 := by
  by_cases ha : a = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack)
  · simpa [rowEmbed, ha, raw] using h.symm
  · simp [rowEmbed, ha, raw, rowPrivate] at h

theorem edge_not_tail (a : ETHScaleEdgePreparation.Stack) (j : Fin 13) :
    edgeEmbed a ≠ tail j := by
  by_cases ha : a = ETHScaleEdgePreparation.raw <;>
    simp [edgeEmbed, ha, raw, edgePrivate, tail]

theorem column_not_tail (a : ETHScaleColumnCandidate.Stack) (j : Fin 13) :
    columnEmbed a ≠ tail j := by
  by_cases ha : a = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack) <;>
    simp [columnEmbed, ha, raw, columnPrivate, tail]

theorem row_not_tail (a : ETHScaleColumnCandidate.Stack) (j : Fin 13) :
    rowEmbed a ≠ tail j := by
  by_cases ha : a = (.inl (.inl 0) : ETHScaleColumnCandidate.Stack) <;>
    simp [rowEmbed, ha, raw, rowPrivate, tail]

noncomputable def edgeOut : Stack :=
  edgeEmbed (ETHScaleEdgePreparation.candidateEmbed (.inr 0))
noncomputable def columnOut : Stack := columnEmbed (.inr 0)
noncomputable def rowOut : Stack := rowEmbed (.inr 0)

noncomputable def edgeControl : ETHScaleEdgePreparation.FullControl :=
  ((none, ()), (ETHParameterScaleMachineLogCopy.copyControl none, none))
noncomputable def columnControl : ETHScaleColumnCandidate.Control :=
  (ETHParameterScaleMachineLogCopy.copyControl none, none)

noncomputable def edgeProgram :=
  fun l => stackStmt edgeEmbed (ETHScaleEdgePreparation.fullProgram l)
noncomputable def columnProgram :=
  fun l => stackStmt columnEmbed (ETHScaleColumnCandidate.program l)
noncomputable def rowProgram :=
  fun l => stackStmt rowEmbed (ETHScaleColumnCandidate.program l)

noncomputable def edgeBound (n : ℕ) :=
  2*n+5 + (ETHScaleColumnCandidate.logCost (n+2) +
    (2*Nat.clog 2 (n+2)+2)+1)+1
noncomputable def simpleBound (n : ℕ) :=
  ETHScaleColumnCandidate.logCost n + (2*Nat.clog 2 n+2)+1

theorem edge_stage (i : Parameters.Input) :
    ∃ t ≤ edgeBound i.edges, ∃ F : Stack → List Bool,
      ((advance edgeProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel .scan)),
          edgeControl, initial i⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            ETHScaleEdgePreparation.FullLabel ETHScaleEdgePreparation.FullControl) =
        ⟨none, edgeControl, F⟩ ∧
      F edgeOut = List.replicate (Nat.clog 2 (i.edges+2)) true ∧
      F (raw 5) = List.replicate i.edges true ∧
      (∀ k, (¬ ∃ x, edgeEmbed x = k) → F k = initial i k) := by
  obtain ⟨t, ht, A, ha, hsource, hout⟩ :=
    ETHScaleEdgePreparation.edge_candidate i.edges
  let F : Stack → List Bool := bank edgeEmbed (initial i) A
  have hbank : bank edgeEmbed (initial i)
      (ETHScaleEdgePreparation.initial i.edges) = initial i :=
    bank_eq_self edgeEmbed (initial i) _
      (fun k => (edgeEmbed_initial i k).symm)
  have h := BitMachineStackRun.run edgeEmbed (initial i)
    ETHScaleEdgePreparation.fullProgram
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel .scan)), edgeControl,
      ETHScaleEdgePreparation.initial i.edges⟩ :
      TM2.Cfg (fun _ : ETHScaleEdgePreparation.Stack => Bool)
        ETHScaleEdgePreparation.FullLabel ETHScaleEdgePreparation.FullControl) t
  have ha' : ((advance ETHScaleEdgePreparation.fullProgram)^[t])
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel .scan)), edgeControl,
        ETHScaleEdgePreparation.initial i.edges⟩ :
        TM2.Cfg (fun _ : ETHScaleEdgePreparation.Stack => Bool)
          ETHScaleEdgePreparation.FullLabel ETHScaleEdgePreparation.FullControl) =
      ⟨none, edgeControl, A⟩ := by
    simpa only [edgeControl] using ha
  rw [show stackCfg edgeEmbed (initial i) _ =
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel .scan)), edgeControl,
        initial i⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ETHScaleEdgePreparation.FullLabel ETHScaleEdgePreparation.FullControl) by
      simp only [stackCfg, hbank], ha'] at h
  refine ⟨t, by simpa only [edgeBound] using ht, F, ?_, ?_, ?_, ?_⟩
  · simpa only [edgeProgram, stackCfg, F] using h
  · exact (bank_at edgeEmbed (initial i) A _).trans hout
  · exact (bank_at edgeEmbed (initial i) A
      ETHScaleEdgePreparation.raw).trans hsource
  · intro k hk
    exact bank_outside edgeEmbed (initial i) A k hk

theorem generic_simple_stage
    (ι : ETHScaleColumnCandidate.Stack ↪ Stack)
    (S : Stack → List Bool) (n : ℕ)
    (hinit : ∀ k, S (ι k) = ETHScaleColumnCandidate.initial n k) :
    ∃ t ≤ simpleBound n, ∃ F : Stack → List Bool,
      ((advance (fun l => stackStmt ι (ETHScaleColumnCandidate.program l)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
          columnControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) =
        ⟨none, columnControl, F⟩ ∧
      F (ι (.inr 0)) = List.replicate (Nat.clog 2 n) true ∧
      F (ι (.inl (.inl 0))) = List.replicate n true ∧
      (∀ k, (¬ ∃ x, ι x = k) → F k = S k) := by
  obtain ⟨t, ht, A, ha, hout, hsource⟩ :=
    ETHScaleColumnCandidate.column_candidate n
  let F : Stack → List Bool := bank ι S A
  have hbank : bank ι S (ETHScaleColumnCandidate.initial n) = S :=
    bank_eq_self ι S _ (fun k => (hinit k).symm)
  have h := BitMachineStackRun.run ι S ETHScaleColumnCandidate.program
    (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
      columnControl, ETHScaleColumnCandidate.initial n⟩ :
      TM2.Cfg (fun _ : ETHScaleColumnCandidate.Stack => Bool)
        ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) t
  have ha' : ((advance ETHScaleColumnCandidate.program)^[t])
      (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
        columnControl, ETHScaleColumnCandidate.initial n⟩ :
        TM2.Cfg (fun _ : ETHScaleColumnCandidate.Stack => Bool)
          ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) =
      ⟨none, columnControl, A⟩ := by
    simpa only [columnControl] using ha
  rw [show stackCfg ι S _ =
      (⟨some (BitMachineRawSequence.leftLabel (.inl .scan)),
        columnControl, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          ETHScaleColumnCandidate.Label ETHScaleColumnCandidate.Control) by
      simp only [stackCfg, hbank], ha'] at h
  refine ⟨t, by simpa only [simpleBound] using ht, F, ?_, ?_, ?_, ?_⟩
  · simpa only [stackCfg, F] using h
  · exact (bank_at ι S A _).trans hout
  · exact (bank_at ι S A _).trans hsource
  · intro k hk
    exact bank_outside ι S A k hk

noncomputable def firstProgram :=
  BitMachineRawSequence.program edgeProgram columnProgram
    (BitMachineRawSequence.leftLabel (.inl .scan))
    edgeControl columnControl

noncomputable def threeProgram :=
  BitMachineRawSequence.program firstProgram rowProgram
    (BitMachineRawSequence.leftLabel (.inl .scan))
    (edgeControl, columnControl) columnControl

noncomputable def threeBound (i : Parameters.Input) :=
  edgeBound i.edges + simpleBound i.columns + 1 +
    simpleBound i.rows + 1

theorem three_log_run (i : Parameters.Input) :
    ∃ t ≤ threeBound i, ∃ F : Stack → List Bool,
      ((advance threeProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel .scan)))),
          ((edgeControl, columnControl), columnControl), initial i⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                ETHScaleEdgePreparation.FullLabel ETHScaleColumnCandidate.Label)
              ETHScaleColumnCandidate.Label)
            ((ETHScaleEdgePreparation.FullControl × ETHScaleColumnCandidate.Control) ×
              ETHScaleColumnCandidate.Control)) =
        ⟨none, ((edgeControl, columnControl), columnControl), F⟩ ∧
      F edgeOut = List.replicate (Nat.clog 2 (i.edges+2)) true ∧
      F columnOut = List.replicate (Nat.clog 2 i.columns) true ∧
      F rowOut = List.replicate (Nat.clog 2 i.rows) true ∧
      (∀ j : Fin 6, F (raw j) = ETHParameterScaleMachineInput.words i j) ∧
      (∀ j : Fin 13, F (tail j) = []) := by
  obtain ⟨te, hte, S1, he, heout, heraw, heframe⟩ := edge_stage i
  have hcolInit : ∀ k, S1 (columnEmbed k) =
      ETHScaleColumnCandidate.initial i.columns k := by
    intro k
    rw [heframe (columnEmbed k) (by
      rintro ⟨x, hx⟩
      exact edge_column_disjoint x k hx)]
    exact columnEmbed_initial i k
  obtain ⟨tc, htc, S2, hc, hcout, hcraw, hcframe⟩ :=
    generic_simple_stage columnEmbed S1 i.columns hcolInit
  have hrowInit : ∀ k, S2 (rowEmbed k) =
      ETHScaleColumnCandidate.initial i.rows k := by
    intro k
    rw [hcframe (rowEmbed k) (by
      rintro ⟨x, hx⟩
      exact column_row_disjoint x k hx)]
    rw [heframe (rowEmbed k) (by
      rintro ⟨x, hx⟩
      exact edge_row_disjoint x k hx)]
    exact rowEmbed_initial i k
  obtain ⟨tr, htr, S3, hr, hrout, hrraw, hrframe⟩ :=
    generic_simple_stage rowEmbed S2 i.rows hrowInit
  obtain ⟨tfirst, htfirst, hfirst⟩ := BitMachineRawSequence.runs
    edgeProgram columnProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel .scan))
    (BitMachineRawSequence.leftLabel (.inl .scan))
    edgeControl edgeControl columnControl columnControl
    (initial i) S1 S2 te tc he hc
  obtain ⟨t, ht, htotal⟩ := BitMachineRawSequence.runs
    firstProgram rowProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel .scan)))
    (BitMachineRawSequence.leftLabel (.inl .scan))
    (edgeControl, columnControl) (edgeControl, columnControl)
    columnControl columnControl
    (initial i) S2 S3 tfirst tr hfirst hr
  refine ⟨t, by unfold threeBound; omega, S3,
    by simpa only [threeProgram] using htotal, ?_, ?_, hrout, ?_, ?_⟩
  · calc
      S3 edgeOut = S2 edgeOut := hrframe edgeOut (by
        rintro ⟨k, hk⟩
        exact (edge_row_disjoint
          (ETHScaleEdgePreparation.candidateEmbed (.inr 0)) k) hk.symm)
      _ = S1 edgeOut := hcframe edgeOut (by
        rintro ⟨k, hk⟩
        exact (edge_column_disjoint
          (ETHScaleEdgePreparation.candidateEmbed (.inr 0)) k) hk.symm)
      _ = _ := heout
  · calc
      S3 columnOut = S2 columnOut := hrframe columnOut (by
        rintro ⟨k, hk⟩
        exact (column_row_disjoint (.inr 0) k) hk.symm)
      _ = _ := hcout
  · intro j
    by_cases hj3 : j = 3
    · subst j
      simpa [rowEmbed, raw, ETHParameterScaleMachineInput.words] using hrraw
    by_cases hj4 : j = 4
    · subst j
      have hf : S3 (raw 4) = S2 (raw 4) := hrframe _ (by
        rintro ⟨k, hk⟩
        exact hj3 (row_raw_only k 4 hk))
      rw [hf]
      simpa [columnEmbed, raw, ETHParameterScaleMachineInput.words] using hcraw
    by_cases hj5 : j = 5
    · subst j
      have hf3 : S3 (raw 5) = S2 (raw 5) := hrframe _ (by
        rintro ⟨k, hk⟩
        exact hj3 (row_raw_only k 5 hk))
      have hf4 : S2 (raw 5) = S1 (raw 5) := hcframe _ (by
        rintro ⟨k, hk⟩
        exact hj4 (column_raw_only k 5 hk))
      rw [hf3, hf4]
      simpa [ETHParameterScaleMachineInput.words] using heraw
    calc
      S3 (raw j) = S2 (raw j) := hrframe _ (by
        rintro ⟨k, hk⟩
        exact hj3 (row_raw_only k j hk))
      _ = S1 (raw j) := hcframe _ (by
        rintro ⟨k, hk⟩
        exact hj4 (column_raw_only k j hk))
      _ = initial i (raw j) := heframe _ (by
        rintro ⟨k, hk⟩
        exact hj5 (edge_raw_only k j hk))
      _ = ETHParameterScaleMachineInput.words i j := rfl
  · intro j
    calc
      S3 (tail j) = S2 (tail j) := hrframe _ (by
        rintro ⟨k, hk⟩
        exact row_not_tail k j hk)
      _ = S1 (tail j) := hcframe _ (by
        rintro ⟨k, hk⟩
        exact column_not_tail k j hk)
      _ = initial i (tail j) := heframe _ (by
        rintro ⟨k, hk⟩
        exact edge_not_tail k j hk)
      _ = [] := rfl

end EthInapproximability.CurrentPaper.ETHScaleGlobalLog
