import EthInapproximability.CurrentPaper.SourceGenericCompositeTop

/-!
# Accepted raw source facts at an arbitrary fixed alphabet

Paper B, locked v8 Section 6 and Appendix B; CP-SOURCE-EFFECTIVE.
Generic-alphabet forms of the (binary-stated) facts in
`SourceCSPEntryBound.raw_accepted_source` and `physical_first_rest`, derived
only from an actual accepting run of the fixed global validator. The proofs
use the admitted generic `SourceCSPTotalSelectiveScratch.raw_total_selective`,
`SourceCSPAcceptedCount.raw_accepted_count_at` and
`RawCanonicalReadback.successful_rows_literal`; no `a = 2` is used.
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.AcceptedSource

open Turing BitMachineEncoding
open scoped Classical

/-- Everything the converter needs from an actual accepting validator halt:
typed header/rows, the literal row suffix, the retained cap and count cells,
and a run of the same halt within the validator's total bound. -/
theorem raw_accepted_source (a q : Nat) (input : List Bool) (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩) :
    ∃ (tb n m : Nat) (suffix : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n a q),
      tb ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tb])
        (SourceCSPGlobalDecisionProgram.initial a q input) =
          ⟨none, .row (vr, some true), S⟩ ∧
      0 < n ∧ 0 < m ∧ n ≤ q * m ∧ m ≤ input.length ∧
      input = SourceCSPHeaderParse.header n m a q ++ suffix ∧
      SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
        some (rows, []) ∧
      S SourceCSPGlobalDecisionProgram.savedSource = suffix ∧
      S SourceCSPHeaderRowBridge.capSource =
        List.replicate (n - 1) true ∧
      S SourceCSPHeaderRowBridge.count = List.replicate m true := by
  obtain ⟨tg', htg', c, S', hglobal, ts, _, d, W, _hselect, hcase⟩ :=
    SourceCSPTotalSelectiveScratch.raw_total_selective a q input
  have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input)
    tg' tg (by rw [hglobal]) (by rw [hacc])
  have hc : c = .row (vr, some true) := by
    have h := congrArg (fun z => z.var) heq
    simpa only [hglobal, hacc] using h
  have hS : S' = S := by
    have h := congrArg (fun z => z.stk) heq
    simpa only [hglobal, hacc] using h
  rcases hcase with hreje | hzero | hgood
  · have hf := hreje.1
    rw [hc] at hf
    contradiction
  · have hf := hzero.1
    rw [hc] at hf
    cases hf
  · obtain ⟨n, m, suffix, rows, vr', _hc', _, hinput,
      hn, hsize, hmL, hread, hsaved, hcap, _⟩ := hgood
    have hm : 0 < m := by
      by_contra hnot
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnot
      subst m
      simp at hsize
      omega
    subst S'
    subst c
    refine ⟨tg', n, m, suffix, rows, htg', hglobal, hn, hm, hsize, hmL,
      hinput, hread, hsaved, hcap, ?_⟩
    exact SourceCSPAcceptedCount.raw_accepted_count_at a q n m
      input suffix hinput tg vr S hacc

/-- The first-row parser's unread word is the canonical field list of rows
`1..m-1` (generic `SourceGenericAllRowLoop.remainingRows`). -/
theorem physical_first_rest {n m a q : Nat}
    (hm : 0 < m) (suffix rest : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, []))
    (hfirst : suffix =
      SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest) :
    rest = SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (SourceGenericAllRowLoop.remainingRows rows 0 (m - 1)
        (by omega)) := by
  have hcanonical := RawCanonicalReadback.successful_rows_literal
    suffix rows hread
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  subst m
  rw [SourceCSPCodec.fnFields_succ] at hcanonical
  rw [hfirst] at hcanonical
  have htail : rest = SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin k => rows j.succ) :=
    List.append_cancel_left hcanonical
  convert htail using 1
  congr 1
  funext j
  apply congrArg rows
  apply Fin.ext
  change 0 + 1 + j.val = j.succ.val
  simp only [Fin.val_succ]
  omega

theorem rows_query_width {n m a q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q) :
    ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ n := by
  intro i j
  have hb := UnaryBinaryEncoding.bits_length_le ((rows i).1 j).val
  have hl := ((rows i).1 j).isLt
  omega

theorem initial_length_le (a q : Nat) (input : List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    ((SourceCSPGlobalDecisionProgram.initial a q input).stk g).length ≤
      input.length := by
  have h := SourceCSPEntryBound.first_initial_length_le q input (.inl g)
  have e1 := SourceCSPSecondPassGlobalLift.initial_left 2 q input g
  have e2 : (SourceCSPGlobalDecisionProgram.initial a q input).stk g =
      (SourceCSPGlobalDecisionProgram.initial 2 q input).stk g := rfl
  rw [e2, ← e1]
  exact h

/-- Word envelope for every validator cell and every staged first-row cell,
as a fixed-`(a,q)` function of the raw input length. -/
noncomputable def envelope (a q L : Nat) : Nat :=
  L + BitMachineStackGrowth.perStep (SourceCSPGlobalDecisionProgram.program a q) *
      (SourceCSPGlobalTotalValidation.totalBound a q L + 1) +
    BitMachineStackGrowth.perStep (SourceCSPFirstRowController.bodyProgram q a) *
      (SourceCSPFirstRowController.uniformStageBound q L +
        SourceCSPFirstRowController.uniformRowBound a q L + 1)

theorem global_cells_le (a q : Nat) (input : List Bool) (tb : Nat)
    (c : SourceCSPGlobalDecisionProgram.Control a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (htb : tb ≤ SourceCSPGlobalTotalValidation.totalBound a q input.length + 1)
    (hrun : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tb])
      (SourceCSPGlobalDecisionProgram.initial a q input) = ⟨none, c, S⟩) :
    ∀ g, (S g).length ≤
      input.length + BitMachineStackGrowth.perStep
        (SourceCSPGlobalDecisionProgram.program a q) *
          (SourceCSPGlobalTotalValidation.totalBound a q input.length + 1) := by
  intro g
  have hg := BitMachineStackGrowth.run_growth
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input) tb g
  rw [hrun] at hg
  have hi := initial_length_le a q input g
  have hm := Nat.mul_le_mul_left
    (BitMachineStackGrowth.perStep (SourceCSPGlobalDecisionProgram.program a q)) htb
  change (S g).length ≤ _ at hg
  omega

theorem stage_cells_le (a q : Nat) (X Y tb : Nat)
    (B F : SourceCSPFirstRowController.Stack q → List Bool)
    (v : SourceCSPFirstRowController.BodyControl)
    (hB : ∀ x, (B x).length ≤ X) (htb : tb ≤ Y)
    (hrun : ((advance (SourceCSPFirstRowController.bodyProgram q a))^[tb])
      (⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
        SourceCSPFirstRowController.bodyInitial, B⟩ :
        TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
          (SourceCSPFirstRowController.BodyLabel q a)
          SourceCSPFirstRowController.BodyControl) = ⟨none, v, F⟩) :
    ∀ x, (F x).length ≤
      X + BitMachineStackGrowth.perStep
        (SourceCSPFirstRowController.bodyProgram q a) * Y := by
  intro x
  have hg := BitMachineStackGrowth.run_growth
    (SourceCSPFirstRowController.bodyProgram q a)
    (⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
      SourceCSPFirstRowController.bodyInitial, B⟩ :
      TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
        (SourceCSPFirstRowController.BodyLabel q a)
        SourceCSPFirstRowController.BodyControl) tb x
  rw [hrun] at hg
  have hi := hB x
  have hm := Nat.mul_le_mul_left
    (BitMachineStackGrowth.perStep (SourceCSPFirstRowController.bodyProgram q a)) htb
  have hg' : (F x).length ≤ (B x).length +
      BitMachineStackGrowth.perStep
        (SourceCSPFirstRowController.bodyProgram q a) * tb := hg
  omega

#print axioms raw_accepted_source
#print axioms physical_first_rest
#print axioms rows_query_width
#print axioms initial_length_le
#print axioms global_cells_le
#print axioms stage_cells_le

end EthInapproximability.CurrentPaper.SourceGenericComposite.AcceptedSource
