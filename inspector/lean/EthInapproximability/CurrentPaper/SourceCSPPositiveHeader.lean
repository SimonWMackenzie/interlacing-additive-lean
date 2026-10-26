import EthInapproximability.CurrentPaper.SourceCSPBudgetFrame
import EthInapproximability.CurrentPaper.SourceCSPGuardedCodec

/-!
# Encoded input through the positive-vertex query cap

The physical raw-length/header/constraint-count controller is framed in the
larger budget bank, then sequentially composed with the status peel,
fixed-q multiplication, and positive-vertex cap controller. This file still
stops before the row loop and clause stream.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPPositiveHeader

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPBudgetFrame.Stack

def initial (input : List Bool) : Stack → List Bool
  | .inl k => SourceCSPInputFrame.initial input k
  | .inr _ => []

def headerProgram (a q : Nat) (l : BitMachineRawSequence.Label
    (SourceCSPConstraintGuard.HeaderLabel a q)
    SourceCSPQueryRange.Label) :=
  stmt SourceCSPBudgetFrame.inputEmbedding id id id none
    (SourceCSPConstraintGuard.guardedProgram a q l)

def fullHeaderProgram (a q : Nat) :=
  BitMachineRawSequence.program (headerProgram a q)
    (SourceCSPBudgetFrame.positiveCapProgram q)
    (.inl (.inl ()) : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
      SourceCSPVertexCap.Label)
    (((((none, none), (((none, none), none), none)),
      ((none, none), (none, false))) :
        SourceCSPConstraintGuard.HeaderControl × SourceCSPQueryRange.Control))
    (((none, none), (((none, none), (none, false)), none)) :
      (Option Bool × Option Bool) × SourceCSPVertexCap.Control)

def rows {a q : Nat} (P : EncodedETHSource.ConstraintInstance a q) : List Bool :=
  SourceCSPCodec.fnFields SourceCSPCodec.rowFields (SourceCSPCodec.rowsOf P)

def headerBound (a q L B : Nat) : Nat :=
  3 * L + 4 + 4 * (2 * L + 4) + 3 +
    (a.bits.length + 1) + (q.bits.length + 1) + 3 +
    (2 * B + 2 + (2 * L + 2) + 1 +
      (L + 1) * (4 * B + 5) + 1) + 1

theorem encoded_guarded {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q) :
    ∃ (t : Nat) (c : SourceCSPConstraintGuard.GuardedConfig a q),
      t ≤ headerBound a q (EncodedETHSource.constraintBits P).length
        P.constraints.bits.length ∧
      ((advance (SourceCSPConstraintGuard.guardedProgram a q))^[t])
        (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
          ((((none, none), (((none, none), none), none))),
            ((none, none), (none, false))),
          SourceCSPInputFrame.initial (EncodedETHSource.constraintBits P)⟩ :
          SourceCSPConstraintGuard.GuardedConfig a q) = c ∧
      c.l = none ∧
      c.stk (.inl (.inl (.inl 0))) = P.vertices.bits ∧
      c.stk (.inl (.inl (.inl 1))) = P.constraints.bits ∧
      c.stk (.inl (.inl (.inr 0))) = rows P ∧
      c.stk (.inr 6) = true :: List.replicate P.constraints true := by
  obtain ⟨t, c, ht, hr, hh, hn, hm, hrest, hout⟩ :=
    SourceCSPConstraintGuard.canonical_guarded_header
      P.vertices P.constraints a q (rows P)
  have heq : EncodedETHSource.constraintBits P =
      SourceCSPHeaderParse.header P.vertices P.constraints a q ++ rows P :=
    SourceCSPGuardedCodec.input_eq_header_rows P
  rw [← heq] at ht hr hout
  refine ⟨t, c, ?_, hr, hh, hn, hm, hrest, ?_⟩
  · simpa only [headerBound] using ht
  · rw [hout]
    exact SourceCSPGuardedCodec.guard_result_exact P

theorem framed_encoded_guard {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q) :
    ∃ t v S, t ≤ headerBound a q (EncodedETHSource.constraintBits P).length
        P.constraints.bits.length ∧
      ((advance (headerProgram a q))^[t])
        (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
          ((((none, none), (((none, none), none), none))),
            ((none, none), (none, false))),
          initial (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPConstraintGuard.HeaderLabel a q)
              SourceCSPQueryRange.Label)
            (SourceCSPConstraintGuard.HeaderControl ×
              SourceCSPQueryRange.Control)) = ⟨none, v, S⟩ ∧
      S (.inl (.inl (.inl (.inl 0)))) = P.vertices.bits ∧
      S (.inl (.inr 6)) = true :: List.replicate P.constraints true ∧
      S (.inl (.inl (.inl (.inr 0)))) = rows P ∧
      (∀ k : Fin 7, S (.inr k) = []) := by
  let input := EncodedETHSource.constraintBits P
  obtain ⟨t, c, ht, hr, hh, hn, _, hrest, hout⟩ := encoded_guarded P
  have hhalt : (((advance (SourceCSPConstraintGuard.guardedProgram a q))^[t])
      (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
        ((((none, none), (((none, none), none), none))),
          ((none, none), (none, false))),
        SourceCSPInputFrame.initial input⟩ :
        SourceCSPConstraintGuard.GuardedConfig a q)).l = none := by
    rw [hr]
    exact hh
  obtain ⟨u, hu, hrun⟩ := outputs SourceCSPBudgetFrame.inputEmbedding
    (initial input) id id id (fun _ => rfl) none
    (SourceCSPConstraintGuard.guardedProgram a q) (headerProgram a q)
    (fun _ => rfl)
    (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
      ((((none, none), (((none, none), none), none))),
        ((none, none), (none, false))),
      SourceCSPInputFrame.initial input⟩ :
      SourceCSPConstraintGuard.GuardedConfig a q) t hhalt
  have hstart : cfg SourceCSPBudgetFrame.inputEmbedding (initial input)
      id id none
      (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
        ((((none, none), (((none, none), none), none))),
          ((none, none), (none, false))),
        SourceCSPInputFrame.initial input⟩ :
        SourceCSPConstraintGuard.GuardedConfig a q) =
      (⟨some (.inl (.inl (.inl BitMachineCopy.Label.scan))),
        ((((none, none), (((none, none), none), none))),
          ((none, none), (none, false))),
        initial input⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label
            (SourceCSPConstraintGuard.HeaderLabel a q)
            SourceCSPQueryRange.Label)
          (SourceCSPConstraintGuard.HeaderControl ×
            SourceCSPQueryRange.Control)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  rw [hr, hstart] at hrun
  let S := bank SourceCSPBudgetFrame.inputEmbedding (initial input) c.stk
  refine ⟨u, c.var, S, hu.trans ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, cfg, stackCfg, BitMachineInline.cfg,
      id_eq, hh, Option.map_none] using hrun
  · change bank SourceCSPBudgetFrame.inputEmbedding _ _
      (SourceCSPBudgetFrame.inputEmbedding (.inl (.inl (.inl 0)))) = _
    rw [bank_at]
    exact hn
  · change bank SourceCSPBudgetFrame.inputEmbedding _ _
      (SourceCSPBudgetFrame.inputEmbedding (.inr 6)) = _
    rw [bank_at]
    exact hout
  · change bank SourceCSPBudgetFrame.inputEmbedding _ _
      (SourceCSPBudgetFrame.inputEmbedding (.inl (.inl (.inr 0)))) = _
    rw [bank_at]
    exact hrest
  · intro k
    change bank SourceCSPBudgetFrame.inputEmbedding (initial input) c.stk
      (.inr k) = []
    rw [bank_outside]
    · rfl
    · rintro ⟨j, hj⟩
      cases hj

def positiveBound (a q L B n m : Nat) : Nat :=
  headerBound a q L B +
    (q * (2 * m + 3) + 3 +
      (2 * n.bits.length + 2 + (2 * (q * m) + 2) + 1 +
        (q * m + 1) * (4 * n.bits.length + 5) + 3) + 1) + 1

/-- One actual finite program carries a valid positive-vertex encoded CSP
through raw input counting, header checks, bounded `m`, fixed-q budget and
positive vertex cap. This is still upstream of row parsing and clauses. -/
theorem encoded_positive_cap {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hn : 0 < P.vertices) (hsize : SourceCSPCodec.ValidSize P) :
    ∃ t v S,
      t ≤ positiveBound a q (EncodedETHSource.constraintBits P).length
        P.constraints.bits.length P.vertices P.constraints ∧
      ((advance (fullHeaderProgram a q))^[t])
        (⟨some (.inl (.inl (.inl (.inl BitMachineCopy.Label.scan)))),
          (((((none, none), (((none, none), none), none)),
            ((none, none), (none, false)))),
            ((none, none), (((none, none), (none, false)), none))),
          initial (EncodedETHSource.constraintBits P)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label
                (SourceCSPConstraintGuard.HeaderLabel a q)
                SourceCSPQueryRange.Label)
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
                SourceCSPVertexCap.Label))
            ((SourceCSPConstraintGuard.HeaderControl × SourceCSPQueryRange.Control) ×
              ((Option Bool × Option Bool) × SourceCSPVertexCap.Control))) =
        ⟨none,
          ((((none, none), (((none, none), none), none)),
            ((none, none), (none, false))), ((none, none), v)), S⟩ ∧
      S (.inr 6) = true :: List.replicate (P.vertices - 1) true ∧
      S (.inl (.inr 6)) = List.replicate P.constraints true := by
  let input := EncodedETHSource.constraintBits P
  obtain ⟨th, vh, Sh, hth, hrh, hnword, hmword, _, hextras⟩ :=
    framed_encoded_guard P
  have hready : ∀ k : Fin 7, 3 ≤ k.val → Sh (.inr k) = [] := by
    intro k _
    exact hextras k
  obtain ⟨tp, vp, Sp, htp, hrp, hcap, hm⟩ :=
    SourceCSPBudgetFrame.positive_cap_success
      P.vertices P.constraints q Sh hn hsize hmword hnword
      (hextras 0) (hextras 1) (hextras 2) hready
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (headerProgram a q) (SourceCSPBudgetFrame.positiveCapProgram q)
    (.inl (.inl (.inl BitMachineCopy.Label.scan)) :
      BitMachineRawSequence.Label (SourceCSPConstraintGuard.HeaderLabel a q)
        SourceCSPQueryRange.Label)
    (.inl (.inl ()) : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label Unit (SourceFixedUnaryBudget.Label q))
      SourceCSPVertexCap.Label)
    (((none, none), (((none, none), none), none)),
      ((none, none), (none, false))) vh
    ((none, none), (((none, none), (none, false)), none))
    ((none, none), vp)
    (initial input) Sh Sp th tp hrh hrp
  refine ⟨t, vp, Sp, ?_, ?_, hcap, hm⟩
  · change t ≤ positiveBound a q input.length
      P.constraints.bits.length P.vertices P.constraints
    dsimp only [input]
    unfold positiveBound
    omega
  · simpa only [fullHeaderProgram, input] using hr

end EthInapproximability.CurrentPaper.SourceCSPPositiveHeader
