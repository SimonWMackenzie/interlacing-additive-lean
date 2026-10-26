import EthInapproximability.CurrentPaper.SourceCSPHeaderParse
import EthInapproximability.CurrentPaper.SourceFixedBinaryCheck
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-!
# Framed literal checks of the fixed CSP alphabet and arity

The four header words occupy permanent stack positions. A fixed-word
comparator is inlined on one chosen position, writing its result on a
separate status stack. The check consumes the selected word but leaves the
other header words and the unconsumed source suffix in place.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPHeaderCheck

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPRowController.Stack 4 ⊕ Fin 1

def checkerEmbedding (j : Fin 4) : Fin 2 ↪ Stack where
  toFun k := if k = 0 then .inl (.inl j) else .inr 0
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all

def parserEmbedding : SourceCSPRowController.Stack 4 ↪ Stack where
  toFun := Sum.inl
  inj' := by intro x y h; exact Sum.inl.inj h

def parserProgram (l : SourceCSPRowController.Label 4 0) :
    TM2.Stmt (fun _ : Stack => Bool) (SourceCSPRowController.Label 4 0)
      SourceCSPRowController.Control :=
  stmt parserEmbedding id id id none (SourceCSPRowController.program 4 0 l)

def parserRun (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      (SourceCSPRowController.Label 4 0) SourceCSPRowController.Control) :=
  ((advance parserProgram)^[t]) c

def parserInitial (input : List Bool) : Stack → List Bool
  | .inl k => SourceCSPRowController.contents (fun _ => []) input [] [] k
  | .inr _ => []

noncomputable def parserAfter (n m a q : Nat) (rest : List Bool) :
    Stack → List Bool :=
  bank parserEmbedding (parserInitial (SourceCSPHeaderParse.header n m a q ++ rest))
    (SourceCSPRowController.contents (fun j =>
      (SourceCSPHeaderParse.numbers n m a q j).bits) rest [] [true])

theorem parser_canonical (n m a q : Nat) (rest : List Bool) :
    ∃ t v, t ≤ 4 * (2 *
        (SourceCSPHeaderParse.header n m a q ++ rest).length + 4) + 3 ∧
      parserRun t
        (⟨some (.start 0), (none, none),
          parserInitial (SourceCSPHeaderParse.header n m a q ++ rest)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (SourceCSPRowController.Label 4 0) SourceCSPRowController.Control) =
        ⟨none, v, parserAfter n m a q rest⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceCSPHeaderParse.canonical_run n m a q rest
  let input := SourceCSPHeaderParse.header n m a q ++ rest
  let before := parserInitial input
  let localCfg : SourceCSPHeaderParse.Config :=
    SourceCSPRowController.cfg (H := 0) (some (.start 0))
      (none, none) (fun _ => []) input [] []
  have hhalt : (SourceCSPRowController.run (H := 0) t localCfg).l = none := by
    rw [hr]
    rfl
  obtain ⟨u, hu, hrun⟩ := outputs parserEmbedding before id id id
    (fun _ => rfl) none (SourceCSPRowController.program 4 0)
    parserProgram (fun _ => rfl) localCfg t hhalt
  have hstart : cfg parserEmbedding before id id none localCfg =
      (⟨some (.start 0), (none, none), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (SourceCSPRowController.Label 4 0) SourceCSPRowController.Control) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq,
      SourceCSPRowController.cfg]
    congr 1
    apply bank_eq_self
    intro k
    cases k with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  change ((advance (SourceCSPRowController.program 4 0))^[t]) localCfg = _ at hr
  rw [hr, hstart] at hrun
  refine ⟨u, (none, none), hu.trans ht, ?_⟩
  simpa only [parserRun, parserAfter, cfg, stackCfg,
    BitMachineInline.cfg, SourceCSPRowController.cfg,
    id_eq, Option.map_none] using hrun

theorem parser_word (n m a q : Nat) (rest : List Bool) (j : Fin 4) :
    parserAfter n m a q rest (.inl (.inl j)) =
      (SourceCSPHeaderParse.numbers n m a q j).bits := by
  change bank parserEmbedding _ _ (parserEmbedding (.inl j)) = _
  rw [bank_at]
  rfl

theorem parser_status (n m a q : Nat) (rest : List Bool) :
    parserAfter n m a q rest (.inr 0) = [] := by
  apply bank_outside
  rintro ⟨k, hk⟩
  cases hk

def checkerProgram (expected : List Bool) (j : Fin 4)
    (l : SourceFixedBinaryCheck.Label expected) :
    TM2.Stmt (fun _ : Stack => Bool) (SourceFixedBinaryCheck.Label expected)
      (Option Bool) :=
  stmt (checkerEmbedding j) id id id none (SourceFixedBinaryCheck.program expected l)

def checkerRun (expected : List Bool) (j : Fin 4) (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      (SourceFixedBinaryCheck.Label expected) (Option Bool)) :=
  ((advance (checkerProgram expected j))^[t]) c

theorem checker_total (expected word status : List Bool) (j : Fin 4)
    (before : Stack → List Bool)
    (hword : before (.inl (.inl j)) = word)
    (hstatus : before (.inr 0) = status) :
    ∃ t v S, t ≤ expected.length + 1 ∧
      checkerRun expected j t
        (⟨some (.compare 0), none, before⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (SourceFixedBinaryCheck.Label expected) (Option Bool)) =
        ⟨none, v, S⟩ ∧
      S (.inr 0) = decide (word = expected) :: status ∧
      (∀ k : Fin 4, k ≠ j → S (.inl (.inl k)) = before (.inl (.inl k))) ∧
      S (.inl (.inr 0)) = before (.inl (.inr 0)) := by
  let localCfg : SourceFixedBinaryCheck.Config expected :=
    ⟨some (.compare 0), none, SourceFixedBinaryCheck.contents word status⟩
  obtain ⟨t, c, ht, hr, hh, hs⟩ :=
    SourceFixedBinaryCheck.run_from expected 0 word status none
  have hlocal : localCfg =
      (⟨some (.compare 0), none, SourceFixedBinaryCheck.contents word status⟩ :
        SourceFixedBinaryCheck.Config expected) := rfl
  have hhalt : (SourceFixedBinaryCheck.run expected t localCfg).l = none := by
    rw [hlocal, hr]
    exact hh
  obtain ⟨u, hu, hrun⟩ := outputs (checkerEmbedding j) before id id id
    (fun _ => rfl) none (SourceFixedBinaryCheck.program expected)
    (checkerProgram expected j) (fun _ => rfl) localCfg t hhalt
  have hstart : cfg (checkerEmbedding j) before id id none localCfg =
      (⟨some (.compare 0), none, before⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (SourceFixedBinaryCheck.Label expected) (Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [checkerEmbedding, SourceFixedBinaryCheck.contents,
      hword, hstatus]
  change ((advance (SourceFixedBinaryCheck.program expected))^[t]) localCfg = c at hr
  rw [hr, hstart] at hrun
  refine ⟨u, c.var, bank (checkerEmbedding j) before c.stk,
    hu.trans ht, ?_, ?_, ?_, ?_⟩
  · simpa only [checkerRun, cfg, stackCfg, BitMachineInline.cfg, hh,
      id_eq, Option.map_none] using hrun
  · change bank (checkerEmbedding j) before c.stk
        (checkerEmbedding j 1) = _
    rw [bank_at]
    simpa only [List.drop_zero, Fin.val_zero, Nat.sub_zero] using hs
  · intro k hk
    apply bank_outside
    rintro ⟨u, hu⟩
    fin_cases u
    · simp [checkerEmbedding] at hu
      exact hk hu.symm
    · simp [checkerEmbedding] at hu
  · apply bank_outside
    rintro ⟨u, hu⟩
    fin_cases u <;> simp [checkerEmbedding] at hu

def alphabetProgram (a : Nat) :=
  BitMachineRawSequence.program parserProgram
    (checkerProgram a.bits 2) (.compare 0 : SourceFixedBinaryCheck.Label a.bits)
    ((none, none) : SourceCSPRowController.Control) (none : Option Bool)

def alphabetRun (a t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
        (SourceFixedBinaryCheck.Label a.bits))
      (BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))) :=
  ((advance (alphabetProgram a))^[t]) c

/-- The canonical four-field header is physically parsed and its fixed
alphabet word physically checked. This is a two-stage computation on one
stack bank; arity checking is a subsequent stage. -/
theorem canonical_alphabet (n m a q : Nat) (rest : List Bool) :
    ∃ t S v, t ≤ 4 * (2 *
        (SourceCSPHeaderParse.header n m a q ++ rest).length + 4) + 3 +
        (a.bits.length + 1) + 1 ∧
      alphabetRun a t
        (⟨some (.inl (.start 0)), ((none, none), none),
          parserInitial (SourceCSPHeaderParse.header n m a q ++ rest)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
              (SourceFixedBinaryCheck.Label a.bits))
            (BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))) =
        ⟨none, ((none, none), v), S⟩ ∧
      S (.inr 0) = [true] ∧
      S (.inl (.inl 3)) = q.bits ∧
      S (.inl (.inr 0)) = rest := by
  obtain ⟨tp, vp, hp, hpr⟩ := parser_canonical n m a q rest
  have ha : parserAfter n m a q rest (.inl (.inl 2)) = a.bits := by
    simpa [SourceCSPHeaderParse.numbers] using parser_word n m a q rest 2
  obtain ⟨tc, vc, S, hc, hcr, hs, hq, hrest⟩ :=
    checker_total a.bits a.bits [] 2 (parserAfter n m a q rest) ha
      (parser_status n m a q rest)
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs parserProgram
    (checkerProgram a.bits 2)
    (.start 0 : SourceCSPRowController.Label 4 0)
    (.compare 0 : SourceFixedBinaryCheck.Label a.bits)
    ((none, none) : SourceCSPRowController.Control)
    vp (none : Option Bool) vc
    (parserInitial (SourceCSPHeaderParse.header n m a q ++ rest))
    (parserAfter n m a q rest) S tp tc hpr hcr
  refine ⟨t, S, vc, ?_, hr, ?_, ?_, ?_⟩
  · omega
  · simpa using hs
  · rw [hq 3 (by decide)]
    simpa [SourceCSPHeaderParse.numbers] using parser_word n m a q rest 3
  · rw [hrest]
    change bank parserEmbedding _ _ (parserEmbedding (.inr 0)) = _
    rw [bank_at]
    rfl

def fixedHeaderProgram (a q : Nat) :=
  BitMachineRawSequence.program (alphabetProgram a)
    (checkerProgram q.bits 3) (.compare 0 : SourceFixedBinaryCheck.Label q.bits)
    (((none, none), none) :
      BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))
    (none : Option Bool)

def fixedHeaderRun (a q t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
          (SourceFixedBinaryCheck.Label a.bits))
        (SourceFixedBinaryCheck.Label q.bits))
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))
        (Option Bool))) :=
  ((advance (fixedHeaderProgram a q))^[t]) c

/-- Both fixed source-parameter fields are physically validated on canonical
headers. The retained `n,m` words and input suffix are not decoded here. -/
theorem canonical_fixed_header (n m a q : Nat) (rest : List Bool) :
    ∃ t S v, t ≤ 4 * (2 *
        (SourceCSPHeaderParse.header n m a q ++ rest).length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 2 ∧
      fixedHeaderRun a q t
        (⟨some (.inl (.inl (.start 0))), (((none, none), none), none),
          parserInitial (SourceCSPHeaderParse.header n m a q ++ rest)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
                (SourceFixedBinaryCheck.Label a.bits))
              (SourceFixedBinaryCheck.Label q.bits))
            (BitMachineRawSequence.Control
              (BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))
              (Option Bool))) =
        ⟨none, (((none, none), none), v), S⟩ ∧
      S (.inr 0) = [true, true] ∧
      S (.inl (.inr 0)) = rest := by
  obtain ⟨ta, Sa, va, hta, hra, hsa, hqa, hresta⟩ :=
    canonical_alphabet n m a q rest
  obtain ⟨tq, vq, Sq, htq, hrq, hsq, _, hrestq⟩ :=
    checker_total q.bits q.bits [true] 3 Sa hqa hsa
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (alphabetProgram a) (checkerProgram q.bits 3)
    (.inl (.start 0) : BitMachineRawSequence.Label
      (SourceCSPRowController.Label 4 0)
      (SourceFixedBinaryCheck.Label a.bits))
    (.compare 0 : SourceFixedBinaryCheck.Label q.bits)
    (((none, none), none) :
      BitMachineRawSequence.Control SourceCSPRowController.Control (Option Bool))
    ((none, none), va) (none : Option Bool) vq
    (parserInitial (SourceCSPHeaderParse.header n m a q ++ rest))
    Sa Sq ta tq hra hrq
  refine ⟨t, Sq, vq, ?_, hr, ?_, ?_⟩
  · omega
  · simpa using hsq
  · exact hrestq.trans hresta

end EthInapproximability.CurrentPaper.SourceCSPHeaderCheck
