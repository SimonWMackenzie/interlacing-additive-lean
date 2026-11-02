import EthInapproximability.CurrentPaper.SourceCSPHeaderFields
import EthInapproximability.CurrentPaper.SourceInputLengthUnary

/-!
# Shared physical input-length and header frame

The raw input is counted in unary before the header parser consumes it. The
counter preserves the source bitstream, so the header parser subsequently
reads the same physical input stack. Three foreign stacks retain the counter
work and its unary output while the fixed header is parsed and checked.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPInputFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := SourceCSPHeaderCheck.Stack ⊕ Fin 7

def lengthEmbedding : SourceInputLengthUnary.Stack ↪ Stack where
  toFun k := if k = 0 then .inl (.inl (.inr 0))
    else if k = 1 then .inr 0 else if k = 2 then .inr 1 else .inr 2
  inj' := by intro x y h; fin_cases x <;> fin_cases y <;> simp_all

def headerEmbedding : SourceCSPHeaderCheck.Stack ↪ Stack where
  toFun := Sum.inl
  inj' := by intro x y h; exact Sum.inl.inj h

def initial (input : List Bool) : Stack → List Bool
  | .inl k => SourceCSPHeaderCheck.parserInitial input k
  | .inr _ => []

noncomputable def afterLength (input : List Bool) : Stack → List Bool :=
  bank lengthEmbedding (initial input)
    (SourceInputLengthUnary.contents input [] []
      (List.replicate input.length true))

def lengthProgram (l : BitMachineRawSequence.Label BitMachineCopy.Label
    SourceInputLengthUnary.CountLabel) :=
  stmt lengthEmbedding id id id none (SourceInputLengthUnary.program l)

def headerProgram (a q : Nat) (l : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
      (SourceFixedBinaryCheck.Label a.bits))
    (SourceFixedBinaryCheck.Label q.bits)) :=
  stmt headerEmbedding id id id none (SourceCSPHeaderCheck.fixedHeaderProgram a q l)

theorem length_framed (input : List Bool) :
    ∃ t, t ≤ 3 * input.length + 4 ∧
      ((advance lengthProgram)^[t])
        (⟨some (.inl BitMachineCopy.Label.scan), (none, none), initial input⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label BitMachineCopy.Label
              SourceInputLengthUnary.CountLabel)
            (Option Bool × Option Bool)) =
        ⟨none, (none, none), afterLength input⟩ := by
  obtain ⟨t, ht, hr⟩ := SourceInputLengthUnary.length_run input
  let localCfg : SourceInputLengthUnary.Config :=
    ⟨some (.inl BitMachineCopy.Label.scan), (none, none),
      SourceInputLengthUnary.contents input [] [] []⟩
  have hhalt : (((advance SourceInputLengthUnary.program)^[t]) localCfg).l = none := by
    simpa only [BitMachineRawSequence.leftLabel] using
      congrArg (fun c => c.l) hr
  obtain ⟨u, hu, hrun⟩ := outputs lengthEmbedding (initial input)
    id id id (fun _ => rfl) none SourceInputLengthUnary.program
    lengthProgram (fun _ => rfl) localCfg t hhalt
  have hstart : cfg lengthEmbedding (initial input) id id none localCfg =
      (⟨some (.inl BitMachineCopy.Label.scan), (none, none), initial input⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label BitMachineCopy.Label
            SourceInputLengthUnary.CountLabel)
          (Option Bool × Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> rfl
  change ((advance SourceInputLengthUnary.program)^[t]) localCfg = _ at hr
  rw [hr, hstart] at hrun
  refine ⟨u, hu.trans ht, ?_⟩
  simpa only [afterLength, cfg, stackCfg, BitMachineInline.cfg,
    id_eq, Option.map_none] using hrun

theorem after_length_header (input : List Bool) :
    (fun k => afterLength input (headerEmbedding k)) =
      SourceCSPHeaderCheck.parserInitial input := by
  funext k
  dsimp only [afterLength, headerEmbedding]
  cases k with
  | inl r =>
      cases r with
      | inl j =>
          rw [bank_outside]
          · rfl
          · rintro ⟨i, hi⟩
            fin_cases i <;> simp [lengthEmbedding] at hi
      | inr i =>
          fin_cases i
          · change bank lengthEmbedding _ _ (lengthEmbedding 0) = _
            rw [bank_at]
            rfl
          · rw [bank_outside]
            · rfl
            · rintro ⟨j, hj⟩
              fin_cases j <;> simp [lengthEmbedding] at hj
          · rw [bank_outside]
            · rfl
            · rintro ⟨j, hj⟩
              fin_cases j <;> simp [lengthEmbedding] at hj
  | inr i =>
      fin_cases i
      rw [bank_outside]
      · rfl
      · rintro ⟨j, hj⟩
        fin_cases j <;> simp [lengthEmbedding] at hj

theorem after_length_cap (input : List Bool) :
    afterLength input (.inr 2) = List.replicate input.length true := by
  change bank lengthEmbedding _ _ (lengthEmbedding 3) = _
  rw [bank_at]
  rfl

theorem after_length_unused (input : List Bool) (k : Fin 7) (hk : 3 ≤ k.val) :
    afterLength input (.inr k) = [] := by
  change bank lengthEmbedding (initial input)
    (SourceInputLengthUnary.contents input [] []
      (List.replicate input.length true)) (.inr k) = []
  rw [bank_outside]
  · rfl
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp [lengthEmbedding] at hi <;> omega

theorem header_framed (n m a q : Nat) (rest : List Bool) :
    ∃ t v S, t ≤ 4 * (2 *
        (SourceCSPHeaderParse.header n m a q ++ rest).length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 2 ∧
      ((advance (headerProgram a q))^[t])
        (⟨some (.inl (.inl (.start 0))), (((none, none), none), none),
          afterLength (SourceCSPHeaderParse.header n m a q ++ rest)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
                (SourceFixedBinaryCheck.Label a.bits))
              (SourceFixedBinaryCheck.Label q.bits))
            ((SourceCSPRowController.Control × Option Bool) × Option Bool)) =
        ⟨none, (((none, none), none), v), S⟩ ∧
      S (.inl (.inr 0)) = [true, true] ∧
      S (.inl (.inl (.inl 0))) = n.bits ∧
      S (.inl (.inl (.inl 1))) = m.bits ∧
      S (.inl (.inl (.inr 0))) = rest ∧
      S (.inr 2) = List.replicate
        (SourceCSPHeaderParse.header n m a q ++ rest).length true ∧
      (∀ k : Fin 7, 3 ≤ k.val → S (.inr k) = []) := by
  let input := SourceCSPHeaderParse.header n m a q ++ rest
  obtain ⟨t, Sl, vl, ht, hr, hs, hn, hm, hrest⟩ :=
    SourceCSPHeaderFields.canonical_variable_words n m a q rest
  let before := afterLength input
  let localCfg : TM2.Cfg (fun _ : SourceCSPHeaderCheck.Stack => Bool)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
          (SourceFixedBinaryCheck.Label a.bits))
        (SourceFixedBinaryCheck.Label q.bits))
      ((SourceCSPRowController.Control × Option Bool) × Option Bool) :=
    ⟨some (.inl (.inl (.start 0))), (((none, none), none), none),
      SourceCSPHeaderCheck.parserInitial input⟩
  have hhalt : (((advance (SourceCSPHeaderCheck.fixedHeaderProgram a q))^[t])
      localCfg).l = none := by
    simpa only [SourceCSPHeaderCheck.fixedHeaderRun] using
      congrArg (fun c => c.l) hr
  obtain ⟨u, hu, hrun⟩ := outputs headerEmbedding before id id id
    (fun _ => rfl) none (SourceCSPHeaderCheck.fixedHeaderProgram a q)
    (headerProgram a q) (fun _ => rfl) localCfg t hhalt
  have hstart : cfg headerEmbedding before id id none localCfg =
      (⟨some (.inl (.inl (.start 0))), (((none, none), none), none), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          (BitMachineRawSequence.Label
            (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
              (SourceFixedBinaryCheck.Label a.bits))
            (SourceFixedBinaryCheck.Label q.bits))
          ((SourceCSPRowController.Control × Option Bool) × Option Bool)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, id_eq]
    congr 1
    apply bank_eq_self
    intro k
    exact (congrFun (after_length_header input) k).symm
  change ((advance (SourceCSPHeaderCheck.fixedHeaderProgram a q))^[t])
    localCfg = _ at hr
  rw [hr, hstart] at hrun
  let S := bank headerEmbedding before Sl
  refine ⟨u, vl, S, hu.trans ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, cfg, stackCfg, BitMachineInline.cfg,
      id_eq, Option.map_none] using hrun
  · change bank headerEmbedding before Sl (headerEmbedding (.inr 0)) = _
    rw [bank_at]
    exact hs
  · change bank headerEmbedding before Sl
      (headerEmbedding (.inl (.inl 0))) = _
    rw [bank_at]
    exact hn
  · change bank headerEmbedding before Sl
      (headerEmbedding (.inl (.inl 1))) = _
    rw [bank_at]
    exact hm
  · change bank headerEmbedding before Sl
      (headerEmbedding (.inl (.inr 0))) = _
    rw [bank_at]
    exact hrest
  · change bank headerEmbedding before Sl (.inr 2) = _
    rw [bank_outside]
    · exact after_length_cap input
    · rintro ⟨k, hk⟩
      cases hk
  · intro k hk
    change bank headerEmbedding before Sl (.inr k) = _
    rw [bank_outside]
    · exact after_length_unused input k hk
    · rintro ⟨j, hj⟩
      cases hj

def inputHeaderProgram (a q : Nat) :=
  BitMachineRawSequence.program lengthProgram (headerProgram a q)
    (.inl (.inl (.start 0)))
    ((none, none) : Option Bool × Option Bool)
    ((((none, none), none), none) :
      (SourceCSPRowController.Control × Option Bool) × Option Bool)

/-- The raw input length is counted before the same input is physically
consumed by canonical header parsing and fixed source-parameter checks. -/
theorem canonical_input_header (n m a q : Nat) (rest : List Bool) :
    ∃ t c, t ≤ 3 * (SourceCSPHeaderParse.header n m a q ++ rest).length + 4 +
        4 * (2 * (SourceCSPHeaderParse.header n m a q ++ rest).length + 4) + 3 +
        (a.bits.length + 1) + (q.bits.length + 1) + 3 ∧
      ((advance (inputHeaderProgram a q))^[t])
        (⟨some (.inl (.inl BitMachineCopy.Label.scan)),
          ((none, none), (((none, none), none), none)),
          initial (SourceCSPHeaderParse.header n m a q ++ rest)⟩ :
          TM2.Cfg (fun _ : Stack => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label BitMachineCopy.Label
                SourceInputLengthUnary.CountLabel)
              (BitMachineRawSequence.Label
                (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
                  (SourceFixedBinaryCheck.Label a.bits))
                (SourceFixedBinaryCheck.Label q.bits)))
            ((Option Bool × Option Bool) ×
              ((SourceCSPRowController.Control × Option Bool) × Option Bool))) = c ∧
      c.l = none ∧ c.stk (.inl (.inr 0)) = [true, true] ∧
      c.stk (.inl (.inl (.inl 0))) = n.bits ∧
      c.stk (.inl (.inl (.inl 1))) = m.bits ∧
      c.stk (.inl (.inl (.inr 0))) = rest ∧
      c.stk (.inr 2) = List.replicate
        (SourceCSPHeaderParse.header n m a q ++ rest).length true ∧
      (∀ k : Fin 7, 3 ≤ k.val → c.stk (.inr k) = []) := by
  let input := SourceCSPHeaderParse.header n m a q ++ rest
  obtain ⟨tl, htl, hrl⟩ := length_framed input
  obtain ⟨th, vh, Sh, hth, hrh, hstatus, hn, hm, hrest, hcap, hunused⟩ :=
    header_framed n m a q rest
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    lengthProgram (headerProgram a q)
    (.inl BitMachineCopy.Label.scan : BitMachineRawSequence.Label
      BitMachineCopy.Label SourceInputLengthUnary.CountLabel)
    (.inl (.inl (.start 0)) : BitMachineRawSequence.Label
      (BitMachineRawSequence.Label (SourceCSPRowController.Label 4 0)
        (SourceFixedBinaryCheck.Label a.bits))
      (SourceFixedBinaryCheck.Label q.bits))
    ((none, none) : Option Bool × Option Bool) (none, none)
    ((((none, none), none), none) :
      (SourceCSPRowController.Control × Option Bool) × Option Bool)
    (((none, none), none), vh)
    (initial input) (afterLength input) Sh tl th hrl hrh
  refine ⟨t, ⟨none, ((none, none), (((none, none), none), vh)), Sh⟩,
    ?_, ?_, rfl, hstatus, hn, hm, hrest, hcap, hunused⟩
  · dsimp only [input] at htl
    omega
  · simpa only [inputHeaderProgram, input] using hr

end EthInapproximability.CurrentPaper.SourceCSPInputFrame
