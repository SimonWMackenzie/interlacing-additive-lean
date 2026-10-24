import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.SourceCSPCodec

/-!
# Physical bounded query validation with preserved operands

Source: frozen v8 `06-eth.tex`, the bounded finite-alphabet CSP to Boolean
source adapter. The original binary query and unary vertex cap are retained
while actual copy and bounded-subtraction programs use scratch stacks. A cap
of length `n-1` is correct only when `n > 0`; zero vertices must be rejected
by the enclosing controller.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPQueryRange

open Turing BitMachineEncoding BitMachineStackEmbedding

abbrev Stack := Fin 6
abbrev CopyLabel := BitMachineRawSequence.Label BitMachineCopy.Label BitMachineCopy.Label
abbrev Label := BitMachineRawSequence.Label CopyLabel ProtocolBoundedUnary.Label
abbrev CopyControl := Option Bool × Option Bool
abbrev Control := CopyControl × ProtocolBoundedUnary.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def queryCopy : Fin 3 ↪ Stack where
  toFun k := if k = 0 then 0 else if k = 1 then 2 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def capCopy : Fin 3 ↪ Stack where
  toFun k := if k = 0 then 1 else if k = 1 then 3 else 4
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def bounded : Fin 4 ↪ Stack where
  toFun k := if k = 0 then 2 else if k = 1 then 3 else if k = 2 then 4 else 5
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def contents (query cap queryWork capWork scratch output : List Bool) : Stack → List Bool :=
  ![query, cap, queryWork, capWork, scratch, output]

def copyQuery (l : BitMachineCopy.Label) :=
  stackStmt queryCopy (BitMachineCopy.program l)

def copyCap (l : BitMachineCopy.Label) :=
  stackStmt capCopy (BitMachineCopy.program l)

def validate (l : ProtocolBoundedUnary.Label) :=
  stackStmt bounded (ProtocolBoundedUnary.program l)

def copies := BitMachineRawSequence.program copyQuery copyCap
  .scan (none : Option Bool) (none : Option Bool)

def program := BitMachineRawSequence.program copies validate
  .zeroScan ((none, none) : CopyControl) ((none, false) : ProtocolBoundedUnary.Control)

private theorem query_initial (query cap output : List Bool) :
    bank queryCopy (contents query cap [] [] [] output)
      (BitMachineCopy.cfg (some .scan) none query [] []).stk =
      contents query cap [] [] [] output := by
  apply bank_eq_self
  intro k
  fin_cases k <;> rfl

private theorem query_final (query cap output : List Bool) :
    bank queryCopy (contents query cap [] [] [] output)
      (BitMachineCopy.cfg none none query query []).stk =
      contents query cap query [] [] output := by
  funext k
  fin_cases k
  · change bank queryCopy _ _ (queryCopy 0) = _
    rw [bank_at]; rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [queryCopy] at hj
  · change bank queryCopy _ _ (queryCopy 1) = _
    rw [bank_at]; rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [queryCopy] at hj
  · change bank queryCopy _ _ (queryCopy 2) = _
    rw [bank_at]; rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [queryCopy] at hj

private theorem cap_initial (query cap output : List Bool) :
    bank capCopy (contents query cap query [] [] output)
      (BitMachineCopy.cfg (some .scan) none cap [] []).stk =
      contents query cap query [] [] output := by
  apply bank_eq_self
  intro k
  fin_cases k <;> rfl

private theorem cap_final (query cap output : List Bool) :
    bank capCopy (contents query cap query [] [] output)
      (BitMachineCopy.cfg none none cap cap []).stk =
      contents query cap query cap [] output := by
  funext k
  fin_cases k
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [capCopy] at hj
  · change bank capCopy _ _ (capCopy 0) = _
    rw [bank_at]; rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [capCopy] at hj
  · change bank capCopy _ _ (capCopy 1) = _
    rw [bank_at]; rfl
  · change bank capCopy _ _ (capCopy 2) = _
    rw [bank_at]; rfl
  · rw [bank_outside]
    · rfl
    · intro ⟨j, hj⟩; fin_cases j <;> simp [capCopy] at hj

private theorem bounded_initial (query cap output : List Bool) :
    bank bounded (contents query cap query cap [] output)
      (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
        query cap [] output).stk =
      contents query cap query cap [] output := by
  apply bank_eq_self
  intro k
  fin_cases k <;> rfl

/-- The physical program preserves both operands, returns the exact status and
unary result, and charges both source-preserving copies, the bounded loop, and
the two finite-control handoffs. Residual working operands are deliberately
not claimed to equal their initial values. -/
theorem range_run (query cap output : List Bool) :
    ∃ t c, t ≤ 2 * query.length + 2 + (2 * cap.length + 2) + 1 +
          (cap.length + 1) * (4 * query.length + 5) + 1 ∧
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), (none, false)),
          contents query cap [] [] [] output⟩ : Config) = c ∧
      c.l = none ∧ c.stk 0 = query ∧ c.stk 1 = cap ∧
      c.stk 4 = [] ∧ c.stk 5 = ProtocolBoundedUnary.result query cap output := by
  have hq := BitMachineCopy.run_correct none query []
  have hq' := BitMachineStackRun.run queryCopy (contents query cap [] [] [] output)
    BitMachineCopy.program (BitMachineCopy.cfg (some .scan) none query [] [])
    (2 * query.length + 2)
  rw [show ((advance BitMachineCopy.program)^[2 * query.length + 2])
      (BitMachineCopy.cfg (some .scan) none query [] []) = _ from hq] at hq'
  simp only [stackCfg, query_initial] at hq'
  have hq'' : ((advance copyQuery)^[2 * query.length + 2])
      (⟨some BitMachineCopy.Label.scan, none,
        contents query cap [] [] [] output⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, contents query cap query [] [] output⟩ := by
    simpa only [List.append_nil, query_final] using hq'
  have hc := BitMachineCopy.run_correct none cap []
  have hc' := BitMachineStackRun.run capCopy (contents query cap query [] [] output)
    BitMachineCopy.program (BitMachineCopy.cfg (some .scan) none cap [] [])
    (2 * cap.length + 2)
  rw [show ((advance BitMachineCopy.program)^[2 * cap.length + 2])
      (BitMachineCopy.cfg (some .scan) none cap [] []) = _ from hc] at hc'
  simp only [stackCfg, cap_initial] at hc'
  have hc'' : ((advance copyCap)^[2 * cap.length + 2])
      (⟨some BitMachineCopy.Label.scan, none,
        contents query cap query [] [] output⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, contents query cap query cap [] output⟩ := by
    simpa only [List.append_nil, cap_final] using hc'
  obtain ⟨tc, htc, hcopies⟩ := BitMachineRawSequence.runs copyQuery copyCap
    .scan .scan (none : Option Bool) none (none : Option Bool) none
    (contents query cap [] [] [] output)
    (contents query cap query [] [] output)
    (contents query cap query cap [] output)
    (2 * query.length + 2) (2 * cap.length + 2) hq'' hc''
  obtain ⟨tb, cb, htb, hb, hhalt, hout, _, hwork, _⟩ :=
    ProtocolBoundedUnary.bounded_run_framed query cap output
  have hb' := BitMachineStackRun.run bounded
    (contents query cap query cap [] output) ProtocolBoundedUnary.program
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
      query cap [] output) tb
  rw [show ((advance ProtocolBoundedUnary.program)^[tb])
      (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
        query cap [] output) = cb from hb] at hb'
  simp only [stackCfg, bounded_initial] at hb'
  cases cb with
  | mk l v S =>
      simp only at hhalt hout hwork hb'
      subst l
      obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs copies validate
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) .zeroScan
        ((none, none) : CopyControl) (none, none)
        ((none, false) : ProtocolBoundedUnary.Control) v
        (contents query cap [] [] [] output)
        (contents query cap query cap [] output)
        (bank bounded (contents query cap query cap [] output) S)
        tc tb hcopies hb'
      refine ⟨t, _, by omega, hr, rfl, ?_, ?_, ?_, ?_⟩
      · exact (bank_outside bounded _ S 0 (by
          intro ⟨k, hk⟩; fin_cases k <;> simp [bounded] at hk)).trans rfl
      · exact (bank_outside bounded _ S 1 (by
          intro ⟨k, hk⟩; fin_cases k <;> simp [bounded] at hk)).trans rfl
      · change bank bounded (contents query cap query cap [] output) S (bounded 2) = []
        rw [bank_at]
        exact hwork
      · change bank bounded (contents query cap query cap [] output) S (bounded 3) = _
        rw [bank_at]
        exact hout

/-- The physical bounded-subtraction result implements a strict vertex-range
test when the cap has one cell fewer than the positive vertex count. -/
theorem result_at_vertices (query output : List Bool) (n : ℕ) (hn : 0 < n) :
    ProtocolBoundedUnary.result query (List.replicate (n - 1) true) output =
      if EncodedCommunication.bitsValue query < n then
        true :: List.replicate (EncodedCommunication.bitsValue query) true ++ output
      else false :: List.replicate (n - 1) true ++ output := by
  unfold ProtocolBoundedUnary.result
  simp only [List.length_replicate]
  split_ifs with h
  · have hv : EncodedCommunication.bitsValue query ≤ n - 1 := by omega
    simp [hv]
  · have hv : n - 1 ≤ EncodedCommunication.bitsValue query := by omega
    have hf : ¬ EncodedCommunication.bitsValue query ≤ n - 1 := by omega
    simp [hf, Nat.min_eq_right hv]

/-- A typed row's selected query is accepted, and its unary coordinate is
written physically. This theorem uses the same actual program as `range_run`;
the typed row merely supplies the strict-range proof. -/
theorem typed_row_query_run {n a q : ℕ} (row : SourceCSPCodec.Row n a q)
    (i : Fin q) (hn : 0 < n) (output : List Bool) :
    ∃ t c, t ≤ 2 * (row.1 i).val.bits.length + 2 +
          (2 * (n - 1) + 2) + 1 +
          (n - 1 + 1) * (4 * (row.1 i).val.bits.length + 5) + 1 ∧
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
          ((none, none), (none, false)),
          contents (row.1 i).val.bits (List.replicate (n - 1) true)
            [] [] [] output⟩ : Config) = c ∧
      c.l = none ∧ c.stk 0 = (row.1 i).val.bits ∧
      c.stk 1 = List.replicate (n - 1) true ∧ c.stk 4 = [] ∧
      c.stk 5 = true :: List.replicate (row.1 i).val true ++ output := by
  obtain ⟨t, c, ht, hr, hl, hq, hc, hs, ho⟩ :=
    range_run (row.1 i).val.bits (List.replicate (n - 1) true) output
  refine ⟨t, c, by simpa only [List.length_replicate] using ht,
    hr, hl, hq, hc, hs, ?_⟩
  rw [ho, result_at_vertices _ _ n hn, EncodedCommunication.bitsValue_bits,
    if_pos (row.1 i).isLt]

end EthInapproximability.CurrentPaper.SourceCSPQueryRange
