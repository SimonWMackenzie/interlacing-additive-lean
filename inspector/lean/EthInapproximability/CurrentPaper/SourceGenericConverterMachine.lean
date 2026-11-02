import EthInapproximability.CurrentPaper.SourceGenericConverterFinite

/-!
# The fixed generic converter as one `BitMachine.Machine`

Paper B, locked v8 Section 6 (`thm:paper-sparse-gap-source`) and Appendix B;
CP-SOURCE-EFFECTIVE, arbitrary fixed alphabet `a` (never `a = 2`).

`machine a q hq` is `BitMachineEncoding.ofFinite` of the frozen predecessor
program `SourceGenericComposite.Converter.converter a q hq`, with its actual
raw-input cell as input and the validator output slot as output. The ordinary
`Machine.init input` is exactly the predecessor's `converterInitial` (raw input
in the validator's input cell, every other cell empty). The predecessor's run
theorems transfer with the SAME transition count (`outputsWithin_of_raw_run`).
-/

namespace EthInapproximability.CurrentPaper.SourceGenericComposite.ConverterMachine

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericComposite.Converter
open scoped Classical

noncomputable section

/-- The validator's raw-input cell (the parser `source` cell). -/
def gIn (q : Nat) : SourceCSPGlobalDecisionProgram.Stack q :=
  .inl (.inl (.inl (.inl (.inr 0))))

theorem global_initial_single (q : Nat) (input : List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    SourceCSPHeaderRowBridge.initial input g = if g = gIn q then input else [] := by
  rcases g with ((((j | j) | j) | j) | j) | j
  · simp [SourceCSPHeaderRowBridge.initial, SourceCSPPositiveHeader.initial,
      SourceCSPInputFrame.initial, SourceCSPHeaderCheck.parserInitial,
      SourceCSPRowController.contents, gIn]
  · fin_cases j <;>
      simp [SourceCSPHeaderRowBridge.initial, SourceCSPPositiveHeader.initial,
        SourceCSPInputFrame.initial, SourceCSPHeaderCheck.parserInitial,
        SourceCSPRowController.contents, gIn]
  · simp [SourceCSPHeaderRowBridge.initial, SourceCSPPositiveHeader.initial,
      SourceCSPInputFrame.initial, SourceCSPHeaderCheck.parserInitial, gIn]
  · simp [SourceCSPHeaderRowBridge.initial, SourceCSPPositiveHeader.initial,
      SourceCSPInputFrame.initial, gIn]
  · simp [SourceCSPHeaderRowBridge.initial, SourceCSPPositiveHeader.initial, gIn]
  · simp [SourceCSPHeaderRowBridge.initial, gIn]

/-- The converter's raw-input cell. -/
def inCell (q : Nat) : CStack q := globalEmbC q (gIn q)

variable (a q : Nat) (hq : 0 < q)

abbrev Lab := TopLabel a q (LabOf (body (a := a) hq))
abbrev Ctl := TopControl a q (FirstRow.CtlOf (body (a := a) hq))

def startLabel : Lab a q hq :=
  BitMachineRawSequence.leftLabel
    (.prefix (.prefix (.inl (SourceCSPGuardDispatchSequence.headerStart a q))))

noncomputable def startControl : Ctl a q hq :=
  (.prefix SourceCSPGuardOutputCombined.initialControl, bodyInit (a := a) hq)

instance labFintype : Fintype (Lab a q hq) :=
  @Fintype.ofFinite _ (ConverterFinite.labelFinite a q hq)

instance ctlFintype : Fintype (Ctl a q hq) :=
  @Fintype.ofFinite _ (ConverterFinite.controlFinite a q hq)

/-- THE fixed converter machine at fixed `(a,q)`. -/
noncomputable def machine : BitMachine.Machine :=
  ofFinite (inCell q) (outCell q) (startLabel a q hq) (startControl a q hq)
    (converter a q hq)

theorem converterInitial_eq (input : List Bool) :
    converterInitial a q hq input =
      rawInit (inCell q) (startLabel a q hq) (startControl a q hq) input := by
  unfold converterInitial topCInitial rawInit
  simp only [BitMachineInline.cfg, stackCfg, SourceCSPGlobalDecisionProgram.initial]
  congr 1
  funext k
  by_cases hk : ∃ g, globalEmbC q g = k
  · obtain ⟨g, rfl⟩ := hk
    rw [bank_at, global_initial_single]
    by_cases hg : g = gIn q
    · subst hg; simp [inCell]
    · have hne : globalEmbC q g ≠ inCell q := by
        intro h; exact hg ((globalEmbC q).injective h)
      simp [hg, hne]
  · rw [bank_outside _ _ _ _ hk]
    have hne : k ≠ inCell q := by
      rintro rfl; exact hk ⟨gIn q, rfl⟩
    simp [hne]

variable {a q}

/-- Every raw input: the SAME fixed machine halts within the predecessor's
clock with the reject word, the zero word, or the encoded three-CNF of the
read-back instance. -/
theorem machine_total (ha : 0 < a) (hq : 0 < q) (input : List Bool) :
    ∃ out : List Bool,
      (machine a q hq).OutputsWithin input out (convC a q * (input.length + 1) ^ 27) ∧
      ((out = SourceCSPRejectFormula.bits ∧ out ∉ EncodedCNF.Language) ∨
        out = [false, false] ∨
        (∃ (n m : Nat) (rows : Fin m → SourceCSPCodec.Row n a q) (suffix : List Bool),
          input = SourceCSPHeaderParse.header n m a q ++ suffix ∧
          SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix = some (rows, []) ∧
          out = EncodedCNF.encode (SourceBooleanEncoding.threeCNF
            (SourceCSPCodec.fromRows n m a q rows).system hq))) := by
  obtain ⟨t, ht, c, W, hrun, hcase⟩ := converter_total ha hq input
  refine ⟨W (outCell q), ?_, hcase⟩
  apply outputsWithin_of_raw_run (inCell q) (outCell q) (startLabel a q hq)
    (startControl a q hq) (converter a q hq) input (W (outCell q)) t _ ht
  · rw [← converterInitial_eq, hrun]
  · rw [← converterInitial_eq, hrun]

/-- Typed valid instances (zero vertices included). -/
theorem machine_valid (ha : 0 < a) (hq : 0 < q)
    (P : EncodedETHSource.ConstraintInstance a q) (hsize : SourceCSPCodec.ValidSize P) :
    (machine a q hq).OutputsWithin (EncodedETHSource.constraintBits P)
      (EncodedCNF.encode (SourceBooleanEncoding.threeCNF P.system hq))
      (convC a q * ((EncodedETHSource.constraintBits P).length + 1) ^ 27) := by
  obtain ⟨t, ht, c, W, hrun, hout⟩ := converter_valid ha hq P hsize
  apply outputsWithin_of_raw_run (inCell q) (outCell q) (startLabel a q hq)
    (startControl a q hq) (converter a q hq) _ _ t _ ht
  · rw [← converterInitial_eq, hrun]
  · rw [← converterInitial_eq, hrun]; exact hout

/-- The cited Dinur output at `(a,q) = (D.alphabet, D.arity)`. Hypotheses used:
`D.alphabet_pos`, `D.arity_pos`, `D.no_isolates`, `D.bitFunction_valid`. -/
theorem machine_dinur (D : EncodedETHSource.DinurReduction)
    (f : EncodedETHSource.ValidFormula) :
    (machine D.alphabet D.arity D.arity_pos).OutputsWithin
      (EncodedETHSource.constraintBits (D.reduce f))
      (EncodedCNF.encode (EncodedETHSourceComposition.booleanFormula D f).val)
      (convC D.alphabet D.arity *
        ((EncodedETHSource.constraintBits (D.reduce f)).length + 1) ^ 27) :=
  machine_valid D.alphabet_pos D.arity_pos (D.reduce f) (D.no_isolates f)

/-- The same statement on the cited bit function's literal output word. -/
theorem machine_dinur_bits (D : EncodedETHSource.DinurReduction)
    (f : EncodedETHSource.ValidFormula) :
    (machine D.alphabet D.arity D.arity_pos).OutputsWithin
      (D.bitFunction (EncodedCNF.encode f.val))
      (EncodedCNF.encode (EncodedETHSourceComposition.booleanFormula D f).val)
      (convC D.alphabet D.arity *
        ((D.bitFunction (EncodedCNF.encode f.val)).length + 1) ^ 27) := by
  rw [D.bitFunction_valid f]
  exact machine_dinur D f

end

#print axioms global_initial_single
#print axioms converterInitial_eq
#print axioms machine_total
#print axioms machine_valid
#print axioms machine_dinur
#print axioms machine_dinur_bits

end EthInapproximability.CurrentPaper.SourceGenericComposite.ConverterMachine
