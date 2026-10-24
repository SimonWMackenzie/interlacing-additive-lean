import CurrentAdditive.V38ReadyBank

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace CurrentAdditive.V38PhysicalRenderer

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open EncodedCommunication
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.V38ReadyScalars (labelType controlType b d)
open CurrentAdditive.V38TablePrinter.Ambient
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec Paper2.YaoFrame Paper2.HeaderA

def prefixStart (t : ℕ) : labelType (V38ReadyField.program t) :=
  BitMachineRawSequence.leftLabel (V38ReadyField.prefixStart t)
def prefixControl (t : ℕ) : controlType (V38ReadyField.program t) :=
  (V38ReadyField.prefixControl t,V38ReadyField.fieldControl t)
def printerStart (t : ℕ) : labelType (CurrentAdditive.V38TablePrinter.Ambient.writerHeaderProgram t 16) :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (MultiMove.startLabel ((CurrentAdditive.V38TablePrinter.Ambient.writerJobs t 16).map CopyFill.toJob)))
def printerControl (t : ℕ) : controlType (CurrentAdditive.V38TablePrinter.Ambient.writerHeaderProgram t 16) :=
  ((MultiMove.initial,CurrentAdditive.V38TablePrinter.Ambient.writerTableControl),(MultiMove.initial,progCtl))

def program (t : ℕ) := BitMachineRawSequence.program
  (V38ReadyField.program t) (CurrentAdditive.V38TablePrinter.Ambient.writerHeaderProgram t 16)
  (printerStart t) (prefixControl t) (printerControl t)

def clock {t : ℕ} (x : YaoSource t) :=
  V38ReadyField.clock x + preparedBudget t (d x) x.2.2 + 1

def word {t : ℕ} (x : YaoSource t) : List Bool :=
  encodeInstance (V38Executable.instanceOfTable (b x) t (d x)
    ((TrialSearch.firstPassing (d x)).getD 0) (le_paddedEdgeCount x.2.1) x.2.2)

theorem printer_run (t : ℕ) (x : YaoSource t) (p modulus : ℕ) :
    ∃ steps ≤ preparedBudget t (d x) x.2.2, ∃ control,
      ((advance (CurrentAdditive.V38TablePrinter.Ambient.writerHeaderProgram t 16))^[steps])
        (⟨some (printerStart t), printerControl t, V38ReadyField.outputBank x p modulus⟩ :
          TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, ((MultiMove.initial,control),(MultiMove.initial,progCtl)),
          bank (headerEmbed t 16)
            (CopyFill.fill (CurrentAdditive.V38TablePrinter.Ambient.headerJobs t 16)
              (CurrentAdditive.V38TablePrinter.Ambient.writerOutputBank t 16 (d x) modulus x.2.2 (V38ReadyField.outputBank x p modulus)))
            (fun k => if k=outH then encodeInstance
              (V38Executable.instanceOfTable (b x) t (d x) modulus
                (le_paddedEdgeCount x.2.1) x.2.2) else [])⟩ := by
  let S := V38ReadyField.outputBank x p modulus
  have h := V38ReadyField.output_ready x p modulus
  obtain ⟨u,hu,c,hr⟩ := physical_writer_header t 16 (d x) modulus x.2.2 S
    h.scratch h.writer h.header h.capacity h.labels h.addresses h.body h.arity
    h.bits h.width h.rows h.columns h.threshold
  have hw := writer_copy_cost t 16 (d x) modulus x.2.2 S
    h.capacity h.labels h.addresses h.body h.arity h.bits h.width h.rows h.columns
  have hh := header_copy_cost t 16 (d x) modulus x.2.2 S h.rows h.columns h.threshold
  rw [hw,hh] at hu
  have ht : u ≤ preparedBudget t (d x) x.2.2 := by
    dsimp only [preparedBudget,headerRunBudget]
    simp only [Nat.mul_add]
    omega
  exact ⟨u,ht,c,by simpa only [printerStart,printerControl,S] using hr⟩

theorem raw_run (t : ℕ) (ht : 4 ≤ t) (x : YaoSource t) :
    ∃ steps ≤ clock x,
      let z := ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel (prefixStart t)),
          (prefixControl t,printerControl t),
          bank (sourceEmbed t 16) (blank t 16) (initBank 0 x [])⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _)
      z.l = none ∧ z.stk (.header outH) = word x := by
  obtain ⟨modulus,hm,p,_,s,hs,hr⟩ := V38ReadyField.run t ht x
  obtain ⟨u,hu,c,hprint⟩ := printer_run t x p modulus
  obtain ⟨v,hv,hc⟩ := BitMachineRawSequence.runs
    (V38ReadyField.program t) (CurrentAdditive.V38TablePrinter.Ambient.writerHeaderProgram t 16)
    (prefixStart t) (printerStart t) (prefixControl t) (prefixControl t)
    (printerControl t) ((MultiMove.initial,c),(MultiMove.initial,progCtl))
    (bank (sourceEmbed t 16) (blank t 16) (initBank 0 x []))
    (V38ReadyField.outputBank x p modulus) _ s u
    (by simpa only [prefixStart,prefixControl] using hr) hprint
  refine ⟨v,by unfold clock; omega,?_⟩
  dsimp only
  rw [show ((advance (program t))^[v]) _ = _ from hc]
  constructor
  · rfl
  · dsimp only [TM2.Cfg.stk]
    change bank (headerEmbed t 16) _ _ (.header outH) = _
    have hslot : (headerEmbed t 16) outH = (.header outH : Cell t 16) := rfl
    rw [←hslot,bank_at]
    simp only [ite_true,word,hm,Option.getD_some]

#print axioms printer_run
#print axioms raw_run
end CurrentAdditive.V38PhysicalRenderer
