import CurrentAdditive.V38ReadyScalars
import CurrentAdditive.V38AmbientFullBank

noncomputable section
namespace CurrentAdditive.V38ReadyField

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec
open CurrentAdditive.SmallBias
open CurrentAdditive.V38ReadyScalars (labelType controlType b d H)
open CurrentAdditive.V38AmbientFieldInstall (producerEmbed producerSlot sourceControl)
open CurrentAdditive.FieldSearchCompletion

def prefixControl (t : ℕ) : controlType (V38ReadyScalars.program t) :=
  (V38ReadyScalars.frontControl t, V38ReadyScalars.scalarControl t)
def prefixStart (t : ℕ) : labelType (V38ReadyScalars.program t) :=
  BitMachineRawSequence.leftLabel (V38ReadyScalars.frontStart t)
def fieldControl (t : ℕ) : controlType (V38AmbientFieldFull.fullProgram t) :=
  ((none, none), (sourceControl, none))
def fieldStart (t : ℕ) : labelType (V38AmbientFieldFull.fullProgram t) :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)

def outputBank {t : ℕ} (x : YaoSource t) (p modulus : ℕ) :=
  V38AmbientFieldFull.finalBank (b x) t p modulus (V38ReadyScalars.outputBank x)
def program (t : ℕ) := BitMachineRawSequence.program
  (V38ReadyScalars.program t) (V38AmbientFieldFull.fullProgram t)
  (fieldStart t) (prefixControl t) (fieldControl t)
def clock {t : ℕ} (x : YaoSource t) :=
  V38ReadyScalars.clock x + V38AmbientFieldFull.fullClock (b x) t + 1

theorem producer_blank (t : ℕ) (x : YaoSource t) :
    ∀ i : V38FieldPad.Stack, V38ReadyScalars.outputBank x (producerEmbed t i) = [] := by
  intro i
  have hf : V38ReadyScalars.outputBank x (producerEmbed t i) =
      V38SourceFront.outputBank x (producerEmbed t i) := by
    apply V38ReadyScalars.output_foreign
    all_goals
      intro k hk
      cases i with
      | inl j => cases j <;> simp [producerEmbed,producerSlot,fieldCombinedEmbed] at hk
      | inr j => cases j <;> simp [producerEmbed,producerSlot] at hk
  rw [hf]
  cases i with
  | inl j =>
    cases j with
    | inl k =>
      exact V38SourceFront.blank_value x (.fieldInit k)
        (by intro i h; cases h) (by intro i h; cases h) (by intro i h; cases h)
    | inr k =>
      exact V38SourceFront.blank_value x (.field k)
        (by intro i h; cases h) (by intro i h; cases h) (by intro i h; cases h)
  | inr j =>
    cases j <;>
      exact V38SourceFront.blank_value x _
        (by intro i h; cases h) (by intro i h; cases h) (by intro i h; cases h)

theorem scratch_blank (t : ℕ) (x : YaoSource t) :
    V38ReadyScalars.outputBank x (.copyScratch 0) = [] := by
  apply V38ReadyScalars.blank_value <;> intro i h <;> cases h

theorem run (t : ℕ) (ht : 4 ≤ t) (x : YaoSource t) :
    ∃ modulus, TrialSearch.firstPassing (d x) = some modulus ∧
      ∃ p ≤ 100*(v38FieldTarget (b x) t)^5,
      ∃ steps ≤ clock x,
        ((advance (program t))^[steps])
          (⟨some (BitMachineRawSequence.leftLabel (prefixStart t)),
            (prefixControl t, fieldControl t),
            bank (sourceEmbed t 16) (blank t 16) (initBank 0 x [])⟩ :
              TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
          ⟨none, (prefixControl t, fieldControl t), outputBank x p modulus⟩ := by
  obtain ⟨s,hs,hr⟩ := V38ReadyScalars.run t (by omega) x
  obtain ⟨modulus,hm,p,hp,u,hu,hfield⟩ :=
    V38AmbientFieldFull.physical_full_bank (b x) t ht
      (V38ReadyScalars.outputBank x) (V38ReadyScalars.degree_value x)
      (V38ReadyScalars.genuine_value x) (producer_blank t x) (scratch_blank t x)
  obtain ⟨v,hv,hc⟩ := BitMachineRawSequence.runs
    (V38ReadyScalars.program t) (V38AmbientFieldFull.fullProgram t)
    (prefixStart t) (fieldStart t) (prefixControl t) (prefixControl t)
    (fieldControl t) (fieldControl t)
    (bank (sourceEmbed t 16) (blank t 16) (initBank 0 x []))
    (V38ReadyScalars.outputBank x) (outputBank x p modulus) s u
    (by simpa [prefixControl,prefixStart] using hr)
    (by simpa [fieldControl,fieldStart,outputBank] using hfield)
  exact ⟨modulus,hm,p,hp,v,by unfold clock; omega,by simpa [program] using hc⟩

theorem outside_producer (t : ℕ) (j : Cell t 16)
    (hF : ∀ k, j ≠ .field k) (hI : ∀ k, j ≠ .fieldInit k)
    (h1 : j ≠ .copyScratch 1) (h2 : j ≠ .copyScratch 2) :
    ¬ ∃ i : V38FieldPad.Stack, producerEmbed t i = j := by
  rintro ⟨i,hi⟩
  cases i with
  | inl k =>
    cases k with
    | inl k => exact hI k (by simpa [producerEmbed,producerSlot,fieldCombinedEmbed] using hi.symm)
    | inr k => exact hF k (by simpa [producerEmbed,producerSlot,fieldCombinedEmbed] using hi.symm)
  | inr k =>
    cases k with
    | false => exact h1 (by simpa [producerEmbed,producerSlot] using hi.symm)
    | true => exact h2 (by simpa [producerEmbed,producerSlot] using hi.symm)

theorem output_foreign {t : ℕ} (x : YaoSource t) (p modulus : ℕ) (j : Cell t 16)
    (hj : ¬ ∃ i : V38FieldPad.Stack, producerEmbed t i = j) :
    outputBank x p modulus j = V38ReadyScalars.outputBank x j :=
  V38AmbientFieldFull.finalBank_foreign (b x) t p modulus _ j hj

#print axioms producer_blank
#print axioms scratch_blank
#print axioms run
end CurrentAdditive.V38ReadyField
