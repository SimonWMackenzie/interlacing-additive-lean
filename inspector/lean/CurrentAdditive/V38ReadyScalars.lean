import CurrentAdditive.V38SourceFrontValues
import CurrentAdditive.V39ScalarProgram
import CurrentAdditive.V38PublicClock

noncomputable section
namespace CurrentAdditive.V38ReadyScalars

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec
open CurrentAdditive.SmallBias

abbrev labelType {K L V : Type*}
    (_ : L → TM2.Stmt (fun _ : K => Bool) L V) := L
abbrev controlType {K L V : Type*}
    (_ : L → TM2.Stmt (fun _ : K => Bool) L V) := V

def b {t : ℕ} (x : YaoSource t) := paddedEdgeBits x.2.1
def d {t : ℕ} (x : YaoSource t) := v38FieldDegree (b x) t
def H {t : ℕ} (x : YaoSource t) := paddedEdgeCount x.2.1

def frontStart (t : ℕ) : labelType (V38SourceFront.program t) :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      Paper2.YaoHeaderParser.startLabel)))
def frontControl (t : ℕ) : controlType (V38SourceFront.program t) :=
  (V38SourceFront.degreeControl t, V38SourceFront.widthsControl)
def scalarStart (t : ℕ) : labelType (V39ScalarSetup.scalarProgram t) :=
  BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
      BitMachineCopy.Label.scan)))
def scalarControl (t : ℕ) : controlType (V39ScalarSetup.scalarProgram t) :=
  (((V39ScalarSetup.selectorControl, V39ScalarSetup.squareControl),
    V39ScalarSetup.dimensionsControl), V39ScalarSetup.thresholdControl)

def outputBank {t : ℕ} (x : YaoSource t) : Cell t 16 → List Bool :=
  V39ScalarSetup.scalarOutput t x.1 (b x) (H x) (d x)
    (V38SourceFront.outputBank x)

def program (t : ℕ) := BitMachineRawSequence.program
  (V38SourceFront.program t) (V39ScalarSetup.scalarProgram t)
  (scalarStart t) (frontControl t) (scalarControl t)

def clock {t : ℕ} (x : YaoSource t) :=
  V38SourceFront.clock x + V39ScalarSetup.scalarBudget t x.1 (b x) (H x) (d x) + 1

theorem scalar_run (t : ℕ) (x : YaoSource t) :
    ∃ steps ≤ V39ScalarSetup.scalarBudget t x.1 (b x) (H x) (d x),
      ((advance (V39ScalarSetup.scalarProgram t))^[steps])
        (⟨some (scalarStart t), scalarControl t, V38SourceFront.outputBank x⟩ :
          TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, scalarControl t, outputBank x⟩ := by
  obtain ⟨_,hv,hb,hH,_⟩ := V38SourceFront.source_public x
  have hd : V38SourceFront.outputBank x (.degree 3) = List.replicate (d x) true := by
    rw [V38SourceFront.degree_value]
    rw [d, b, V38Clock.degree_exact]
  have hblank (j : Cell t 16)
      (hw : ∀ k : Fin 8, Cell.width k ≠ j)
      (hd : ∀ k : Fin 16, Cell.degree k ≠ j)
      (hs : ∀ k : WStack t 0, Cell.source k ≠ j) :=
    V38SourceFront.blank_value x j hw hd hs
  have hs : ∀ i, V38SourceFront.outputBank x (.selector i) = [] := by
    intro i; exact hblank _ (by intro k h; cases h)
      (by intro k h; cases h) (by intro k h; cases h)
  have hq : ∀ i, V38SourceFront.outputBank x (.square i) = [] := by
    intro i; exact hblank _ (by intro k h; cases h)
      (by intro k h; cases h) (by intro k h; cases h)
  have hm : ∀ i, V38SourceFront.outputBank x (.dimensions i) = [] := by
    intro i; exact hblank _ (by intro k h; cases h)
      (by intro k h; cases h) (by intro k h; cases h)
  have ht : ∀ i, V38SourceFront.outputBank x (.threshold i) = [] := by
    intro i; exact hblank _ (by intro k h; cases h)
      (by intro k h; cases h) (by intro k h; cases h)
  have hc : V38SourceFront.outputBank x (.copyScratch 0) = [] :=
    hblank _ (by intro k h; cases h) (by intro k h; cases h) (by intro k h; cases h)
  simpa only [scalarStart, scalarControl, outputBank, b, H] using
    V39ScalarSetup.physical_scalar_setup t x.1 (b x) (H x) (d x)
      (V38SourceFront.outputBank x) hv hb hH hd hs hq hm ht hc

theorem run (t : ℕ) (ht : 1 ≤ t) (x : YaoSource t) :
    ∃ steps ≤ clock x,
      ((advance (program t))^[steps])
        (⟨some (BitMachineRawSequence.leftLabel (frontStart t)),
          (frontControl t, scalarControl t),
          bank (sourceEmbed t 16) (blank t 16) (initBank 0 x [])⟩ :
            TM2.Cfg (fun _ : Cell t 16 => Bool) _ _) =
        ⟨none, (frontControl t, scalarControl t), outputBank x⟩ := by
  obtain ⟨s,hs,hr⟩ := V38SourceFront.run t ht x
  obtain ⟨u,hu,hrun⟩ := scalar_run t x
  obtain ⟨v,hv,hc⟩ := BitMachineRawSequence.runs
    (V38SourceFront.program t) (V39ScalarSetup.scalarProgram t)
    (frontStart t) (scalarStart t) (frontControl t) (frontControl t)
    (scalarControl t) (scalarControl t)
    (bank (sourceEmbed t 16) (blank t 16) (initBank 0 x []))
    (V38SourceFront.outputBank x) (outputBank x) s u
    (by simpa [frontStart,frontControl] using hr) hrun
  exact ⟨v, by unfold clock; omega, by simpa [program] using hc⟩

theorem output_foreign {t : ℕ} (x : YaoSource t) (j : Cell t 16)
    (hs : ∀ i, j ≠ .selector i) (hq : ∀ i, j ≠ .square i)
    (hm : ∀ i, j ≠ .dimensions i) (ht : ∀ i, j ≠ .threshold i) :
    outputBank x j = V38SourceFront.outputBank x j :=
  V39ScalarSetup.scalarOutput_foreign t x.1 (b x) (H x) (d x)
    (V38SourceFront.outputBank x) j hs hq hm ht

theorem degree_value {t : ℕ} (x : YaoSource t) :
    outputBank x (.degree 3) = List.replicate (d x) true := by
  rw [output_foreign x (.degree 3) (by intro i h; cases h)
    (by intro i h; cases h) (by intro i h; cases h) (by intro i h; cases h)]
  rw [V38SourceFront.degree_value, d, b, V38Clock.degree_exact]

theorem genuine_value {t : ℕ} (x : YaoSource t) :
    outputBank x (.width 5) = List.replicate (v38PositionCount (b x) t) true := by
  rw [output_foreign x (.width 5) (by intro i h; cases h)
    (by intro i h; cases h) (by intro i h; cases h) (by intro i h; cases h)]
  exact V38SourceFront.genuine_width_value x

theorem blank_value {t : ℕ} (x : YaoSource t) (j : Cell t 16)
    (hs : ∀ i, j ≠ .selector i) (hq : ∀ i, j ≠ .square i)
    (hm : ∀ i, j ≠ .dimensions i) (ht : ∀ i, j ≠ .threshold i)
    (hw : ∀ k : Fin 8, Cell.width k ≠ j)
    (hd : ∀ k : Fin 16, Cell.degree k ≠ j)
    (hsrc : ∀ k : WStack t 0, Cell.source k ≠ j) :
    outputBank x j = [] := by
  rw [output_foreign x j hs hq hm ht]
  exact V38SourceFront.blank_value x j hw hd hsrc

#print axioms scalar_run
#print axioms run
end CurrentAdditive.V38ReadyScalars
