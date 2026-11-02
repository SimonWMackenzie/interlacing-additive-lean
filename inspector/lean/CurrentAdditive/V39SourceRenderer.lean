import CurrentAdditive.V39SourceCompiler
import CurrentAdditive.V38ExecutableEntry

/-! Exact semantic renderer for the stronger source. The public field modulus
is the output of the fixed executable search, rather than an existentially
chosen modulus. This file does not assert a physical table-printing clock. -/

namespace CurrentAdditive.V39SourceRenderer

open CurrentAdditive.SmallBias CurrentAdditive.V38Source CurrentAdditive.V38Encoded
open CurrentAdditive.V39SourceCompiler
open CurrentAdditive.FiniteFieldConstructor
open Paper2.YaoSourceCodec Paper2.EncodedSelectedOutput
open Paper2.Yao Workspace.Types.Protocol
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication

set_option maxHeartbeats 1000000

def selectedModulus (b t : ℕ) : ℕ :=
  (TrialSearch.firstPassing (v38FieldDegree b t)).getD 0

/-- A computable instance with the literal selected source, address space,
field list, zero-off-edge entries, row-major table and public threshold. -/
def sourceInstance {t : ℕ} (src : YaoSource t) : Instance :=
  let b := edgeBits src.2.1
  CurrentAdditive.V38Executable.instanceOfTable b t (v38FieldDegree b t)
    (selectedModulus b t) (edgeCount_le_capacity src.2.1) src.2.2

def render (t : ℕ) (bits : List Bool) : List Bool :=
  match decodeAll t bits with
  | some src => encodeInstance (sourceInstance src)
  | none => []

theorem render_encode {t : ℕ} (src : YaoSource t) :
    render t (encode src) = encodeInstance (sourceInstance src) := by
  simp only [render, decodeAll_encode]

theorem render_sourceCode {t : ℕ} (G : GLSourceInput t) (input : List Bool) :
    render t (sourceCode G input) =
      encodeInstance (sourceInstance (selectedSource G input)) :=
  render_encode _

theorem selectedInstance_valid {t : ℕ} (G : GLSourceInput t) (input : List Bool) :
    (sourceInstance (selectedSource G input)).Valid :=
  CurrentAdditive.V38Executable.instanceOfTable_valid
    (selectedSource_nonempty G input) _ _ _ _ _ _

theorem sourceInstance_Dalt {t : ℕ} (src : YaoSource t) (starter : Turn) :
    Dalt starter (ProtocolVerifier.tableGame (sourceInstance src).rows
      (sourceInstance src).cols (sourceInstance src).table) =
      Dalt starter (CurrentAdditive.V38Executable.table
        (edgeBits src.2.1) t (v38FieldDegree (edgeBits src.2.1) t)
        (selectedModulus (edgeBits src.2.1) t)
        (edgeCount_le_capacity src.2.1) src.2.2).matrix := by
  exact congrArg (Dalt starter) (tableGame_eq_matrix _)

/-- The selected deterministic modulus succeeds on every actual source size. -/
theorem selectedModulus_passes {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) (ht : 4 ≤ t) :
    TrialSearch.firstPassing (v38FieldDegree (edgeBits (selectedSource G input).2.1) t) =
      some (selectedModulus (edgeBits (selectedSource G input).2.1) t) := by
  obtain ⟨output, modulus, houtput, hmodulus, hout, hyes, hno⟩ :=
    CurrentAdditive.V38Executable.selected_executable_table_costs G input ht
  simpa only [selectedModulus, hmodulus, Option.getD_some] using hmodulus

/-- Both cost implications hold for the same concrete encoded instance. -/
theorem selectedInstance_costs {t : ℕ} (G : GLSourceInput t)
    (input : List Bool) (ht : 4 ≤ t) :
    let src := selectedSource G input
    let b := edgeBits src.2.1
    let inst := sourceInstance src
    (input ∈ G.L →
      Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table) ≤
        2 * b + 4 * t + 2) ∧
    (input ∉ G.L →
      (2 * b + 4 * t + 2) + 2 * t - 8 ≤
        Dalt .alice (ProtocolVerifier.tableGame inst.rows inst.cols inst.table)) := by
  dsimp only
  obtain ⟨output, modulus, houtput, hmodulus, hout, hyes, hno⟩ :=
    CurrentAdditive.V38Executable.selected_executable_table_costs G input ht
  have hm : selectedModulus (edgeBits (selectedSource G input).2.1) t = modulus := by
    simp only [selectedModulus, hmodulus, Option.getD_some]
  constructor
  · intro hy
    rw [sourceInstance_Dalt, hm]
    exact hyes hy
  · intro hn
    rw [sourceInstance_Dalt, hm]
    exact hno hn

theorem sourceInstance_dimensions {t : ℕ} (src : YaoSource t) :
    (sourceInstance src).rows =
        src.1 * (2 ^ edgeBits src.2.1) ^ (2 ^ (t - 1)) ∧
    (sourceInstance src).cols =
        2 ^ (t - 1) * 2 ^ edgeBits src.2.1 *
          (2 ^ v38FieldDegree (edgeBits src.2.1) t) ^ 2 ∧
    (sourceInstance src).threshold = 2 * edgeBits src.2.1 + 4 * t + 2 := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms render_encode
#print axioms render_sourceCode
#print axioms selectedInstance_valid
#print axioms sourceInstance_Dalt
#print axioms selectedModulus_passes
#print axioms selectedInstance_costs
#print axioms sourceInstance_dimensions

end CurrentAdditive.V39SourceRenderer
