import CurrentAdditive.V40MidpointRequestRun
import EthInapproximability.CurrentPaper.EntryClockPolyFrame

noncomputable section
namespace CurrentAdditive.V40MidpointRequest

open Paper2 Turing EthInapproximability.CurrentPaper BitMachineEncoding
open EncodedCommunication MinimumRatioContext EntryClockPoly
open V39PublicSchedule

def invokeCap (M : BitMachine.Machine) (L T : ℕ) : ℕ :=
  (2*L+2)+T+(2*(L+T*M.pushBound)+2)+
    (M.stackCount*(L+T*M.pushBound)+M.stackCount+2)+3

theorem invoke_le (M : BitMachine.Machine) (word : List Bool) (t L U : ℕ)
    (hL : word.length ≤ L) (hT : t ≤ U) :
    MachineInvokeFull.uniformBound M word t ≤ invokeCap M L U := by
  unfold MachineInvokeFull.uniformBound invokeCap
  gcongr

def cap (T : ℕ) : ℕ :=
  (2*T+2)+(2*T+2)+(4*T+2)+
    invokeCap FieldM (2*T) ((UnaryBinaryEncoding.coefficient+10)*(2*T+1)^2)+
    invokeCap MatrixM (7*T+3) (3*(7*T+4))+
    (2*(5*T+2)+2)+(2*(4*T+1)+2)+6

syntax "solve_midpoint_poly" : tactic
macro_rules
  | `(tactic| solve_midpoint_poly) => `(tactic| first
      | assumption
      | exact PolyIn.self
      | exact PolyIn.const _
      | (apply PolyIn.add <;> solve_midpoint_poly)
      | (apply PolyIn.mul <;> solve_midpoint_poly)
      | (apply PolyIn.pow <;> solve_midpoint_poly))

theorem cap_poly : PolyIn (fun n : ℕ => n) cap := by
  unfold cap invokeCap
  solve_midpoint_poly

theorem encoded_length (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    (encodeInstance (V40RandomPermittedFamily.instanceWord L k f)).length ≤
      7 * sampleSide L k ^ 2 + 3 := by
  have hp := V40RandomPermittedFamily.side_pos L k
  have hn := V40RandomPermittedFamily.numerator_le_entries L k
  have hB : B L k ≤ sampleSide L k ^ 2 := by unfold V40RandomPermittedFamily.numerator at hn; omega
  have hm : sampleSide L k ≤ sampleSide L k ^ 2 := by nlinarith
  have hdim := EncodedGraph.natField_length_upper (sampleSide L k)
  have hbudget := EncodedGraph.natField_length_upper (B L k)
  simp only [V40RandomPermittedFamily.instanceWord, encodeInstance, List.length_append,
    MatrixMaterialization.rowMajor_length]
  nlinarith

theorem matrix_length (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    (V40RandomPermittedFamily.matrixWord L k f).length ≤ 5 * sampleSide L k ^ 2 + 2 := by
  have hp := V40RandomPermittedFamily.side_pos L k
  have hm : sampleSide L k ≤ sampleSide L k ^ 2 := by nlinarith
  have hdim := EncodedGraph.natField_length_upper (sampleSide L k)
  simp only [V40RandomPermittedFamily.matrixWord, AModel.matrixWord, List.length_append,
    MatrixMaterialization.rowMajor_length]
  nlinarith

theorem public_clock_le (L k : ℕ)
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool) :
    clock (B L k) k (encodeInstance (V40RandomPermittedFamily.instanceWord L k f)) ≤
      cap (sampleSide L k ^ 2) := by
  let T := sampleSide L k ^ 2
  have hn : 2*B L k+k ≤ 2*T := V40RandomPermittedFamily.numerator_le_entries L k
  have hb : B L k ≤ T := by omega
  have hk : k ≤ 2*T := by omega
  have hword := encoded_length L k f
  have hmatrix : (AFront.Projection.matrixPart
      (encodeInstance (V40RandomPermittedFamily.instanceWord L k f))).length ≤ 5*T+2 := by
    rw [AFront.Projection.matrixPart_encodeInstance]
    exact matrix_length L k f
  have hheader : (natField (2*B L k+k)).length ≤ 4*T+1 :=
    (EncodedGraph.natField_length_upper _).trans (by omega)
  have hf : fieldClock (B L k) k ≤
      invokeCap FieldM (2*T) ((UnaryBinaryEncoding.coefficient+10)*(2*T+1)^2) := by
    apply invoke_le
    · simpa using hn
    · gcongr
  have hm : matrixClock (encodeInstance (V40RandomPermittedFamily.instanceWord L k f)) ≤
      invokeCap MatrixM (7*T+3) (3*(7*T+4)) := by
    apply invoke_le
    · exact hword
    · omega
  unfold clock cap
  dsimp only [T] at *
  omega

/-- One pair of constants bounds the physical requester uniformly in every
public schedule and every table payload, using this same table's entries. -/
theorem uniform_clock : ∃ C d : ℕ, ∀ L k
    (f : Fin (sampleSide L k) → Fin (sampleSide L k) → Bool),
    clock (B L k) k (encodeInstance (V40RandomPermittedFamily.instanceWord L k f)) ≤
      C * (CurrentAdditive.Eventual.entries (V40RandomPermittedFamily.matrixWord L k f)+1)^d := by
  obtain ⟨C,d,hC⟩ := cap_poly
  refine ⟨C,d,?_⟩
  intro L k f
  rw [V40RandomPermittedFamily.table_entries]
  exact (public_clock_le L k f).trans (hC _)

#print axioms public_clock_le
#print axioms uniform_clock

end CurrentAdditive.V40MidpointRequest
