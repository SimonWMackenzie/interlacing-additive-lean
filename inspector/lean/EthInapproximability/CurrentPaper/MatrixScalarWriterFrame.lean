import EthInapproximability.CurrentPaper.MatrixScalarParameters
import EthInapproximability.CurrentPaper.MatrixTableRuntime

/-! # Physical scalar registers inside the exact table writer

The scalar program's unary inputs and outputs are placed at the real table
writer locations. The first-family, second-family and source arrays are
foreign to this stage and remain unchanged. A single additional persistent
stack holds `n`, which is not needed by the table writer and is preserved
rather than silently discarded.
-/

namespace EthInapproximability.CurrentPaper.MatrixScalarWriterFrame

open Turing BitMachineEncoding

abbrev WriterStack := MatrixTableWriter.Stack 51 ⊕ Unit

/-- Scalar slots 14 and 15 feed the writer's row/column-size registers;
slots 6--8 and 13 feed the persistent cell bank. Slot 4 retains `n` in the
one additional stack outside the writer. -/
def scalarSlots : Fin 22 ↪ WriterStack :=
  ⟨![.inl (.inl (.inl 24)), .inl (.inl (.inl 25)),
     .inl (.inl (.inl 3)), .inl (.inl (.inl 1)), .inr (),
     .inl (.inl (.inl 5)), .inl (.inl (.inl 26)), .inl (.inl (.inl 27)),
     .inl (.inl (.inl 2)), .inl (.inl (.inl 6)), .inl (.inl (.inl 7)),
     .inl (.inl (.inl 8)), .inl (.inl (.inl 9)), .inl (.inl (.inl 0)),
     .inl (.inr .rows), .inl (.inr .cols), .inl (.inl (.inl 31)),
     .inl (.inl (.inl 10)), .inl (.inl (.inl 11)), .inl (.inl (.inl 12)),
     .inl (.inl (.inl 13)), .inl (.inl (.inl 14))], by decide⟩

def post (a d N₁ N₂ n : ℕ) (data : MatrixMaterialization.ExactBitData) :
    MatrixTableWriter.Data 51 :=
  MatrixTableWriter.ready (MatrixTableRuntime.persistentBank a d N₁ N₂ data)
    (4 * N₂ + n) (8 * (d * N₁) ^ 4) 0 0 0 0 [] []

def postFrame (a d N₁ N₂ n : ℕ) (data : MatrixMaterialization.ExactBitData) :
    WriterStack → List Bool :=
  Sum.elim (post a d N₁ N₂ n data).contents (fun _ => List.replicate n true)

def foreign (a d N₁ N₂ n : ℕ) (data : MatrixMaterialization.ExactBitData) :
    WriterStack → List Bool := postFrame a d N₁ N₂ n data

/-- Only the selected slots need checking: the embedding frames all others.
The width identity requires the paper's alphabet condition `a ≥ 2`. -/
theorem output_frame {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (data : MatrixMaterialization.ExactBitData) :
    BitMachineStackEmbedding.bank scalarSlots (foreign a d N₁ N₂ n data)
      (MatrixScalarParameters.outputBank a d N₁ N₂ n) =
        postFrame a d N₁ N₂ n data := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro k
  have hpow : 2 ≤ 2^a := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) ha
    norm_num at h ⊢
    omega
  fin_cases k <;> try rfl
  change List.replicate (2^a+1) true =
    List.replicate (ExactConstruction.prefixLength a+3) true
  congr 1
  simp only [ExactConstruction.prefixLength, Construction.qOne]
  omega

def scalarProgram (l : MatrixScalarParameters.Label) :
    TM2.Stmt (fun _ : WriterStack => Bool)
      MatrixScalarParameters.Label MatrixScalarParameters.Control :=
  BitMachineStackEmbedding.stmt scalarSlots id id id none
    (MatrixScalarParameters.program l)

/-- The actual scalar controller runs at its mapped writer locations, while
all foreign cells, including the three literal payload arrays, are framed. -/
theorem scalar_run (a d N₁ N₂ n : ℕ)
    (data : MatrixMaterialization.ExactBitData) :
    ∃ t ≤ 200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1),
      ((advance scalarProgram)^[t])
        (BitMachineStackEmbedding.cfg scalarSlots (foreign a d N₁ N₂ n data) id id none
          (⟨some (.inl (.inr false)), MatrixScalarParameters.idle,
            MatrixScalarParameters.inputBank a d N₁ N₂ n⟩ :
            MatrixScalarParameters.Config)) =
        BitMachineStackEmbedding.cfg scalarSlots (foreign a d N₁ N₂ n data) id id none
          (⟨none, MatrixScalarParameters.idle,
            MatrixScalarParameters.outputBank a d N₁ N₂ n⟩ :
            MatrixScalarParameters.Config) := by
  obtain ⟨t, ht, he⟩ := MatrixScalarParameters.scalar_run_bound a d N₁ N₂ n
  change ((advance MatrixScalarParameters.program)^[t]) _ = _ at he
  have hh : (((advance MatrixScalarParameters.program)^[t])
      (⟨some (.inl (.inr false)), MatrixScalarParameters.idle,
        MatrixScalarParameters.inputBank a d N₁ N₂ n⟩ :
        MatrixScalarParameters.Config)).l = none := by rw [he]
  obtain ⟨u, hu, hr⟩ := BitMachineStackEmbedding.outputs scalarSlots
    (foreign a d N₁ N₂ n data)
    id id id (fun _ => rfl) none MatrixScalarParameters.program scalarProgram
    (fun _ => rfl)
    (⟨some (.inl (.inr false)), MatrixScalarParameters.idle,
      MatrixScalarParameters.inputBank a d N₁ N₂ n⟩ :
      MatrixScalarParameters.Config) t hh
  rw [he] at hr
  exact ⟨u, hu.trans ht, hr⟩

noncomputable def preFrame (a d N₁ N₂ n : ℕ)
    (data : MatrixMaterialization.ExactBitData) :
    WriterStack → List Bool :=
  BitMachineStackEmbedding.bank scalarSlots (foreign a d N₁ N₂ n data)
    (MatrixScalarParameters.inputBank a d N₁ N₂ n)

/-- A computable, fully explicit starting bank: only the five unary scalar
inputs and three literal payload arrays are nonempty. -/
def rawInput (a d N₁ N₂ n : ℕ) (data : MatrixMaterialization.ExactBitData) :
    WriterStack → List Bool
  | .inl (.inl (.inl k)) =>
      match k.val with
      | 1 => List.replicate N₂ true
      | 3 => List.replicate N₁ true
      | 24 => List.replicate a true
      | 25 => List.replicate d true
      | 28 => data.first
      | 29 => data.second
      | 30 => data.source
      | _ => []
  | .inl (.inl (.inr _)) => []
  | .inr () => List.replicate n true
  | .inl (.inr _) => []

set_option maxHeartbeats 120000 in
-- The finite 22-slot/61-slot frame check branches over literal stack indices.
theorem preFrame_eq_rawInput (a d N₁ N₂ n : ℕ)
    (data : MatrixMaterialization.ExactBitData) :
    preFrame a d N₁ N₂ n data = rawInput a d N₁ N₂ n data := by
  have hlocal (k : Fin 22) :
      MatrixScalarParameters.inputBank a d N₁ N₂ n k =
        rawInput a d N₁ N₂ n data (scalarSlots k) := by
    fin_cases k <;> rfl
  have hforeign (j : WriterStack) (h : ¬ ∃ k, scalarSlots k = j) :
      foreign a d N₁ N₂ n data j = rawInput a d N₁ N₂ n data j := by
    cases j with
    | inl j =>
        cases j with
        | inl j =>
            cases j with
            | inl j => fin_cases j <;> first | rfl | exact (h (by decide)).elim
            | inr j => fin_cases j <;> rfl
        | inr j => cases j <;> first | rfl | exact (h (by decide)).elim
    | inr j => cases j; rfl
  funext j
  by_cases h : ∃ k, scalarSlots k = j
  · obtain ⟨k, rfl⟩ := h
    rw [preFrame, BitMachineStackEmbedding.bank_at]
    exact hlocal k
  · rw [preFrame, BitMachineStackEmbedding.bank_outside scalarSlots
      (foreign a d N₁ N₂ n data) _ j h]
    exact hforeign j h

theorem scalar_run_post {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (data : MatrixMaterialization.ExactBitData) :
    ∃ t ≤ 200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1),
      ((advance scalarProgram)^[t])
        (⟨some (.inl (.inr false)), MatrixScalarParameters.idle,
          preFrame a d N₁ N₂ n data⟩ :
          TM2.Cfg (fun _ : WriterStack => Bool) _ _) =
        ⟨none, MatrixScalarParameters.idle, postFrame a d N₁ N₂ n data⟩ := by
  obtain ⟨t, ht, hr⟩ := scalar_run a d N₁ N₂ n data
  refine ⟨t, ht, ?_⟩
  simpa only [BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg,
    BitMachineInline.cfg, preFrame, output_frame ha] using hr

/-- The same run starts with a computable literal bank rather than the
proof-only overlay used internally to establish framing. -/
theorem scalar_run_raw {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (data : MatrixMaterialization.ExactBitData) :
    ∃ t ≤ 200 * (2^a+a+d+N₁+N₂+n+(d*N₁)^4+1),
      ((advance scalarProgram)^[t])
        (⟨some (.inl (.inr false)), MatrixScalarParameters.idle,
          rawInput a d N₁ N₂ n data⟩ :
          TM2.Cfg (fun _ : WriterStack => Bool) _ _) =
        ⟨none, MatrixScalarParameters.idle, postFrame a d N₁ N₂ n data⟩ := by
  obtain ⟨t, ht, hr⟩ := scalar_run_post ha data
  exact ⟨t, ht, by simpa only [preFrame_eq_rawInput] using hr⟩

end EthInapproximability.CurrentPaper.MatrixScalarWriterFrame
