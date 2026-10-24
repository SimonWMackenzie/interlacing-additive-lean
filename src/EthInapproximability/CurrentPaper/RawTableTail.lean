import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.MatrixStage4Codes
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.RawTableWriter22

/-!
# Tail of the raw Stage-4 table producer: row-major writer, then writer22

Lane owner:b-weighted-level-2, unit 2, map item 3 (tail only).

ONE fixed composite controller, for an arbitrary fixed entry program `P`
(label `start`, control `initial`) over `MatrixTableWriter.CellStack K`:

1. the admitted row-major table writer `MatrixTableWriter.program P start
   initial`, lifted onto the table-writer region (`tableSlots`);
2. one handoff;
3. the checked private transfer `RawTableWriter22.program`, lifted by
   `transferSlots`, which copies the reached output word of the table
   writer into cell 22 of an arbitrary `Fin 64` writer bank `W` (initially
   blank there) and preserves every other writer cell.

The only premise about the entry program is the admitted local contract
`MatrixTableWriter.EntryRuns`, i.e. actual bounded runs of the SAME fixed
`P` on the SAME fixed bank for every row/column index. No table word is an
input: the output cell and cell 22 start blank and the word is produced by
the writer. The specialization `raw_table_writer22` targets exactly
`MatrixStage4Codes.rawTable R a s q L nv nb hs family order vectors cap`.

NOT claimed here: any entry program satisfying `EntryRuns` for the raw
Stage-4 entry function (that is the open producer), the production of the
fixed operand bank, or any polynomial majorization of `T`.
-/

namespace EthInapproximability.CurrentPaper.RawTableTail

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4Codes MatrixMaterialization Construction

variable {K : ℕ}

/-- Combined physical bank: the table-writer region (cell bank, three
distinguished cells, and the writer's administrative stacks), the `Fin 64`
writer, and two blank transfer cells. -/
abbrev Stack (K : ℕ) := MatrixTableWriter.Stack K ⊕ (Fin 64 ⊕ Fin 2)

def tableSlots (K : ℕ) : MatrixTableWriter.Stack K ↪ Stack K :=
  ⟨Sum.inl, Sum.inl_injective⟩

def transferMap (K : ℕ) : RawTableWriter22.Stack → Stack K :=
  Sum.elim (fun k => Sum.inr (Sum.inl k))
    (![Sum.inl (Sum.inr MatrixTableWriter.Extra.output),
      Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)] : Fin 3 → Stack K)

theorem transferMap_injective (K : ℕ) : Function.Injective (transferMap K) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · simpa [transferMap] using h
  · fin_cases b <;> simp [transferMap] at h
  · fin_cases a <;> simp [transferMap] at h
  · fin_cases a <;> fin_cases b <;> simp_all [transferMap]

def transferSlots (K : ℕ) : RawTableWriter22.Stack ↪ Stack K :=
  ⟨transferMap K, transferMap_injective K⟩

/-- The whole combined bank, given the table-writer data and the writer. -/
def glob (d : MatrixTableWriter.Data K) (W : Fin 64 → List Bool) :
    Stack K → List Bool :=
  Sum.elim d.contents (Sum.elim W (fun _ => []))

variable {L V : Type*}
variable (P : L → TM2.Stmt (fun _ : MatrixTableWriter.CellStack K => Bool) L V)
  (start : L) (initial : V)

abbrev TableLabel (L : Type*) := MatrixTableWriter.Label L
abbrev TableControl (V : Type*) := MatrixTableWriter.Control V

def tableProgram :
    TableLabel L → TM2.Stmt (fun _ : Stack K => Bool) (TableLabel L) (TableControl V) :=
  fun l => stackStmt (tableSlots K) (MatrixTableWriter.program P start initial l)

def transferProgram :
    BitMachineCopy.Label → TM2.Stmt (fun _ : Stack K => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => stackStmt (transferSlots K) (RawTableWriter22.program l)

abbrev Label (L : Type*) := BitMachineRawSequence.Label (TableLabel L) BitMachineCopy.Label
abbrev Control (V : Type*) := BitMachineRawSequence.Control (TableControl V) (Option Bool)

/-- The single fixed composite controller. -/
def program : Label L → TM2.Stmt (fun _ : Stack K => Bool) (Label L) (Control V) :=
  BitMachineRawSequence.program (tableProgram P start initial) transferProgram
    BitMachineCopy.Label.scan ((initial, none) : TableControl V) (none : Option Bool)

def startLabel : Label L :=
  BitMachineRawSequence.leftLabel (Sum.inr (MatrixTableWriter.Admin.copy
    MatrixTableWriter.Source.rows))

def startControl : Control V := ((initial, none), none)

/-- Start bank: the writer's `ready` data with EMPTY output and a blank
buffer, the arbitrary writer bank `W`, and blank transfer cells. -/
def startBank (bank : Fin K → List Bool) (r c : ℕ) (W : Fin 64 → List Bool) :
    Stack K → List Bool :=
  glob (MatrixTableWriter.ready bank r c 0 0 0 0 [] []) W

/-- Exit bank: the same writer data with the produced word in its output
cell, and the same word in writer cell 22. -/
def exitBank (bank : Fin K → List Bool) (r c : ℕ) (W : Fin 64 → List Bool)
    (word : List Bool) : Stack K → List Bool :=
  glob (MatrixTableWriter.ready bank r c 0 0 0 0 [] word)
    (Function.update W 22 word)

theorem table_bank (d : MatrixTableWriter.Data K) (W : Fin 64 → List Bool)
    (S : MatrixTableWriter.Stack K → List Bool) :
    bank (tableSlots K) (glob d W) S = Sum.elim S (Sum.elim W (fun _ => [])) := by
  funext j
  rcases j with j | j
  · exact bank_at (tableSlots K) (glob d W) S j
  · rw [bank_outside]
    · rfl
    · rintro ⟨k, hk⟩
      cases hk

theorem table_phase (bank : Fin K → List Bool) (r c T : ℕ)
    (entry : ℕ → ℕ → Bool) (f : Fin r → Fin c → Bool)
    (he : ∀ x y, entry x.val y.val = f x y)
    (hcell : MatrixTableWriter.EntryRuns P start initial bank r c T entry)
    (W : Fin 64 → List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound r c T, ∃ v,
      ((advance (tableProgram P start initial))^[t])
        (⟨some (Sum.inr (MatrixTableWriter.Admin.copy MatrixTableWriter.Source.rows)),
          ((initial, none) : TableControl V), startBank bank r c W⟩ :
          TM2.Cfg (fun _ : Stack K => Bool) (TableLabel L) (TableControl V)) =
        ⟨none, v, glob (MatrixTableWriter.ready bank r c 0 0 0 0 [] (rowMajor f)) W⟩ := by
  obtain ⟨t, ht, v, hrun⟩ := MatrixTableWriter.write_rowMajor P start initial
    bank r c T entry f he hcell []
  refine ⟨t, ht, v, ?_⟩
  have hl := BitMachineStackRun.run (tableSlots K) (startBank bank r c W)
    (MatrixTableWriter.program P start initial)
    (MatrixTableWriter.cfg (L := L) (some (Sum.inr (MatrixTableWriter.Admin.copy
      MatrixTableWriter.Source.rows))) ((initial, none) : TableControl V)
      (MatrixTableWriter.ready bank r c 0 0 0 0 [] [])) t
  have hrun' : ((advance (MatrixTableWriter.program P start initial))^[t])
      (MatrixTableWriter.cfg (L := L) (some (Sum.inr (MatrixTableWriter.Admin.copy
        MatrixTableWriter.Source.rows))) ((initial, none) : TableControl V)
        (MatrixTableWriter.ready bank r c 0 0 0 0 [] [])) =
      MatrixTableWriter.cfg (L := L) none v
        (MatrixTableWriter.ready bank r c 0 0 0 0 [] (rowMajor f)) := by
    simpa only [MatrixTableWriter.run, List.append_nil] using hrun
  rw [hrun'] at hl
  have hs : stackCfg (tableSlots K) (startBank bank r c W)
      (MatrixTableWriter.cfg (L := L) (some (Sum.inr (MatrixTableWriter.Admin.copy
        MatrixTableWriter.Source.rows))) ((initial, none) : TableControl V)
        (MatrixTableWriter.ready bank r c 0 0 0 0 [] [])) =
      ⟨some (Sum.inr (MatrixTableWriter.Admin.copy MatrixTableWriter.Source.rows)),
        ((initial, none) : TableControl V), startBank bank r c W⟩ := by
    simp only [stackCfg, MatrixTableWriter.cfg, startBank, table_bank]
    rfl
  have hf : stackCfg (tableSlots K) (startBank bank r c W)
      (MatrixTableWriter.cfg (L := L) none v
        (MatrixTableWriter.ready bank r c 0 0 0 0 [] (rowMajor f))) =
      ⟨none, v, glob (MatrixTableWriter.ready bank r c 0 0 0 0 [] (rowMajor f)) W⟩ := by
    simp only [stackCfg, MatrixTableWriter.cfg, startBank, table_bank]
    rfl
  rw [hs, hf] at hl
  exact hl

theorem finalBank_eq_update (W : Fin 64 → List Bool) (word : List Bool) :
    RawTableWriter22.finalBank W word =
      Function.update (RawTableWriter22.initialBank W word) (Sum.inl 22) word := by
  funext k
  rcases k with k | k
  · by_cases hk : k = 22
    · subst hk
      simp [RawTableWriter22.finalBank]
    · have hne : (Sum.inl k : RawTableWriter22.Stack) ≠ Sum.inl 22 := by
        intro h; exact hk (Sum.inl_injective h)
      rw [Function.update_of_ne hne]
      simp [RawTableWriter22.finalBank, RawTableWriter22.initialBank, hk]
  · rw [Function.update_of_ne (by simp)]
    rfl

theorem transfer_start_bank (d : MatrixTableWriter.Data K)
    (W : Fin 64 → List Bool) :
    bank (transferSlots K) (glob d W) (RawTableWriter22.initialBank W d.output) =
      glob d W := by
  apply bank_eq_self
  intro k
  rcases k with k | k
  · rfl
  · fin_cases k <;> rfl

theorem transfer_final_bank (d : MatrixTableWriter.Data K)
    (W : Fin 64 → List Bool) :
    bank (transferSlots K) (glob d W) (RawTableWriter22.finalBank W d.output) =
      glob d (Function.update W 22 d.output) := by
  rw [finalBank_eq_update, bank_update, transfer_start_bank]
  show Function.update (glob d W) (Sum.inr (Sum.inl 22)) d.output =
    glob d (Function.update W 22 d.output)
  funext j
  rcases j with j | j | j
  · rw [Function.update_of_ne (by simp)]
    rfl
  · by_cases hj : j = 22
    · subst hj
      rw [Function.update_self]
      show d.output = Function.update W 22 d.output 22
      rw [Function.update_self]
    · have hne : (Sum.inr (Sum.inl j) : Stack K) ≠ Sum.inr (Sum.inl 22) := by
        intro h
        exact hj (Sum.inl_injective (Sum.inr_injective h))
      rw [Function.update_of_ne hne]
      show W j = Function.update W 22 d.output j
      rw [Function.update_of_ne hj]
  · rw [Function.update_of_ne (by simp)]
    rfl

theorem transfer_phase (d : MatrixTableWriter.Data K) (W : Fin 64 → List Bool)
    (hblank : W 22 = []) :
    ((advance (transferProgram (K := K)))^[2 * d.output.length + 2])
      (⟨some BitMachineCopy.Label.scan, none, glob d W⟩ :
        TM2.Cfg (fun _ : Stack K => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, glob d (Function.update W 22 d.output)⟩ := by
  have hl := BitMachineStackRun.run (transferSlots K) (glob d W)
    RawTableWriter22.program
    (⟨some BitMachineCopy.Label.scan, none, RawTableWriter22.initialBank W d.output⟩ :
      TM2.Cfg (fun _ : RawTableWriter22.Stack => Bool) BitMachineCopy.Label (Option Bool))
    (2 * d.output.length + 2)
  rw [RawTableWriter22.run W d.output hblank] at hl
  simp only [stackCfg, transfer_start_bank, transfer_final_bank] at hl
  exact hl

/-- Generic tail: from the admitted local entry contract of ONE fixed entry
program, the single composite controller writes the literal row-major word
of `f` and transfers it into writer cell 22; every other writer cell, the
fixed operand bank and the dimension words are retained exactly. -/
theorem tail_run (bank : Fin K → List Bool) (r c T : ℕ)
    (entry : ℕ → ℕ → Bool) (f : Fin r → Fin c → Bool)
    (he : ∀ x y, entry x.val y.val = f x y)
    (hcell : MatrixTableWriter.EntryRuns P start initial bank r c T entry)
    (W : Fin 64 → List Bool) (hblank : W 22 = []) :
    ∃ t ≤ MatrixTableWriter.writerBound r c T + (2 * (r * c) + 2) + 1,
      ((advance (program P start initial))^[t])
        (⟨some startLabel, startControl initial, startBank bank r c W⟩ :
          TM2.Cfg (fun _ : Stack K => Bool) (Label L) (Control V)) =
        ⟨none, ((initial, none), none), exitBank bank r c W (rowMajor f)⟩ := by
  obtain ⟨ta, hta, v, hA⟩ := table_phase P start initial bank r c T entry f he hcell W
  have hB := transfer_phase (K := K)
    (MatrixTableWriter.ready bank r c 0 0 0 0 [] (rowMajor f)) W hblank
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (tableProgram P start initial) transferProgram
    (Sum.inr (MatrixTableWriter.Admin.copy MatrixTableWriter.Source.rows))
    BitMachineCopy.Label.scan ((initial, none) : TableControl V) v
    (none : Option Bool) none _ _ _ ta _ hA hB
  refine ⟨t, ?_, ?_⟩
  · have hlen : (MatrixTableWriter.ready bank r c 0 0 0 0 [] (rowMajor f)).output.length =
        r * c := by
      simp [MatrixTableWriter.ready]
    rw [hlen] at ht
    omega
  · exact hrun

/-- Specialization to the literal raw Stage-4 table: the only remaining
premise is the admitted local entry contract for one fixed entry program
whose entry function agrees with `encodedRaw` on every in-range index. -/
theorem raw_table_writer22 {rx cy : ℕ} (R : Fin rx → Fin cy → Bool)
    (a s q L' nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L' (Fin rx)) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (bank : Fin K → List Bool) (T : ℕ) (entry : ℕ → ℕ → Bool)
    (he : ∀ x y, entry x.val y.val =
      encodedRaw R a s q L' nv nb hs family order vectors cap x y)
    (hcell : MatrixTableWriter.EntryRuns P start initial bank
      (rows s L' nv nb rx) (cols a s q cy) T entry)
    (W : Fin 64 → List Bool) (hblank : W 22 = []) :
    let word := rawTable R a s q L' nv nb hs family order vectors cap
    ∃ t ≤ MatrixTableWriter.writerBound (rows s L' nv nb rx) (cols a s q cy) T +
        (2 * (rows s L' nv nb rx * cols a s q cy) + 2) + 1,
      ((advance (program P start initial))^[t])
        (⟨some startLabel, startControl initial,
          startBank bank (rows s L' nv nb rx) (cols a s q cy) W⟩ :
          TM2.Cfg (fun _ : Stack K => Bool) (Label L) (Control V)) =
        ⟨none, ((initial, none), none),
          exitBank bank (rows s L' nv nb rx) (cols a s q cy) W word⟩ ∧
      exitBank bank (rows s L' nv nb rx) (cols a s q cy) W word
          (Sum.inr (Sum.inl 22)) = word ∧
      (∀ k : Fin 64, k ≠ 22 →
        exitBank bank (rows s L' nv nb rx) (cols a s q cy) W word
          (Sum.inr (Sum.inl k)) = W k) ∧
      (∀ k : Fin K,
        exitBank bank (rows s L' nv nb rx) (cols a s q cy) W word
          (Sum.inl (Sum.inl (Sum.inl k))) = bank k) := by
  intro word
  obtain ⟨t, ht, hrun⟩ := tail_run P start initial bank
    (rows s L' nv nb rx) (cols a s q cy) T entry
    (encodedRaw R a s q L' nv nb hs family order vectors cap) he hcell W hblank
  refine ⟨t, ht, hrun, ?_, ?_, ?_⟩
  · show Function.update W 22 word 22 = word
    exact Function.update_self 22 word W
  · intro k hk
    show Function.update W 22 word k = W k
    exact Function.update_of_ne hk word W
  · intro k
    rfl

#print axioms table_phase
#print axioms transfer_phase
#print axioms tail_run
#print axioms raw_table_writer22

end EthInapproximability.CurrentPaper.RawTableTail
