import EthInapproximability.CurrentPaper.ExactConstruction
import EthInapproximability.CurrentPaper.ProtocolVerifier
import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Data.Fin.Rev

/-!
# Explicit truth-table materialization

Source: locked v8 `03-exact-hardness.tex`, the polynomial-construction
paragraph, and `B-effectivity-details.tex`, `thm:paper-materialization`.

This module starts with the exact construction. It uses actual finite lists
for the two sampled families and source vectors, explicit numeric input
codecs, and a total evaluator which takes no coloring or support proof.
Correctness assumes the source's proved two-active-items bound.

Resource counters below count payload-list accessor inspections and output
bits written. They do not price arithmetic, rank-loop control or allocation.
The final word-access component is separately compiled to an actual finite
Boolean-stack machine; it does not yet compile the whole matrix evaluator.
-/

namespace EthInapproximability.CurrentPaper.MatrixMaterialization

open ExactConstruction
open Workspace.Types.CommComplexity

/-! ## Sequential finite-list access -/

/-- The second component counts the visited cons/empty cases of this scan. -/
def readList {α : Type*} : List α → ℕ → Option α × ℕ
  | [], _ => (none, 1)
  | x :: _, 0 => (some x, 1)
  | _ :: xs, i + 1 =>
    let r := readList xs i
    (r.1, r.2 + 1)

theorem readList_value {α : Type*} (xs : List α) (i : ℕ) :
    (readList xs i).1 = xs[i]? := by
  induction xs generalizing i with
  | nil => simp [readList]
  | cons x xs ih => cases i <;> simp [readList, ih]

theorem readList_work_le {α : Type*} (xs : List α) (i : ℕ) :
    (readList xs i).2 ≤ xs.length + 1 := by
  induction xs generalizing i with
  | nil => simp [readList]
  | cons x xs ih =>
    cases i with
    | zero => simp [readList]
    | succ i => simpa [readList, Nat.add_assoc] using Nat.add_le_add_right (ih i) 1

/-- Count positive tests while retaining their actual sequential-read cost. -/
def countReads {α : Type*} (test : α → Bool × ℕ) : List α → ℕ × ℕ
  | [] => (0, 0)
  | x :: xs =>
    let t := test x
    let r := countReads test xs
    (r.1 + (if t.1 then 1 else 0), t.2 + r.2)

theorem countReads_value {α : Type*} (test : α → Bool × ℕ) (xs : List α) :
    (countReads test xs).1 = (xs.filter fun x => (test x).1).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [countReads, List.filter_cons]
    cases h : (test x).1 <;> simp [ih, Nat.add_comm]

theorem countReads_work_le {α : Type*} (test : α → Bool × ℕ) (xs : List α)
    (B : ℕ) (hB : ∀ x ∈ xs, (test x).2 ≤ B) :
    (countReads test xs).2 ≤ xs.length * B := by
  induction xs with
  | nil => simp [countReads]
  | cons x xs ih =>
    have h := Nat.add_le_add (hB x (by simp))
      (ih (fun y hy => hB y (by simp [hy])))
    simpa [countReads, Nat.add_mul, Nat.add_comm] using h

/-! ## Stored source and family accessors -/

structure ExactData where
  first : List Bool
  second : List ℕ
  source : List Bool
  deriving Repr

def firstAccessor (data : ExactData) (a N₁ : ℕ) : FirstFamily a N₁ :=
  fun ℓ i => data.first[ℓ.val * (prefixLength a + 3) + i.val]?.getD false

/-- The modulo convention makes malformed numeric payloads total. -/
def secondAccessor (data : ExactData) (a d N₂ : ℕ) : SecondFamily a d N₂ :=
  fun z α => ⟨data.second[z.val * d + α.val]?.getD 0 % width a,
    Nat.mod_lt _ (pow_pos (by omega) _)⟩

def sourceAccessor (data : ExactData) (n d : ℕ) : Fin n → Fin d → Bool :=
  fun i α => data.source[i.val * d + α.val]?.getD false

def sourceRankWithReads (data : ExactData) {n d : ℕ} (i : Fin n) (α : Fin d) : ℕ × ℕ :=
  countReads (fun j : Fin n =>
    if j < i then
      let r := readList data.source (j.val * d + α.val)
      (r.1.getD false, r.2)
    else (false, 0)) (List.finRange n)

theorem sourceRankWithReads_value (data : ExactData) {n d : ℕ}
    (i : Fin n) (α : Fin d) :
    (sourceRankWithReads data i α).1 =
      Construction.activeRank (sourceAccessor data n d) α i := by
  rw [sourceRankWithReads, countReads_value]
  let p : Fin n → Bool := fun j =>
    (if j < i then
      let r := readList data.source (j.val * d + α.val)
      (r.1.getD false, r.2)
    else (false, 0)).1
  change ((List.finRange n).filter p).length = _
  have hn := (List.nodup_finRange n).filter p
  have hcard := List.toFinset_card_of_nodup hn
  rw [← hcard, List.toFinset_filter, List.toFinset_finRange]
  congr 1
  ext j
  simp only [Construction.activeBefore,
    Construction.activeItems, Finset.mem_filter, Finset.mem_univ, true_and,
    readList_value, p, sourceAccessor]
  by_cases h : j < i <;> simp [h, and_comm]

theorem sourceRankWithReads_work_le (data : ExactData) {n d : ℕ}
    (i : Fin n) (α : Fin d) :
    (sourceRankWithReads data i α).2 ≤ n * (data.source.length + 1) := by
  apply (countReads_work_le _ _ (data.source.length + 1) ?_).trans_eq
    (by simp)
  intro j _
  split
  · exact readList_work_le _ _
  · simp

/-! ## Numeric input order -/

/-- Earlier coordinates are more significant in the lexicographic code. -/
def tupleCode (m n : ℕ) : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  (Equiv.arrowCongr (Fin.revPerm) (Equiv.refl _)).trans finFunctionFinEquiv

def rowCode (N₂ n : ℕ) : Rows N₂ n ≃ Fin (4 * N₂ + n) :=
  (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv

def wordCode (a : ℕ) : (Fin a → Bool) ≃ Fin (2 ^ a) :=
  (Equiv.arrowCongr (Equiv.refl _) finTwoEquiv.symm).trans (tupleCode 2 a)

def tailCode : (Fin 3 → Bool) ≃ Fin 8 :=
  wordCode 3

def selectorCode (d N₁ : ℕ) : Selectors d N₁ ≃ Fin ((d * N₁) ^ 4) :=
  (Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv).trans (tupleCode (d * N₁) 4)

def columnCode (d N₁ : ℕ) : Columns d N₁ ≃ Fin (8 * (d * N₁) ^ 4) :=
  (Equiv.prodCongr tailCode (selectorCode d N₁)).trans finProdFinEquiv

@[simp] theorem rowCode_roundtrip (N₂ n : ℕ) (r : Rows N₂ n) :
    (rowCode N₂ n).symm (rowCode N₂ n r) = r := (rowCode N₂ n).symm_apply_apply r

@[simp] theorem columnCode_roundtrip (d N₁ : ℕ) (c : Columns d N₁) :
    (columnCode d N₁).symm (columnCode d N₁ c) = c :=
  (columnCode d N₁).symm_apply_apply c

/-! ## The exact entry evaluator -/

/-- A total entry evaluator. Its second component counts only the list cells
read by the concrete accesses and source-rank scan in the first component. -/
def entryWithReads (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (r : Rows N₂ n) (c : Columns d N₁) : Bool × ℕ :=
  match r with
  | .inl r =>
    let selected := c.2 r.1
    let second := readList data.second (r.2.val * d + selected.1.val)
    let label : Fin (width a) := ⟨second.1.getD 0 % width a,
      Nat.mod_lt _ (pow_pos (by omega) _)⟩
    let first := readList data.first
      (selected.2.val * (prefixLength a + 3) + (duplicateLabel a ha label).val)
    (first.1.getD false, second.2 + first.2)
  | .inr i =>
    if aligned c then
      let active := readList data.source (i.val * d + (c.2 0).1.val)
      if active.1.getD false = true then
        let rank := sourceRankWithReads data i (c.2 0).1
        (if hr : rank.1 < 2 then c.1 ⟨rank.1, by omega⟩ else c.1 2,
          active.2 + rank.2)
      else (c.1 2, active.2)
    else (c.1 2, 0)

theorem entryWithReads_value (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (cap : ∀ α, (Construction.activeItems (sourceAccessor data n d) α).card ≤ 2)
    (r : Rows N₂ n) (c : Columns d N₁) :
    (entryWithReads data ha r c).1 =
      matrix ha (firstAccessor data a N₁) (secondAccessor data a d N₂)
        (sourceAccessor data n d) cap r c := by
  cases r with
  | inl r =>
    simp [entryWithReads, matrix, thirdMatrix, secondMatrix, duplicatedFirstMatrix,
      firstMatrix, firstAccessor, secondAccessor, prefixCoordinate, readList_value]
  | inr i =>
    by_cases hal : aligned c
    · by_cases hi : sourceAccessor data n d i (c.2 0).1 = true
      · have hr : Construction.activeRank (sourceAccessor data n d) (c.2 0).1 i < 2 :=
          (Construction.activeRank_lt_card _ _ _ hi).trans_le (cap _)
        have hi' : data.source[i.val * d + (c.2 0).1.val]?.getD false = true := hi
        simp only [entryWithReads, matrix, vectorEntry, if_pos hal,
          readList_value, if_pos hi', dif_pos hi, sourceRankWithReads_value,
          dif_pos hr]
        rfl
      · simp [entryWithReads, matrix, vectorEntry, hal, readList_value,
          sourceAccessor] at hi ⊢
        simp [hi]
    · simp [entryWithReads, matrix, vectorEntry, hal]

/-- A bound on the actual list-cell reads, without a supplied cost oracle. -/
def entryReadBound (data : ExactData) (n : ℕ) : ℕ :=
  data.first.length + data.second.length + 2 + (n + 1) * (data.source.length + 1)

theorem entryWithReads_work_le (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (r : Rows N₂ n) (c : Columns d N₁) :
    (entryWithReads data ha r c).2 ≤ entryReadBound data n := by
  cases r with
  | inl r =>
    unfold entryWithReads entryReadBound
    dsimp only
    have h₂ := readList_work_le data.second (r.2.val * d + (c.2 r.1).1.val)
    have h₁ := readList_work_le data.first
      ((c.2 r.1).2.val * (prefixLength a + 3) +
        (duplicateLabel a ha ⟨(readList data.second
          (r.2.val * d + (c.2 r.1).1.val)).1.getD 0 % width a,
            Nat.mod_lt _ (pow_pos (by omega) _)⟩).val)
    omega
  | inr i =>
    simp only [entryWithReads]
    split
    · have hread := readList_work_le data.source (i.val * d + (c.2 0).1.val)
      split
      · have hrank := sourceRankWithReads_work_le data i (c.2 0).1
        dsimp only
        unfold entryReadBound
        nlinarith
      · dsimp only
        unfold entryReadBound
        nlinarith
    · simp [entryReadBound]

def encodedEntryWithReads (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (r : Fin (4 * N₂ + n)) (c : Fin (8 * (d * N₁) ^ 4)) : Bool × ℕ :=
  entryWithReads data ha ((rowCode N₂ n).symm r) ((columnCode d N₁).symm c)

def encodedMatrix (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) :
    Fin (4 * N₂ + n) → Fin (8 * (d * N₁) ^ 4) → Bool :=
  fun r c => (encodedEntryWithReads data ha r c).1

theorem encodedMatrix_correct (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (cap : ∀ α, (Construction.activeItems (sourceAccessor data n d) α).card ≤ 2)
    (r : Rows N₂ n) (c : Columns d N₁) :
    encodedMatrix data ha (rowCode N₂ n r) (columnCode d N₁ c) =
      matrix ha (firstAccessor data a N₁) (secondAccessor data a d N₂)
        (sourceAccessor data n d) cap r c := by
  simp only [encodedMatrix, encodedEntryWithReads, Equiv.symm_apply_apply]
  exact entryWithReads_value data ha cap r c

/-! ## Row-major lists -/

def rowMajor {α : Type*} {rows cols : ℕ} (f : Fin rows → Fin cols → α) : List α :=
  List.ofFn fun k : Fin (rows * cols) =>
    f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] theorem rowMajor_length {α : Type*} {rows cols : ℕ}
    (f : Fin rows → Fin cols → α) : (rowMajor f).length = rows * cols := by
  simp [rowMajor]

theorem rowMajor_entry {α : Type*} {rows cols : ℕ}
    (f : Fin rows → Fin cols → α) (r : Fin rows) (c : Fin cols) :
    (rowMajor f)[r.val * cols + c.val]? = some (f r c) := by
  have hidx : r.val * cols + c.val < rows * cols := by
    have := r.isLt
    have := c.isLt
    nlinarith
  simp only [rowMajor, List.getElem?_ofFn, dif_pos hidx]
  have he : (⟨r.val * cols + c.val, hidx⟩ : Fin (rows * cols)) =
      finProdFinEquiv (r, c) := by
    apply Fin.ext
    simp only [finProdFinEquiv_apply_val]
    ring
  rw [he, Equiv.symm_apply_apply]

def table (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) : List Bool :=
  rowMajor (encodedMatrix (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha)

@[simp] theorem table_length (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) :
    (table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha).length =
      (4 * N₂ + n) * (8 * (d * N₁) ^ 4) := rowMajor_length _

theorem table_entry (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (r : Fin (4 * N₂ + n)) (c : Fin (8 * (d * N₁) ^ 4)) :
    (table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha)[
      r.val * (8 * (d * N₁) ^ 4) + c.val]? =
      some (encodedMatrix data ha r c) := rowMajor_entry _ r c

theorem tableGame_eq (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) :
    ProtocolVerifier.tableGame (4 * N₂ + n) (8 * (d * N₁) ^ 4)
      (table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha) =
      encodedMatrix data ha := by
  funext r c
  simp [ProtocolVerifier.tableGame, ProtocolVerifier.tableEntry, table_entry]

theorem rowMajor_map {α β : Type*} {rows cols : ℕ}
    (g : α → β) (f : Fin rows → Fin cols → α) :
    (rowMajor f).map g = rowMajor (fun r c => g (f r c)) := by
  simp [rowMajor, List.map_ofFn, Function.comp_def]

/-- The actual table writer paired with the reads incurred at all entries. -/
def materializeWithReads (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) :
    List Bool × ℕ :=
  let entries := rowMajor
    (encodedEntryWithReads (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha)
  (entries.map Prod.fst, (entries.map Prod.snd).sum)

theorem materializeWithReads_value (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) :
    (materializeWithReads (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha).1 =
      table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha := by
  simp only [materializeWithReads, rowMajor_map]
  rfl

theorem sum_le_length_mul (xs : List ℕ) (B : ℕ) (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons, List.length_cons]
    nlinarith

theorem materializeWithReads_work_le (data : ExactData) {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) :
    (materializeWithReads (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha).2 ≤
      (4 * N₂ + n) * (8 * (d * N₁) ^ 4) * entryReadBound data n := by
  simp only [materializeWithReads, rowMajor_map]
  apply (sum_le_length_mul _ (entryReadBound data n) ?_).trans_eq
    (by rw [rowMajor_length])
  intro x hx
  simp only [rowMajor, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact entryWithReads_work_le data ha _ _

theorem materializeWithReads_written_bits (data : ExactData) {a d N₁ N₂ n : ℕ}
    (ha : 2 ≤ a) :
    (materializeWithReads (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha).1.length =
      (4 * N₂ + n) * (8 * (d * N₁) ^ 4) := by
  rw [materializeWithReads_value, table_length]

/-! ## Literal stored families and their correspondence -/

/-- Store every labelled family member and source vector, including repeated
tuples. No image/set conversion removes duplicate sampled labels. -/
def store {a d N₁ N₂ n : ℕ} (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) : ExactData :=
  ⟨rowMajor C₁, rowMajor (fun z α => (C₂ z α).val), rowMajor v⟩

@[simp] theorem store_firstAccessor {a d N₁ N₂ n : ℕ} (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    firstAccessor (store C₁ C₂ v) a N₁ = C₁ := by
  funext ℓ i
  simp [firstAccessor, store, rowMajor_entry]

@[simp] theorem store_secondAccessor {a d N₁ N₂ n : ℕ} (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    secondAccessor (store C₁ C₂ v) a d N₂ = C₂ := by
  funext z α
  apply Fin.ext
  simp [secondAccessor, store, rowMajor_entry, Nat.mod_eq_of_lt (C₂ z α).isLt]

@[simp] theorem store_sourceAccessor {a d N₁ N₂ n : ℕ} (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    sourceAccessor (store C₁ C₂ v) n d = v := by
  funext i α
  simp [sourceAccessor, store, rowMajor_entry]

theorem store_lengths {a d N₁ N₂ n : ℕ} (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    (store C₁ C₂ v).first.length = N₁ * (prefixLength a + 3) ∧
    (store C₁ C₂ v).second.length = N₂ * d ∧
    (store C₁ C₂ v).source.length = n * d := by
  simp [store]

theorem stored_table_entry {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2)
    (r : Rows N₂ n) (c : Columns d N₁) :
    (table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) (store C₁ C₂ v) ha)[
        (rowCode N₂ n r).val * (8 * (d * N₁) ^ 4) + (columnCode d N₁ c).val]? =
      some (matrix ha C₁ C₂ v cap r c) := by
  rw [table_entry]
  have hcap : ∀ α, (Construction.activeItems
      (sourceAccessor (store C₁ C₂ v) n d) α).card ≤ 2 := by
    simpa only [store_sourceAccessor] using cap
  have h := encodedMatrix_correct (store C₁ C₂ v) ha hcap r c
  simpa only [store_firstAccessor, store_secondAccessor, store_sourceAccessor] using
    congrArg some h

theorem D_encodedMatrix (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (cap : ∀ α, (Construction.activeItems (sourceAccessor data n d) α).card ≤ 2) :
    D (encodedMatrix (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha) =
      D (matrix ha (firstAccessor data a N₁) (secondAccessor data a d N₂)
        (sourceAccessor data n d) cap) := by
  have he : encodedMatrix (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha =
      fun r c => matrix ha (firstAccessor data a N₁) (secondAccessor data a d N₂)
        (sourceAccessor data n d) cap ((rowCode N₂ n).symm r)
          ((columnCode d N₁).symm c) := by
    funext r c
    exact entryWithReads_value data ha cap _ _
  rw [he]
  exact ParameterizedNP.DenseStageFourOpening.D_forget_eq _
    (rowCode N₂ n).symm (columnCode d N₁).symm (rowCode N₂ n) (columnCode d N₁)
    (rowCode N₂ n).symm_apply_apply (columnCode d N₁).symm_apply_apply

theorem D_stored_tableGame {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    D (ProtocolVerifier.tableGame (4 * N₂ + n) (8 * (d * N₁) ^ 4)
      (table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) (store C₁ C₂ v) ha)) =
      D (matrix ha C₁ C₂ v cap) := by
  rw [tableGame_eq]
  have he : encodedMatrix (d := d) (N₁ := N₁) (N₂ := N₂) (n := n)
      (store C₁ C₂ v) ha = fun r c =>
        matrix ha C₁ C₂ v cap ((rowCode N₂ n).symm r) ((columnCode d N₁).symm c) := by
    funext r c
    have h := stored_table_entry ha C₁ C₂ v cap
      ((rowCode N₂ n).symm r) ((columnCode d N₁).symm c)
    simpa only [Equiv.apply_symm_apply, table_entry, Option.some.injEq] using h
  rw [he]
  exact ParameterizedNP.DenseStageFourOpening.D_forget_eq _
    (rowCode N₂ n).symm (columnCode d N₁).symm (rowCode N₂ n) (columnCode d N₁)
    (rowCode N₂ n).symm_apply_apply (columnCode d N₁).symm_apply_apply

theorem stored_reads_le {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    (materializeWithReads (d := d) (N₁ := N₁) (N₂ := N₂) (n := n)
      (store C₁ C₂ v) ha).2 ≤
      (4 * N₂ + n) * (8 * (d * N₁) ^ 4) *
        (N₁ * (prefixLength a + 3) + N₂ * d + 2 + (n + 1) * (n * d + 1)) := by
  simpa only [entryReadBound, store, rowMajor_length] using
    materializeWithReads_work_le (d := d) (N₁ := N₁) (N₂ := N₂) (n := n)
      (store C₁ C₂ v) ha

theorem table_length_polynomial (data : ExactData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (hN₁ : N₁ ≤ d ^ 300) (hN₂ : N₂ ≤ d ^ 100) :
    (table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) data ha).length ≤
      8 * (4 * d ^ 100 + n) * d ^ 1204 := by
  simpa only [table_length, ExactConstruction.card_rows, ExactConstruction.card_columns]
    using ExactConstruction.table_size_polynomial d N₁ N₂ n hN₁ hN₂

/-! ## All-Boolean payload encoding -/

/-- Dimensions are supplied separately. Every second-family label occupies
exactly `a` bits, with its first bit most significant. -/
structure ExactBitData where
  first : List Bool
  second : List Bool
  source : List Bool
  deriving Repr

def storeBits {a d N₁ N₂ n : ℕ} (C₁ : FirstFamily a N₁)
    (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) : ExactBitData :=
  ⟨rowMajor C₁,
    rowMajor (fun k : Fin (N₂ * d) =>
      (wordCode a).symm (C₂ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)),
    rowMajor v⟩

/-- A total decoder for arbitrary finite Boolean payloads. Missing bits use
zero; well-shaped encodings have the exact correspondence proved below. -/
def decodeBits (data : ExactBitData) (a d N₂ : ℕ) : ExactData :=
  ⟨data.first,
    rowMajor (fun z : Fin N₂ => fun α : Fin d =>
      (wordCode a (fun j =>
        data.second[(z.val * d + α.val) * a + j.val]?.getD false)).val),
    data.source⟩

theorem storeBits_second_entry {a d N₁ N₂ n : ℕ}
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool)
    (z : Fin N₂) (α : Fin d) (j : Fin a) :
    (storeBits C₁ C₂ v).second[(z.val * d + α.val) * a + j.val]? =
      some ((wordCode a).symm (C₂ z α) j) := by
  have h := rowMajor_entry (fun k : Fin (N₂ * d) =>
    (wordCode a).symm (C₂ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2))
      (finProdFinEquiv (z, α)) j
  simpa only [storeBits, finProdFinEquiv_apply_val, Equiv.symm_apply_apply,
    Nat.mul_comm, Nat.add_comm] using h

theorem decodeBits_storeBits {a d N₁ N₂ n : ℕ}
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    decodeBits (storeBits C₁ C₂ v) a d N₂ = store C₁ C₂ v := by
  have hf (z : Fin N₂) (α : Fin d) :
      (fun j : Fin a =>
        (storeBits C₁ C₂ v).second[(z.val * d + α.val) * a + j.val]?.getD false) =
        (wordCode a).symm (C₂ z α) := by
    funext j
    rw [storeBits_second_entry]
    rfl
  unfold decodeBits
  simp only [hf, Equiv.apply_symm_apply]
  rfl

theorem storeBits_lengths {a d N₁ N₂ n : ℕ}
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    (storeBits C₁ C₂ v).first.length = N₁ * (prefixLength a + 3) ∧
    (storeBits C₁ C₂ v).second.length = N₂ * d * a ∧
    (storeBits C₁ C₂ v).source.length = n * d := by
  simp [storeBits]

def bitTable (data : ExactBitData) {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a) : List Bool :=
  table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) (decodeBits data a d N₂) ha

theorem bitTable_storeBits {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool) :
    bitTable (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) (storeBits C₁ C₂ v) ha =
      table (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) (store C₁ C₂ v) ha := by
  simp only [bitTable, decodeBits_storeBits]

theorem D_bitTable_storeBits {a d N₁ N₂ n : ℕ} (ha : 2 ≤ a)
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool)
    (cap : ∀ α, (Construction.activeItems v α).card ≤ 2) :
    D (ProtocolVerifier.tableGame (4 * N₂ + n) (8 * (d * N₁) ^ 4)
      (bitTable (d := d) (N₁ := N₁) (N₂ := N₂) (n := n) (storeBits C₁ C₂ v) ha)) =
        D (matrix ha C₁ C₂ v cap) := by
  rw [bitTable_storeBits]
  exact D_stored_tableGame ha C₁ C₂ v cap

/-! ## Literal Boolean-stack access to a fixed-width word

The header consists of a unary offset and a unary width, each terminated by
`false`. The machine returns the indicated word, using zero for missing bits.
All four stacks contain only Booleans; the control state has three values.
No offset, width, or family label is stored in an unbounded control register.
-/

namespace WordSlice

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | countOffset | countWidth | skip | take | clear | reverse
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label (Option Bool)
  | .countOffset => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false)
        (push 1 (fun _ => true) (goto (fun _ => .countOffset)))
        (goto (fun _ => .countWidth)))
  | .countWidth => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false)
        (push 2 (fun _ => true) (goto (fun _ => .countWidth)))
        (goto (fun _ => .skip)))
  | .skip => pop 1 (fun _ b => b)
      (branch Option.isSome
        (pop 0 (fun s _ => s) (goto (fun _ => .skip)))
        (goto (fun _ => .take)))
  | .take => pop 2 (fun _ b => b)
      (branch Option.isSome
        (pop 0 (fun _ b => b) (push 3 (fun b => b.getD false)
          (goto (fun _ => .take))))
        (goto (fun _ => .clear)))
  | .clear => pop 0 (fun _ b => b)
      (branch Option.isSome (goto (fun _ => .clear)) (goto (fun _ => .reverse)))
  | .reverse => pop 3 (fun _ b => b)
      (branch Option.isSome
        (push 0 (fun b => b.getD false) (goto (fun _ => .reverse)))
        (load (fun _ => none) halt))

def stackContents (q offset width saved : List Bool) : Fin 4 → List Bool :=
  fun k => if k = 0 then q else if k = 1 then offset else if k = 2 then width else saved

@[simp] private theorem stack_zero (q o w b : List Bool) : stackContents q o w b 0 = q := rfl
@[simp] private theorem stack_one (q o w b : List Bool) : stackContents q o w b 1 = o := rfl
@[simp] private theorem stack_two (q o w b : List Bool) : stackContents q o w b 2 = w := rfl
@[simp] private theorem stack_three (q o w b : List Bool) : stackContents q o w b 3 = b := rfl

def cfg (l : Option Label) (s : Option Bool) (q offset width saved : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) Label (Option Bool) :=
  ⟨l, s, stackContents q offset width saved⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 4 => Bool) Label (Option Bool)) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label (Option Bool)}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label (Option Bool)}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_offset_true (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countOffset) s (true :: q) o w b) =
      some (cfg (some .countOffset) (some true) q (true :: o) w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_offset_false (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countOffset) s (false :: q) o w b) =
      some (cfg (some .countWidth) (some false) q o w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_width_true (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countWidth) s (true :: q) o w b) =
      some (cfg (some .countWidth) (some true) q o (true :: w) b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_width_false (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .countWidth) s (false :: q) o w b) =
      some (cfg (some .skip) (some false) q o w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_skip_cons (s : Option Bool) (q o w b : List Bool) :
    TM2.step program (cfg (some .skip) s q (true :: o) w b) =
      some (cfg (some .skip) (some true) q.tail o w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_skip_nil (s : Option Bool) (q w b : List Bool) :
    TM2.step program (cfg (some .skip) s q [] w b) =
      some (cfg (some .take) none q [] w b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_take_cons (s : Option Bool) (q w b : List Bool) :
    TM2.step program (cfg (some .take) s q [] (true :: w) b) =
      some (cfg (some .take) q.head? q.tail [] w (q.head?.getD false :: b)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_take_nil (s : Option Bool) (q b : List Bool) :
    TM2.step program (cfg (some .take) s q [] [] b) =
      some (cfg (some .clear) none q [] [] b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_clear_cons (s : Option Bool) (x : Bool) (q b : List Bool) :
    TM2.step program (cfg (some .clear) s (x :: q) [] [] b) =
      some (cfg (some .clear) (some x) q [] [] b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_clear_nil (s : Option Bool) (b : List Bool) :
    TM2.step program (cfg (some .clear) s [] [] [] b) =
      some (cfg (some .reverse) none [] [] [] b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_reverse_cons (s : Option Bool) (x : Bool) (q b : List Bool) :
    TM2.step program (cfg (some .reverse) s q [] [] (x :: b)) =
      some (cfg (some .reverse) (some x) (x :: q) [] [] b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

private theorem step_reverse_nil (s : Option Bool) (q : List Bool) :
    TM2.step program (cfg (some .reverse) s q [] [] []) =
      some (cfg none none q [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

def padded : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, q => q.head?.getD false :: padded n q.tail

@[simp] theorem padded_length (n : ℕ) (q : List Bool) : (padded n q).length = n := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp [padded, ih]

private theorem offset_correct (i m : ℕ) (s : Option Bool) (q w b : List Bool) :
    run (i + 1) (cfg (some .countOffset) s
      (List.replicate i true ++ false :: q) (List.replicate m true) w b) =
      cfg (some .countWidth) (some false) q (List.replicate (i + m) true) w b := by
  induction i generalizing m s with
  | zero => simpa using run_succ (step_offset_false s q (List.replicate m true) w b) 0
  | succ i ih =>
      rw [List.replicate_succ, List.cons_append]
      rw [run_succ (step_offset_true s _ _ _ _)]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using
        ih (m + 1) (some true)

private theorem width_correct (i m : ℕ) (s : Option Bool) (q o b : List Bool) :
    run (i + 1) (cfg (some .countWidth) s
      (List.replicate i true ++ false :: q) o (List.replicate m true) b) =
      cfg (some .skip) (some false) q o (List.replicate (i + m) true) b := by
  induction i generalizing m s with
  | zero => simpa using run_succ (step_width_false s q o (List.replicate m true) b) 0
  | succ i ih =>
      rw [List.replicate_succ, List.cons_append]
      rw [run_succ (step_width_true s _ _ _ _)]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using
        ih (m + 1) (some true)

private theorem skip_correct (i : ℕ) (s : Option Bool) (q w b : List Bool) :
    run (i + 1) (cfg (some .skip) s q (List.replicate i true) w b) =
      cfg (some .take) none (q.drop i) [] w b := by
  induction i generalizing q s with
  | zero => simpa using run_succ (step_skip_nil s q w b) 0
  | succ i ih =>
      rw [List.replicate_succ, run_succ (step_skip_cons s _ _ _ _)]
      simpa only [List.drop_tail] using ih (some true) q.tail

private theorem take_correct (i : ℕ) (s : Option Bool) (q b : List Bool) :
    run (i + 1) (cfg (some .take) s q [] (List.replicate i true) b) =
      cfg (some .clear) none (q.drop i) [] [] ((padded i q).reverse ++ b) := by
  induction i generalizing q s b with
  | zero => simpa [padded] using run_succ (step_take_nil s q b) 0
  | succ i ih =>
      rw [List.replicate_succ, run_succ (step_take_cons s _ _ _)]
      simpa [padded, List.reverse_cons, List.append_assoc, List.drop_tail] using
        ih q.head? q.tail (q.head?.getD false :: b)

private theorem clear_correct (s : Option Bool) (q b : List Bool) :
    run (q.length + 1) (cfg (some .clear) s q [] [] b) =
      cfg (some .reverse) none [] [] [] b := by
  induction q generalizing s with
  | nil => exact run_succ (step_clear_nil s b) 0
  | cons x q ih =>
      rw [List.length_cons, run_succ (step_clear_cons s x q b)]
      exact ih (some x)

private theorem reverse_correct (s : Option Bool) (q b : List Bool) :
    run (b.length + 1) (cfg (some .reverse) s q [] [] b) =
      cfg none none (b.reverse ++ q) [] [] [] := by
  induction b generalizing s q with
  | nil => simpa using run_succ (step_reverse_nil s q) 0
  | cons x b ih =>
      rw [List.length_cons, run_succ (step_reverse_cons s x q b)]
      simpa [List.reverse_cons, List.append_assoc] using ih (some x) (x :: q)

theorem padded_eq_ofFn (n : ℕ) (q : List Bool) :
    padded n q = List.ofFn (fun j : Fin n => q[j.val]?.getD false) := by
  induction n generalizing q with
  | zero => simp [padded]
  | succ n ih =>
      rw [padded, List.ofFn_succ, ih]
      congr 1
      · cases q <;> rfl
      · congr 1
        funext j
        simp

def encodeInput (offset width : ℕ) (q : List Bool) : List Bool :=
  List.replicate offset true ++ false :: (List.replicate width true ++ false :: q)

def exactTime (offset width : ℕ) (q : List Bool) : ℕ :=
  (offset + 1) + (width + 1) + (offset + 1) + (width + 1) +
    ((q.drop offset).drop width).length + 1 + (width + 1)

theorem run_correct (offset width : ℕ) (q : List Bool) :
    run (exactTime offset width q)
      (cfg (some .countOffset) none (encodeInput offset width q) [] [] []) =
      cfg none none (padded width (q.drop offset)) [] [] [] := by
  have h₁ := offset_correct offset 0 none
    (List.replicate width true ++ false :: q) [] []
  simp only [Nat.add_zero, List.replicate_zero] at h₁
  have h₂ := width_correct width 0 (some false) q (List.replicate offset true) []
  simp only [Nat.add_zero, List.replicate_zero] at h₂
  have h₃ := skip_correct offset (some false) q (List.replicate width true) []
  have h₄ := take_correct width none (q.drop offset) []
  simp only [List.append_nil] at h₄
  have h₅ := clear_correct none ((q.drop offset).drop width)
    (padded width (q.drop offset)).reverse
  have h₆ := reverse_correct none [] (padded width (q.drop offset)).reverse
  simp only [List.length_reverse, padded_length, List.reverse_reverse, List.append_nil] at h₆
  have h₁₂ := (run_add h₁ (width + 1)).trans h₂
  have h₁₂₃ := (run_add h₁₂ (offset + 1)).trans h₃
  have h₁₂₃₄ := (run_add h₁₂₃ (width + 1)).trans h₄
  have h₁₂₃₄₅ := (run_add h₁₂₃₄ (((q.drop offset).drop width).length + 1)).trans h₅
  have h := (run_add h₁₂₃₄₅ (width + 1)).trans h₆
  simpa only [exactTime, encodeInput, Nat.add_assoc] using h

theorem exactTime_le (offset width : ℕ) (q : List Bool) :
    exactTime offset width q ≤ 3 * (encodeInput offset width q).length := by
  have hlen : ((q.drop offset).drop width).length ≤ q.length :=
    by simp only [List.length_drop]; omega
  simp only [exactTime, encodeInput, List.length_append, List.length_replicate,
    List.length_cons]
  omega

/-- One fixed machine for every offset, width, and payload. Only the fixed
six labels and three-valued control are renamed to numeric finite types. -/
noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 4) 0 .countOffset (none : Option Bool) program

theorem bitMachine_outputs (offset width : ℕ) (q : List Bool) :
    bitMachine.OutputsWithin (encodeInput offset width q) (padded width (q.drop offset))
      (3 * (encodeInput offset width q).length) := by
  have hi : rawInit (0 : Fin 4) .countOffset (none : Option Bool)
      (encodeInput offset width q) =
      cfg (some .countOffset) none (encodeInput offset width q) [] [] [] := by
    unfold rawInit cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  have hrun := run_correct offset width q
  apply outputsWithin_of_raw_run (0 : Fin 4) 0 .countOffset (none : Option Bool) program
    (encodeInput offset width q) (padded width (q.drop offset))
    (exactTime offset width q) _ (exactTime_le offset width q)
  · change (run (exactTime offset width q) _).l = none
    rw [hi, hrun]
    rfl
  · change (run (exactTime offset width q) _).stk 0 = _
    rw [hi, hrun]
    rfl

theorem stored_word_outputs {a d N₁ N₂ n : ℕ}
    (C₁ : FirstFamily a N₁) (C₂ : SecondFamily a d N₂) (v : Fin n → Fin d → Bool)
    (z : Fin N₂) (α : Fin d) :
    bitMachine.OutputsWithin
      (encodeInput ((z.val * d + α.val) * a) a (storeBits C₁ C₂ v).second)
      (List.ofFn ((wordCode a).symm (C₂ z α)))
      (3 * (encodeInput ((z.val * d + α.val) * a) a (storeBits C₁ C₂ v).second).length) := by
  have he : padded a ((storeBits C₁ C₂ v).second.drop ((z.val * d + α.val) * a)) =
      List.ofFn ((wordCode a).symm (C₂ z α)) := by
    rw [padded_eq_ofFn]
    congr 1
    funext j
    simp only [List.getElem?_drop, storeBits_second_entry, Option.getD_some]
  simpa only [he] using
    bitMachine_outputs ((z.val * d + α.val) * a) a (storeBits C₁ C₂ v).second

end WordSlice

/-- Tiny exact-gadget check: both active ranks, the inactive tail, and an
extra duplicated coordinate label all execute through the stored data. -/
theorem stored_entry_regression :
    let data : ExactData := ⟨[false, true, true, false, true], [3], [true, true, false]⟩
    let c : Columns 1 1 := (fun j => j.val != 1, fun _ => (0, 0))
    (entryWithReads data (by decide : 2 ≤ 2) (.inr (0 : Fin 3) : Rows 1 3) c).1 = true ∧
    (entryWithReads data (by decide : 2 ≤ 2) (.inr (1 : Fin 3) : Rows 1 3) c).1 = false ∧
    (entryWithReads data (by decide : 2 ≤ 2) (.inr (2 : Fin 3) : Rows 1 3) c).1 = true ∧
    (entryWithReads data (by decide : 2 ≤ 2) (.inl (0, 0) : Rows 1 3) c).1 = true := by
  decide

theorem empty_payload_regression :
    let data : ExactData := ⟨[], [], []⟩
    (table (a := 2) (d := 0) (N₁ := 0) (N₂ := 0) (n := 0) data (by decide)).length = 0 ∧
    (readList data.first 100).1 = none ∧ (readList data.first 100).2 = 1 := by
  decide

end EthInapproximability.CurrentPaper.MatrixMaterialization
