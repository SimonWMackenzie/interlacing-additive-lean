import CurrentAdditive.GaussTypedPacket
import CurrentAdditive.GaussMatrixClock
import CurrentAdditive.EntryStep

/-!
The semantic trace for a literal Gauss control loop.  The state contains the
whole materialized matrix, the next row and column, and the pivot list already
written by the loop.  `traceStep` is the exact transition that the physical
controller must implement; the theorem below checks both the matrix and the
ordered pivot list against `echelonMaterialized`.
-/

namespace CurrentAdditive.GaussControlTrace

open CurrentAdditive.SequentialTotality
open CurrentAdditive.MaterializedGauss
open CurrentAdditive.EliminationEntryBounds

structure State (m k : Nat) where
  B : Fin m → Fin k → ℚ
  r : Nat
  c : Nat
  pivots : List (Fin m × Fin k)

def step {m k : Nat} (s : State m k) : State m k :=
  if hr : s.r < m then
    if hc : s.c < k then
      let rf : Fin m := ⟨s.r, hr⟩
      let cf : Fin k := ⟨s.c, hc⟩
      match pivotTyped s.B s.r cf with
      | none => ⟨s.B, s.r, s.c + 1, s.pivots⟩
      | some i =>
        ⟨materialize (clearTyped (swapTyped s.B rf i) rf cf),
          s.r + 1, s.c + 1, s.pivots ++ [(rf, cf)]⟩
    else s
  else s

def initial {m k : Nat} (A : Fin m → Fin k → ℚ) : State m k :=
  ⟨A, 0, 0, []⟩

def after {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) : State m k :=
  (step^[t]) (initial A)

def forget {m k : Nat} (s : State m k) : CursorState m k :=
  ⟨s.B, s.r, s.c⟩

theorem forget_step {m k : Nat} (s : State m k) :
    forget (step s) = cursorStep (forget s) := by
  rcases s with ⟨B, r, c, ps⟩
  by_cases hr : r < m
  · by_cases hc : c < k
    · cases hp : pivotTyped B r ⟨c, hc⟩ <;>
        simp [forget, step, cursorStep, hr, hc, hp]
    · simp [forget, step, cursorStep, hr, hc]
  · simp [forget, step, cursorStep, hr]

theorem after_cursor {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    forget (after A t) = cursorAfter A t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [after, cursorAfter, Function.iterate_succ_apply'] at ih ⊢
      rw [forget_step]
      exact congrArg cursorStep ih

/-- Exact semantic target for every prefix of the physical loop. -/
theorem after_matrix {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    (after A t).B = (echelonMaterialized A 0 0 t).1 := by
  have h := congrArg CursorState.B (after_cursor A t)
  change (after A t).B = (cursorAfter A t).B at h
  rw [h]
  exact cursorAfter_eq_prefix A t

private theorem terminal_row {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r c t : Nat) (hr : ¬ r < m) :
    echelonMaterialized B r c t = (B, []) := by
  cases t with
  | zero => rfl
  | succ t => simp [echelonMaterialized, hr]

private theorem terminal_col {m k : Nat} (B : Fin m → Fin k → ℚ)
    (r c t : Nat) (hc : ¬ c < k) :
    echelonMaterialized B r c t = (B, []) := by
  cases t with
  | zero => rfl
  | succ t =>
      by_cases hr : r < m <;> simp [echelonMaterialized, hr, hc]

theorem run_spec {m k : Nat} (s : State m k) (t : Nat) :
    let out := (step^[t]) s
    let ref := echelonMaterialized s.B s.r s.c t
    out.B = ref.1 ∧ out.pivots = s.pivots ++ ref.2 := by
  induction t generalizing s with
  | zero => simp [echelonMaterialized]
  | succ t ih =>
      simp only [Function.iterate_succ_apply]
      by_cases hr : s.r < m
      · by_cases hc : s.c < k
        · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ with
          | none =>
              have h := ih (step s)
              simpa [step, echelonMaterialized, hr, hc, hp] using h
          | some i =>
              have h := ih (step s)
              simpa [step, echelonMaterialized, hr, hc, hp,
                List.append_assoc] using h
        · have h := ih (step s)
          simp [step, hr, hc, terminal_col s.B s.r s.c t hc] at h
          simpa [step, echelonMaterialized, hr, hc] using h
      · have h := ih (step s)
        simp [step, hr, terminal_row s.B s.r s.c t hr] at h
        simpa [step, echelonMaterialized, hr] using h

theorem after_exact {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    (after A t).B = (echelonMaterialized A 0 0 t).1 ∧
    (after A t).pivots = (echelonMaterialized A 0 0 t).2 := by
  simpa [after, initial] using run_spec (initial A) t

theorem after_k {m k : Nat} (A : Fin m → Fin k → ℚ) :
    (after A k).B = (echelonMaterialized A 0 0 k).1 ∧
    (after A k).pivots = (echelonMaterialized A 0 0 k).2 :=
  after_exact A k

/-- Concrete output layout for the full-support loop: a fixed four-field
bank containing the complete matrix, unary row and column cursors, and the
ordered list of unary pivot pairs.  The physical controller must write this
exact word after `k` transitions. -/
def pivotPacket {m k : Nat} (p : Fin m × Fin k) : List Bool :=
  EthInapproximability.CurrentPaper.BitMachineBankCodec.encode
    (fun j : Fin 2 => if j = 0 then List.replicate p.1.val true
      else List.replicate p.2.val true)

def pivotsPacket {m k : Nat} (ps : List (Fin m × Fin k)) : List Bool :=
  EthInapproximability.CurrentPaper.SourceListEncoding.encode
    (ps.map pivotPacket)

def stateBank {m k : Nat} (s : State m k) :
    EthInapproximability.CurrentPaper.BitMachineBankCodec.Bank 4 :=
  fun j =>
    if j = 0 then CurrentAdditive.GaussPhysical.encodeTypedMatrix s.B
    else if j = 1 then List.replicate s.r true
    else if j = 2 then List.replicate s.c true
    else pivotsPacket s.pivots

def statePacket {m k : Nat} (s : State m k) : List Bool :=
  EthInapproximability.CurrentPaper.BitMachineBankCodec.encode (stateBank s)

theorem statePacket_length {m k : Nat} (s : State m k) :
    (statePacket s).length =
      2 * ((CurrentAdditive.GaussPhysical.encodeTypedMatrix s.B).length +
        s.r + s.c + (pivotsPacket s.pivots).length) + 4 := by
  rw [statePacket,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encode_length]
  simp [stateBank, Fin.sum_univ_succ, Nat.add_assoc]

theorem pivotPacket_length {m k : Nat} (p : Fin m × Fin k) :
    (pivotPacket p).length = 2 * (p.1.val + p.2.val) + 2 := by
  rw [pivotPacket,
    EthInapproximability.CurrentPaper.BitMachineBankCodec.encode_length]
  simp [Fin.sum_univ_succ]

theorem pivotsPacket_length_le {m k : Nat}
    (ps : List (Fin m × Fin k)) :
    (pivotsPacket ps).length ≤
      3 * ps.length * (2 * (m + k) + 3) + 1 := by
  apply EthInapproximability.CurrentPaper.SourceListEncoding.encode_map_length_le
  intro p hp
  rw [pivotPacket_length]
  have hm := p.1.isLt
  have hk := p.2.isLt
  omega

theorem step_size {m k : Nat} (s : State m k) :
    (step s).r ≤ s.r + 1 ∧
    (step s).c ≤ s.c + 1 ∧
    (step s).pivots.length ≤ s.pivots.length + 1 := by
  by_cases hr : s.r < m
  · by_cases hc : s.c < k
    · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ <;>
        simp [step, hr, hc, hp]
    · simp [step, hr, hc]
  · simp [step, hr]

theorem after_size {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    (after A t).r ≤ t ∧ (after A t).c ≤ t ∧
    (after A t).pivots.length ≤ t := by
  induction t with
  | zero => simp [after, initial]
  | succ t ih =>
      simp only [after, Function.iterate_succ_apply'] at ih ⊢
      have hs := step_size ((step^[t]) (initial A))
      omega

theorem step_pivotCount {m k : Nat} (s : State m k)
    (h : s.r = s.pivots.length) :
    (step s).r = (step s).pivots.length := by
  by_cases hr : s.r < m
  · by_cases hc : s.c < k
    · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ <;>
        simp [step, hr, hc, hp] <;> omega
    · simpa [step, hr, hc] using h
  · simpa [step, hr] using h

theorem after_pivotCount {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    (after A t).r = (after A t).pivots.length := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [after, Function.iterate_succ_apply'] at ih ⊢
      exact step_pivotCount _ ih

theorem step_row_le {m k : Nat} (s : State m k) (h : s.r ≤ m) :
    (step s).r ≤ m := by
  by_cases hr : s.r < m
  · by_cases hc : s.c < k
    · cases hp : pivotTyped s.B s.r ⟨s.c, hc⟩ <;>
        simp [step, hr, hc, hp]; omega
    · simpa [step, hr, hc] using h
  · simpa [step, hr] using h

theorem after_row_le {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) :
    (after A t).r ≤ m := by
  induction t with
  | zero => simp [after, initial]
  | succ t ih =>
      simp only [after, Function.iterate_succ_apply'] at ih ⊢
      exact step_row_le _ ih

/-- Whole-state byte bound for the actual zero-one input, with every
column retained.  No truncation to `m+1` columns is used. -/
theorem actual_statePacket_length {m k : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (t : Nat) (ht : t ≤ k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    (statePacket (after Aq t)).length ≤
      2 * (3 * m * (3 * k *
        (4 * ((m + 3) * (m + 1) ^ 2 + 1) + 6) + 2) + 1 +
        2 * t + (3 * t * (2 * (m + k) + 3) + 1)) + 4 := by
  let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
  have hm := CurrentAdditive.GaussPhysical.actualGauss_matrix_packet_length
    A h01 t ht
  have hs := after_size Aq t
  have hp := pivotsPacket_length_le (after Aq t).pivots
  dsimp only at hm
  have hmeq := (after_cursor Aq t)
  have hB := congrArg CursorState.B hmeq
  change (after Aq t).B = (cursorAfter Aq t).B at hB
  have hpl : (pivotsPacket (after Aq t).pivots).length ≤
      3 * t * (2 * (m + k) + 3) + 1 := by
    calc
      _ ≤ 3 * (after Aq t).pivots.length * (2 * (m + k) + 3) + 1 := hp
      _ ≤ 3 * t * (2 * (m + k) + 3) + 1 := by gcongr; exact hs.2.2
  subst Aq
  dsimp only
  rw [statePacket_length]
  rw [hB]
  omega

/-- The explicit storage polynomial after charging the intended full support
bound `k ≤ m*M`.  This uses the complete matrix with `k` columns. -/
def fullSupportStatePoly (m M : Nat) : Nat :=
  2 * (3 * m * (3 * (m * M) *
    (4 * ((m + 3) * (m + 1) ^ 2 + 1) + 6) + 2) + 1 +
    2 * (m * M) +
    (3 * (m * M) * (2 * (m + m * M) + 3) + 1)) + 4

theorem actual_statePacket_full_support {m k M : Nat}
    (A : Matrix (Fin m) (Fin k) ℤ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hk : k ≤ m * M) (t : Nat) (ht : t ≤ k) :
    let Aq : Fin m → Fin k → ℚ := fun i j => (A i j : ℚ)
    (statePacket (after Aq t)).length ≤ fullSupportStatePoly m M := by
  have hs := actual_statePacket_length A h01 t ht
  dsimp only at hs ⊢
  calc
    _ ≤ 2 * (3 * m * (3 * k *
      (4 * ((m + 3) * (m + 1) ^ 2 + 1) + 6) + 2) + 1 +
        2 * t + (3 * t * (2 * (m + k) + 3) + 1)) + 4 := hs
    _ ≤ fullSupportStatePoly m M := by
      unfold fullSupportStatePoly
      gcongr
      all_goals omega

#print axioms after_k
#print axioms statePacket_length
#print axioms actual_statePacket_full_support

end CurrentAdditive.GaussControlTrace
