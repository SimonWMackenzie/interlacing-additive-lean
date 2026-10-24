import Paper2.YaoMaterializationBounds

/-!
Scratch-only operational fragment for frozen v12 `yao:entry`. The counters below
are constructed by recursion, rather than attached to a separate evaluator.
The source is prepared once as lists of ordered vertices. This is a structural
visitation model, not a binary-machine running-time claim.
-/

namespace Paper2.YaoOperationalEntryScratch

open Paper2.YaoLookup
open Paper2.YaoLowerBound.Materialization

/-- Visit exactly the cons cells traversed by a zero-based list lookup. -/
def readAt {A : Type*} : List A → ℕ → Option A × ℕ
  | [], _ => (none, 0)
  | x :: _, 0 => (some x, 1)
  | _ :: xs, i + 1 =>
      let result := readAt xs i
      (result.1, result.2 + 1)

theorem readAt_value {A : Type*} (xs : List A) (i : ℕ) :
    (readAt xs i).1 = xs[i]? := by
  induction xs generalizing i with
  | nil => simp [readAt]
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [readAt] using ih i

theorem readAt_visits_le {A : Type*} (xs : List A) (i : ℕ) :
    (readAt xs i).2 ≤ xs.length := by
  induction xs generalizing i with
  | nil => simp [readAt]
  | cons x xs ih =>
      cases i with
      | zero => simp [readAt]
      | succ i => simpa [readAt] using Nat.succ_le_succ (ih i)

/-- A tape access runs the recursive list reader on the owner's literal
serialized Boolean tape. The result includes the generated visit count. -/
def readTapeOperational {t b lambda : ℕ}
    (bits : SerializedTape t b lambda) (p : Paper2.YaoLowerBound.TapePosition t b lambda) :
    Option Bool × ℕ :=
  readAt bits.val (tapeIndex t b lambda p).val

theorem readTapeOperational_value {t b lambda : ℕ}
    (bits : SerializedTape t b lambda) (p : Paper2.YaoLowerBound.TapePosition t b lambda) :
    (readTapeOperational bits p).1 = some (readTape t b lambda bits p) := by
  simp [readTapeOperational, readAt_value, readTape, List.Vector.get]

theorem readTapeOperational_visits_le {t b lambda : ℕ}
    (bits : SerializedTape t b lambda) (p : Paper2.YaoLowerBound.TapePosition t b lambda) :
    (readTapeOperational bits p).2 ≤ Paper2.YaoLowerBound.tapeBitCount t b lambda := by
  simpa [readTapeOperational, bits.property] using
    readAt_visits_le bits.val (tapeIndex t b lambda p).val

/-- Build a list in numerical `Fin` order; one recursive visit is charged
for each emitted value. The source evaluator receives this prepared list. -/
def prepareVector {A : Type*} : (n : ℕ) → (Fin n → A) → List A × ℕ
  | 0, _ => ([], 0)
  | n + 1, f =>
      let rest := prepareVector n (fun i => f i.succ)
      (f 0 :: rest.1, rest.2 + 1)

theorem prepareVector_value {A : Type*} (n : ℕ) (f : Fin n → A) :
    (prepareVector n f).1 = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prepareVector, List.ofFn_succ, ih]

theorem prepareVector_visits {A : Type*} (n : ℕ) (f : Fin n → A) :
    (prepareVector n f).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [prepareVector, ih]

/-- Prepare every ordered edge once, charging one outer cons and every
vertex cons. This accepts the owner's typed indexed source; binary parsing
of an external source encoding is a separate obligation. -/
def prepareSource {v K : ℕ} : (e : ℕ) →
    (Fin e → Fin K ↪ Fin v) → List (List (Fin v)) × ℕ
  | 0, _ => ([], 0)
  | e + 1, edges =>
      let head := prepareVector K (edges 0)
      let tail := prepareSource e (fun i => edges i.succ)
      (head.1 :: tail.1, head.2 + tail.2 + 1)

theorem prepareSource_value {v K : ℕ} (e : ℕ)
    (edges : Fin e → Fin K ↪ Fin v) :
    (prepareSource e edges).1 =
      List.ofFn (fun i => List.ofFn (edges i : Fin K → Fin v)) := by
  induction e with
  | zero => rfl
  | succ e ih => simp [prepareSource, List.ofFn_succ, prepareVector_value, ih]

theorem prepareSource_visits {v K : ℕ} (e : ℕ)
    (edges : Fin e → Fin K ↪ Fin v) :
    (prepareSource e edges).2 = e * (K + 1) := by
  induction e with
  | zero => simp [prepareSource]
  | succ e ih =>
      simp [prepareSource, prepareVector_visits, ih, Nat.succ_mul]
      omega

theorem prepareSource_length {v K : ℕ} (e : ℕ)
    (edges : Fin e → Fin K ↪ Fin v) :
    (prepareSource e edges).1.length = e := by
  rw [prepareSource_value]
  exact List.length_ofFn

theorem prepareSource_read_real {v K e : ℕ}
    (edges : Fin e → Fin K ↪ Fin v) (a : Fin e) :
    (readAt (prepareSource e edges).1 a.val).1 =
      some (List.ofFn (edges a : Fin K → Fin v)) := by
  rw [readAt_value, prepareSource_value]
  simp

theorem prepareSource_read_unused {v K e : ℕ}
    (edges : Fin e → Fin K ↪ Fin v) (a : ℕ) (ha : e ≤ a) :
    (readAt (prepareSource e edges).1 a).1 = none := by
  rw [readAt_value, prepareSource_value]
  simp [ha]

theorem prepareSource_inner_length {v K : ℕ} (e : ℕ)
    (edges : Fin e → Fin K ↪ Fin v) :
    ∀ edge ∈ (prepareSource e edges).1, edge.length = K := by
  induction e with
  | zero => simp [prepareSource]
  | succ e ih =>
      intro edge hmem
      simp only [prepareSource, List.mem_cons] at hmem
      rcases hmem with heq | htail
      · rw [heq, prepareVector_value]
        exact List.length_ofFn
      · exact ih _ edge htail

/-- Scan an ordered edge until its first matching vertex, counting every
tested cons cell. Zero means absence; positive values are one-based. -/
def scanPosition {V : Type*} [DecidableEq V] : List V → V → ℕ × ℕ
  | [], _ => (0, 0)
  | x :: xs, v =>
      if x = v then (1, 1) else
        let result := scanPosition xs v
        (if result.1 = 0 then 0 else result.1 + 1, result.2 + 1)

theorem scanPosition_visits_le {V : Type*} [DecidableEq V]
    (xs : List V) (v : V) : (scanPosition xs v).2 ≤ xs.length := by
  induction xs with
  | nil => simp [scanPosition]
  | cons x xs ih =>
      by_cases h : x = v
      · simp [scanPosition, h]
      · simpa [scanPosition, h] using Nat.succ_le_succ ih

theorem scanPosition_ofFn_hit {v K : ℕ}
    (edge : Fin K ↪ Fin v) (i : Fin K) :
    (scanPosition (List.ofFn (edge : Fin K → Fin v)) (edge i)).1 = i.val + 1 := by
  induction K with
  | zero => exact Fin.elim0 i
  | succ K ih =>
      induction i using Fin.cases with
      | zero => simp [List.ofFn_succ, scanPosition]
      | succ j =>
          let tail : Fin K ↪ Fin v :=
            ⟨fun x => edge x.succ, by
              intro a b h
              apply Fin.ext
              have hh := congrArg Fin.val (edge.injective h)
              simpa using hh⟩
          have hne : edge 0 ≠ edge j.succ := by
            intro h
            have hh := edge.injective h
            have hv := congrArg Fin.val hh
            simp at hv
          have htail := ih tail j
          have ht : (scanPosition (List.ofFn (fun x : Fin K => edge x.succ))
              (edge j.succ)).1 = j.val + 1 := htail
          simp [List.ofFn_succ, scanPosition, hne, ht]

theorem scanPosition_ofFn_absent {v K : ℕ}
    (edge : Fin K ↪ Fin v) (vertex : Fin v)
    (habsent : ∀ i, edge i ≠ vertex) :
    (scanPosition (List.ofFn (edge : Fin K → Fin v)) vertex).1 = 0 := by
  induction K with
  | zero => simp [scanPosition]
  | succ K ih =>
      let tail : Fin K ↪ Fin v :=
        ⟨fun x => edge x.succ, by
          intro a b h
          apply Fin.ext
          have hh := congrArg Fin.val (edge.injective h)
          simpa using hh⟩
      have ht : (scanPosition (List.ofFn (tail : Fin K → Fin v)) vertex).1 = 0 :=
        ih tail (fun j => habsent j.succ)
      simpa [List.ofFn_succ, scanPosition, habsent 0, tail, ht]

theorem scanPosition_edgePositionEval {v K : ℕ}
    (edge : Fin K ↪ Fin v) (vertex : Fin v) :
    (scanPosition (List.ofFn (edge : Fin K → Fin v)) vertex).1 =
      (edgePositionEval edge vertex).val := by
  by_cases h : ∃ i, edge i = vertex
  · obtain ⟨i, hi⟩ := h
    subst vertex
    rw [scanPosition_ofFn_hit, edgePositionEval_eq,
      Paper2.YaoLookup.edgePosition_apply]
    rfl
  · have ha : ∀ i, edge i ≠ vertex := by
      intro i hi
      exact h ⟨i, hi⟩
    rw [scanPosition_ofFn_absent edge vertex ha, edgePositionEval_eq,
      Paper2.YaoLookup.edgePosition_absent edge vertex ha]
    rfl

/-- Lookup in one prepared source list, then scan the selected ordered edge.
The trace is the output of these two recursive calls. -/
def preparedPosition {v : ℕ} (source : List (List (Fin v)))
    (address : ℕ) (vertex : Fin v) : ℕ × ℕ :=
  let edge := readAt source address
  match edge.1 with
  | none => (0, edge.2)
  | some vertices =>
      let hit := scanPosition vertices vertex
      (hit.1, edge.2 + hit.2)

theorem preparedPosition_visits_le {v : ℕ} (source : List (List (Fin v)))
    (hinner : ∀ edge ∈ source, edge.length ≤ K)
    (address : ℕ) (vertex : Fin v) :
    (preparedPosition source address vertex).2 ≤ source.length + K := by
  unfold preparedPosition
  cases h : (readAt source address).1 with
  | none => simp [h]; exact Nat.le_add_right_of_le (readAt_visits_le source address)
  | some edge =>
      have he : edge ∈ source := by
        rw [readAt_value] at h
        exact List.mem_iff_getElem?.mpr ⟨address, h⟩
      have hh := scanPosition_visits_le edge vertex
      have heK := hinner edge he
      have hs := readAt_visits_le source address
      simp only [h]
      omega

theorem preparedPosition_real {v K e : ℕ}
    (edges : Fin e → Fin K ↪ Fin v) (a : Fin e) (vertex : Fin v) :
    (preparedPosition (prepareSource e edges).1 a.val vertex).1 =
      (edgePositionEval (edges a) vertex).val := by
  simp [preparedPosition, prepareSource_read_real,
    scanPosition_edgePositionEval]

theorem preparedPosition_unused {v K e : ℕ}
    (edges : Fin e → Fin K ↪ Fin v) (a : ℕ) (ha : e ≤ a) (vertex : Fin v) :
    (preparedPosition (prepareSource e edges).1 a vertex).1 = 0 := by
  simp [preparedPosition, prepareSource_read_unused edges a ha]

theorem preparedPosition_eq_positionEval {v K e : ℕ}
    (edges : Fin e → Fin K ↪ Fin v)
    (a : Fin (paddedEdgeCount e)) (vertex : Fin v) :
    (preparedPosition (prepareSource e edges).1 a.val vertex).1 =
      (positionEval (paddedEdgesEval edges) a vertex).val := by
  by_cases h : a.val < e
  · let real : Fin e := ⟨a.val, h⟩
    have hh := preparedPosition_real edges real vertex
    simpa [paddedEdgesEval, positionEval, h, real] using hh
  · have hh := preparedPosition_unused edges a.val (by omega) vertex
    simpa [paddedEdgesEval, positionEval, h] using hh

theorem preparedPosition_source_bound {v K e : ℕ}
    (edges : Fin e → Fin K ↪ Fin v) (address : ℕ) (vertex : Fin v) :
    (preparedPosition (prepareSource e edges).1 address vertex).2 ≤ e + K := by
  simpa [prepareSource_length] using
    preparedPosition_visits_le (prepareSource e edges).1
      (fun edge he => (prepareSource_inner_length e edges edge he).le)
      address vertex

end Paper2.YaoOperationalEntryScratch

#print axioms Paper2.YaoOperationalEntryScratch.prepareSource_value
#print axioms Paper2.YaoOperationalEntryScratch.readTapeOperational_value
#print axioms Paper2.YaoOperationalEntryScratch.readTapeOperational_visits_le
#print axioms Paper2.YaoOperationalEntryScratch.prepareSource_visits
#print axioms Paper2.YaoOperationalEntryScratch.preparedPosition_visits_le
#print axioms Paper2.YaoOperationalEntryScratch.preparedPosition_eq_positionEval
#print axioms Paper2.YaoOperationalEntryScratch.preparedPosition_source_bound
