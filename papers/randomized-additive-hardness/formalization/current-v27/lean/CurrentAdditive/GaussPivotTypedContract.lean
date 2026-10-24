import CurrentAdditive.GaussPivotTypedCallback

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussPivotTypedContract

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussPivotCallbackFrame
open CurrentAdditive.GaussPivotCallbackPost
open CurrentAdditive.GaussPivotTypedRows
open CurrentAdditive.GaussPivotTypedScan
open CurrentAdditive.GaussTypedGetterBridge
open CurrentAdditive.GaussRowZeroCallback
open Turing

abbrev Stack := Fin 32

structure Data {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (r state : List Bool) where
  t : Nat
  v : GaussRowZeroCallback.Control
  T : Stack → List Bool
  bound :
    ∃ i : Fin m, ∃ cellPre cellSuffix : List (List Bool),
      cellPre.length = j.val ∧
      word = SourceListEncoding.encode
        (cellPre ++ CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat (B i j)) :: cellSuffix) ∧
      t ≤ callbackCost cellPre
        (CurrentAdditive.CodeDCodec.encodeRawRat
          (CurrentAdditive.GaussPhysical.rawOfRat (B i j))) cellSuffix
        (selected pre word suffix
          (reversed (piece j.val) pre)
          (List.replicate j.val true) r state).stk
  run_eq :
    let S := (selected pre word suffix
      (reversed (piece j.val) pre) (List.replicate j.val true) r state).stk
    GaussRowZeroCallback.run t
      ⟨some (bLabel .scan), bControl ((), none), S⟩ =
      ⟨none, v, T⟩
  output_eq : T 9 = piece j.val word :: reversed (piece j.val) pre
  scratch_eq : ∀ i : Fin 15, T (clearBank i) = []
  preserve_eq : ∀ x : Stack,
    x = 8 ∨ x = 10 ∨ x = 12 ∨ x = 13 ∨ x = 30 ∨ x = 31 →
    T x = (selected pre word suffix
      (reversed (piece j.val) pre) (List.replicate j.val true) r state).stk x

theorem data_exists {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (r state : List Bool)
    (h : pre ++ word :: suffix = rowWords B) :
    Nonempty (Data B j pre word suffix r state) := by
  obtain ⟨t, v, T, hb, hr, ho, hs, hp⟩ :=
    CurrentAdditive.GaussPivotTypedCallback.witness B j
      pre word suffix r state h
  exact ⟨⟨t, v, T, hb, hr, ho, hs, hp⟩⟩

noncomputable def data {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) (r state : List Bool)
    (h : pre ++ word :: suffix = rowWords B) :
    Data B j pre word suffix r state :=
  Classical.choice (data_exists B j pre word suffix r state h)

noncomputable def time {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (r state : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Nat :=
  if h : pre ++ word :: suffix = rowWords B then
    (data B j pre word suffix r state h).t else 0

noncomputable def control {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (r state : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : GaussRowZeroCallback.Control :=
  if h : pre ++ word :: suffix = rowWords B then
    (data B j pre word suffix r state h).v else bControl ((), none)

noncomputable def state {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (r statePacket : List Bool)
    (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) : Stack → List Bool :=
  if h : pre ++ word :: suffix = rowWords B then
    (data B j pre word suffix r statePacket h).T else fun _ => []

noncomputable def contract {m k : Nat} (B : Fin m → Fin k → ℚ)
    (j : Fin k) (r statePacket : List Bool) :
    Contract GaussRowZeroCallback.program (bLabel .scan)
      (bControl ((), none)) (rowWords B) (piece j.val) []
      (List.replicate j.val true) where
  extra := extra r statePacket
  time := time B j r statePacket
  control := control B j r statePacket
  state := state B j r statePacket
  callback_run := by
    intro pre word suffix h
    dsimp only
    have hr := (data B j pre word suffix r statePacket h).run_eq
    simp only [GaussRowZeroCallback.run] at hr
    simpa only [time, control, state, dif_pos h, List.append_nil,
      ← h] using hr
  post := by
    intro pre word suffix h
    dsimp only
    let D := data B j pre word suffix r statePacket h
    have hp := post_clean pre word suffix
      (reversed (piece j.val) pre)
      (List.replicate j.val true) r statePacket
      D.T (piece j.val word) D.output_eq D.scratch_eq D.preserve_eq
    simpa only [state, dif_pos h, List.append_nil,
      reversed_snoc, ← h] using hp

end CurrentAdditive.GaussPivotTypedContract
