import Paper2.YaoCloneLoop

/-! Unit 5 segment Y10 (lane a-yao-clone-owner-1): the physical clone machine
(T34 `yao:clones`, lock v12 YA:92-116), end to end.

`cloneMachine K M` is ONE fixed finite Boolean-stack machine (the admitted
`BitMachineEncoding.ofFinite` of the literal program of `YaoCloneProg`).
`clone_raw` runs it from the literal input bank (input stack = the code,
every other stack empty) to the exact exit bank (output stack = the Option B
code, every other stack empty) within the public clock `cloneTime`.
`clone_source_outputsWithin` states it for the DRAFT occurrence codec of the
admitted `YaoCloneSrc` (pending AD-1) and the admitted `cloneSource`. -/

namespace Paper2.YaoCloneMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.YaoCloneSource
open Paper2.YaoSourceCodec

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

variable {K M : ℕ}

/-- The public clock of the clone machine (labels bounded by `V`). -/
def cloneTime (K M V v : ℕ) (ls : List (Fin K → ℕ)) : ℕ :=
  (v + 1) + (ls.length + 1) + (ls.length * edgeCost K M V + 1) +
    ((ls.flatMap (edgeBlock M)).length + 1) +
    ((ls.map (fun l => (goodLifts M l).length)).sum + 1) + (v * M + 2)

theorem clone_raw (v : ℕ) (ls : List (Fin K → ℕ)) (V : ℕ) (hV : ∀ l ∈ ls, ∀ j, l j ≤ V) :
    RIn (K := K) (M := M) .hv (bk (occInput v ls) [] [] [] [] [] (E0 K) (E0 K)) none
      (bk [] [] [] [] [] (cloneOutput M v ls) (E0 K) (E0 K)) (cloneTime K M V v ls) := by
  have h1 := hv_run (K := K) (M := M) [] [] [] [] (E0 K) (E0 K) v
    (unaryNat ls.length ++ ls.flatMap edgeInput) []
  have h2 := he_run (K := K) (M := M) [] [] [] (E0 K) (E0 K) ls.length (rep (v * M) ++ [])
    (ls.flatMap edgeInput ++ []) []
  have h3 := edge_run (K := K) (M := M) (rep (v * M) ++ []) V ls hV [] [] []
  have h4 := fin1_run (K := K) (M := M) [] [] (E0 K) (E0 K) (rep (v * M) ++ [])
    (rep (ls.map (fun l => (goodLifts M l).length)).sum ++ [])
    ((ls.flatMap (edgeBlock M)).reverse ++ []) []
  have h5 := fin2_run (K := K) (M := M) [] [] (E0 K) (E0 K) (rep (v * M) ++ [])
    (ls.map (fun l => (goodLifts M l).length)).sum
    (false :: (((ls.flatMap (edgeBlock M)).reverse ++ []).reverse ++ []))
  have h6 := fin3_run (K := K) (M := M) [] [] (E0 K) (E0 K) (v * M)
    (false :: (rep (ls.map (fun l => (goodLifts M l).length)).sum ++
      false :: (((ls.flatMap (edgeBlock M)).reverse ++ []).reverse ++ [])))
  simp only [List.append_nil] at h1 h2 h3 h4 h5 h6
  have hin : occInput v ls = unaryNat v ++ (unaryNat ls.length ++ ls.flatMap edgeInput) := by
    simp [occInput, List.append_assoc]
  rw [hin]
  have := ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6
  refine (RIn.congr_bank this ?_).mono ?_
  · simp [cloneOutput, unaryNat, List.append_assoc]
  · simp only [cloneTime, List.length_reverse]
    omega

/-- The clone machine as a finite Boolean-stack machine (input stack `inp`,
output stack `out`). -/
noncomputable def cloneMachine (K M : ℕ) : BitMachine.Machine :=
  ofFinite (Stk.inp : Stk K) Stk.out (Lbl.hv : Lbl K M) ((none, none) : St) program

theorem rawInit_eq (bits : List Bool) :
    (rawInit (Stk.inp : Stk K) (Lbl.hv : Lbl K M) ((none, none) : St) bits) =
      ⟨some .hv, (none, none), bk bits [] [] [] [] [] (E0 K) (E0 K)⟩ := by
  simp only [rawInit]
  congr 1
  funext k
  cases k <;> simp [bk]

/-- Y10 main theorem, list level: from the literal input `occInput v ls` the
fixed machine halts within `cloneTime` with output `cloneOutput M v ls`. -/
theorem clone_outputsWithin (v : ℕ) (ls : List (Fin K → ℕ)) (V : ℕ)
    (hV : ∀ l ∈ ls, ∀ j, l j ≤ V) :
    (cloneMachine K M).OutputsWithin (occInput v ls) (cloneOutput M v ls) (cloneTime K M V v ls) := by
  obtain ⟨n, hn, σ', hr⟩ := clone_raw (K := K) (M := M) v ls V hV (none, none)
  have hr' : ((advance (program (K := K) (M := M)))^[n])
      (rawInit (Stk.inp : Stk K) (Lbl.hv : Lbl K M) ((none, none) : St) (occInput v ls)) =
      ⟨none, σ', bk [] [] [] [] [] (cloneOutput M v ls) (E0 K) (E0 K)⟩ := by
    rw [rawInit_eq]; exact hr
  exact outputsWithin_of_raw_run _ _ _ _ _ _ _ n _ hn (by rw [hr']) (by rw [hr']; rfl)

theorem labelsOf_le {t : ℕ} (x : DraftOccSource t) :
    ∀ l ∈ labelsOf x, ∀ j, l j ≤ x.1 := by
  intro l hl j
  simp only [labelsOf, List.mem_ofFn] at hl
  obtain ⟨i, rfl⟩ := hl
  exact (x.2.2 i j).isLt.le

/-- Y10 main theorem, source level (T34 machine): the fixed clone machine for
`K = 2^t*2^t`, `M = K*S` maps the DRAFT occurrence code of `x` (pending
AD-1) to the Option B code of the admitted clone source `cloneSource t S x`,
within the public clock `cloneTime K M x.1 x.1 (labelsOf x)`. -/
theorem clone_source_outputsWithin (t S : ℕ) (x : DraftOccSource t) :
    (cloneMachine (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * S)).OutputsWithin (draftOccEncode x)
      (encode (cloneSource t S x))
      (cloneTime (2 ^ t * 2 ^ t) (2 ^ t * 2 ^ t * S) x.1 x.1 (labelsOf x)) := by
  rw [draftOccEncode_eq, encode_cloneSource_eq]
  exact clone_outputsWithin x.1 (labelsOf x) x.1 (labelsOf_le x)

#print axioms clone_raw
#print axioms clone_outputsWithin
#print axioms clone_source_outputsWithin

end Paper2.YaoCloneMachine
