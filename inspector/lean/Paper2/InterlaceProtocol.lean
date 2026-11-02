import Paper2.InterlaceRank

/-!
# The selector protocol for indexed interlacing

Source: Paper 2, frozen `2026-09-22-protocol-labels-v12`, Section 2,
Definition `def:interlace` and equation `eq:selector-upper`.

Alice announces the selector in `Nat.clog 2 q` bits. The corresponding
continuation is the original concrete protocol, with Bob locally evaluating
his indexed tuple at the announced coordinate. The family may contain
repetitions, and no balancedness or random-sampling hypothesis is used.

The only protocol constructors reused are `Workspace.UpperBound.announceTree`
and `Workspace.UpperBound.Protocol.comap`, together with their checked cost
and evaluation lemmas. The base optimal protocol is used in the *analysis*
of communication cost, never to choose a hardness-reduction output.
-/

namespace Paper2

open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {X Y Z : Type*}

/-- An injective binary name for a selector. Local encodings are free in the
communication model. -/
noncomputable def selectorCode (q : ℕ) : Fin q ↪ (Fin (Nat.clog 2 q) → Bool) := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  simpa using (Nat.le_pow_clog (by decide : 1 < 2) q)

/-- Decode valid selector names; unused names have a default selector. The
positive-width guard is precisely what provides that default. -/
noncomputable def selectorDecode {q : ℕ} (hq : 0 < q) :
    (Fin (Nat.clog 2 q) → Bool) → Fin q := by
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  exact Function.invFun (selectorCode q)

@[simp] theorem selectorDecode_code {q : ℕ} (hq : 0 < q) (i : Fin q) :
    selectorDecode hq (selectorCode q i) = i := by
  letI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  unfold selectorDecode
  exact Function.leftInverse_invFun (selectorCode q).injective i

/-- The actual protocol: announce the selector, then execute the base
protocol on the selected entry of Bob's indexed tuple. -/
noncomputable def selectorProtocol {q : ℕ} (hq : 0 < q)
    (S : Z → Fin q → Y) (P : Protocol X Y Bool) :
    Protocol (Fin q × X) Z Bool :=
  Workspace.UpperBound.announceTree (Nat.clog 2 q)
    (fun w => Workspace.UpperBound.Protocol.comap
      (fun a : Fin q × X => a.2) (fun z => S z (selectorDecode hq w)) P)
    (fun a => selectorCode q a.1)

theorem selectorProtocol_cost {q : ℕ} (hq : 0 < q)
    (S : Z → Fin q → Y) (P : Protocol X Y Bool) :
    (selectorProtocol hq S P).cost ≤ Nat.clog 2 q + P.cost := by
  unfold selectorProtocol
  apply Workspace.UpperBound.announceTree_cost
  intro w
  rw [Workspace.UpperBound.Protocol.comap_cost]

@[simp] theorem selectorProtocol_eval {q : ℕ} (hq : 0 < q)
    (S : Z → Fin q → Y) (P : Protocol X Y Bool)
    (a : Fin q × X) (z : Z) :
    (selectorProtocol hq S P).eval a z = P.eval a.2 (S z a.1) := by
  unfold selectorProtocol
  rw [Workspace.UpperBound.announceTree_eval,
    Workspace.UpperBound.Protocol.comap_eval, selectorDecode_code]

theorem selectorProtocol_computes {q : ℕ} (hq : 0 < q)
    (F : X → Y → Bool) (S : Z → Fin q → Y) (P : Protocol X Y Bool)
    (hP : P.Computes F) :
    (selectorProtocol hq S P).Computes (indexedInterlace F S) := by
  intro a z
  rw [selectorProtocol_eval]
  exact hP a.2 (S z a.1)

/-- The integer ceiling-log version of `eq:selector-upper`. The constructor
is independent of any injectivity property of the indexed tuple family. -/
theorem indexedInterlace_D_le [Fintype X] [Fintype Y] [Fintype Z]
    (F : X → Y → Bool) {q : ℕ} (hq : 0 < q) (S : Z → Fin q → Y) :
    D (indexedInterlace F S) ≤ Nat.clog 2 q + D F := by
  obtain ⟨P, hcost, hcomp⟩ :=
    Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty F)
  have hupper := selectorProtocol_cost hq S P
  rw [hcost] at hupper
  have hmem : (selectorProtocol hq S P).cost ∈
      AchievableCosts (indexedInterlace F S) :=
    ⟨selectorProtocol hq S P, rfl, selectorProtocol_computes hq F S P hcomp⟩
  exact (Nat.sInf_le hmem).trans hupper

/-- The exact real-logarithm notation of the manuscript, using the natural
ceiling because communication cost is a natural number. -/
theorem indexedInterlace_D_le_ceil [Fintype X] [Fintype Y] [Fintype Z]
    (F : X → Y → Bool) {q : ℕ} (hq : 0 < q) (S : Z → Fin q → Y) :
    D (indexedInterlace F S) ≤ ⌈Real.logb 2 (q : ℝ)⌉₊ + D F := by
  simpa only [← Real.natCeil_logb_natCast 2 q] using
    indexedInterlace_D_le F hq S

theorem fullInterlace_D_le [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (q : ℕ) (hq : 0 < q) :
    D (fullInterlace F q) ≤ Nat.clog 2 q + D F :=
  indexedInterlace_D_le F hq (fun ys : Fin q → Y => ys)

theorem fullInterlace_D_le_ceil [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (q : ℕ) (hq : 0 < q) :
    D (fullInterlace F q) ≤ ⌈Real.logb 2 (q : ℝ)⌉₊ + D F :=
  indexedInterlace_D_le_ceil F hq (fun ys : Fin q → Y => ys)

/-- Transposition preserves the selector upper bound exactly: it only
exchanges which player announces the selector. -/
theorem indexedInterlace_transpose_D_le [Fintype X] [Fintype Y] [Fintype Z]
    (F : X → Y → Bool) {q : ℕ} (hq : 0 < q) (S : Z → Fin q → Y) :
    D (fun z a => indexedInterlace F S a z) ≤ Nat.clog 2 q + D F := by
  rw [transpose_D]
  exact indexedInterlace_D_le F hq S

theorem fullInterlace_transpose_D_le [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (q : ℕ) (hq : 0 < q) :
    D (fun ys a => fullInterlace F q a ys) ≤ Nat.clog 2 q + D F := by
  rw [transpose_D]
  exact fullInterlace_D_le F q hq

/-- At width `2^d`, the selector contributes at most `d` bits. -/
theorem fullInterlace_two_pow_D_le [Fintype X] [Fintype Y]
    (F : X → Y → Bool) (d : ℕ) :
    D (fullInterlace F (2 ^ d)) ≤ d + D F := by
  simpa only [Nat.clog_pow, one_lt_two] using
    fullInterlace_D_le F (2 ^ d) (Nat.two_pow_pos d)

end Paper2
