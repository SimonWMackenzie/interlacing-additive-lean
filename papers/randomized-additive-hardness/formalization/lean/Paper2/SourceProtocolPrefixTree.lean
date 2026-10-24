import Paper2.PrefixPullback

/-!
# Complete Alice prefixes of an actual protocol

Frozen Paper 2 v12, the common-assignment use of `cl:separation`.
The separation theorem controls live paths. When every fixed-width code is
realised by a retained row, every branch of the prefix is live, so this gives
a complete syntactic Alice tree. Syntactic completeness reflects through any
input pullback, including the fixed-tail maps used by the source construction.
The residual-cost inequality below is additive, with no truncated subtraction.
-/

namespace Paper2.SourceProtocolPrefixTree

open Workspace.Types.Protocol

variable {X Y A B Z : Type*}

/-- Every node strictly above depth `k` is an Alice node, including nodes that
are unreachable on a particular input rectangle. -/
def CompleteAlicePrefix : ℕ → Protocol X Y Z → Prop
  | 0, _ => True
  | _ + 1, Protocol.leaf _ => False
  | k + 1, Protocol.aNode _ l r => CompleteAlicePrefix k l ∧ CompleteAlicePrefix k r
  | _ + 1, Protocol.bNode _ _ _ => False

/-- Input pullback preserves the tree itself, without any surjectivity premise. -/
theorem complete_pullback_iff (f : A → X) (g : B → Y)
    (k : ℕ) (P : Protocol X Y Z) :
    CompleteAlicePrefix k (NPCC.Protocol.pullback f g P) ↔ CompleteAlicePrefix k P := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      cases P <;> simp [NPCC.Protocol.pullback, CompleteAlicePrefix, ih]

/-- Syntactic completeness controls every retained rectangle, even an empty one. -/
theorem firstK_of_complete (R : Finset X) (C : Finset Y)
    (k : ℕ) (P : Protocol X Y Z) (h : CompleteAlicePrefix k P) :
    NPCC.Protocol.FirstKRowBitsOn R C k P := by
  classical
  induction k generalizing R P with
  | zero => trivial
  | succ k ih =>
      cases P with
      | leaf z => exact h.elim
      | bNode b l r => exact h.elim
      | aNode a l r => exact ⟨ih _ l h.1, ih _ r h.2⟩

/-- Realising all codes of an Alice node realises every suffix in each actual
filtered row group. This also records that neither branch is a fixed message. -/
theorem all_codes_branch (R : Finset X) (k : ℕ) (a : X → Bool)
    (l r : Protocol X Y Z)
    (hall : ∀ w : Fin (2 ^ (k + 1)), ∃ x ∈ R,
      NPCC.Protocol.prefixCodeRaw (k + 1) (Protocol.aNode a l r) x = w)
    (b : Bool) (w : Fin (2 ^ k)) :
    ∃ x ∈ R.filter (fun x => a x = b),
      NPCC.Protocol.prefixCodeRaw k (if b then r else l) x = w := by
  classical
  obtain ⟨x, hx, hcode⟩ := hall (NPCC.Protocol.bitCons b w)
  have hhead := congrArg NPCC.Protocol.bitHead hcode
  have hax : a x = b := by
    simpa only [NPCC.Protocol.prefixCodeRaw, NPCC.Protocol.bitHead_bitCons] using hhead
  have htail := congrArg NPCC.Protocol.bitTail hcode
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, hax⟩, ?_⟩
  simpa only [NPCC.Protocol.prefixCodeRaw, NPCC.Protocol.bitTail_bitCons, hax] using htail

/-- A live Alice prefix with every code realised is a complete syntactic prefix
of that same protocol. No replacement or pruning of the protocol is performed. -/
theorem complete_of_firstK_and_all_codes (R : Finset X) (C : Finset Y)
    (k : ℕ) (P : Protocol X Y Z)
    (hrow : NPCC.Protocol.FirstKRowBitsOn R C k P) (hC : C.Nonempty)
    (hall : ∀ w : Fin (2 ^ k), ∃ x ∈ R, NPCC.Protocol.prefixCodeRaw k P x = w) :
    CompleteAlicePrefix k P := by
  classical
  induction k generalizing R P with
  | zero => trivial
  | succ k ih =>
      have hR : R.Nonempty := by
        obtain ⟨x, hx, _⟩ := hall (NPCC.Protocol.zeroPow2 (k + 1))
        exact ⟨x, hx⟩
      cases P with
      | leaf z => exact (hrow.elim hR.ne_empty hC.ne_empty).elim
      | bNode b l r => exact (hrow.elim hR.ne_empty hC.ne_empty).elim
      | aNode a l r =>
          constructor
          · apply ih (R.filter (fun x => a x = false)) l hrow.1
            intro w
            simpa using all_codes_branch R k a l r hall false w
          · apply ih (R.filter (fun x => a x = true)) r hrow.2
            intro w
            simpa using all_codes_branch R k a l r hall true w

/-- At an Alice node whose full codes are realised, both messages occur on
retained rows. The same statement applies recursively by `all_codes_branch`. -/
theorem both_branches_nonempty (R : Finset X) (k : ℕ) (a : X → Bool)
    (l r : Protocol X Y Z)
    (hall : ∀ w : Fin (2 ^ (k + 1)), ∃ x ∈ R,
      NPCC.Protocol.prefixCodeRaw (k + 1) (Protocol.aNode a l r) x = w) :
    (R.filter (fun x => a x = false)).Nonempty ∧
      (R.filter (fun x => a x = true)).Nonempty := by
  classical
  constructor
  · obtain ⟨x, hx, _⟩ := all_codes_branch R k a l r hall false (NPCC.Protocol.zeroPow2 k)
    exact ⟨x, hx⟩
  · obtain ⟨x, hx, _⟩ := all_codes_branch R k a l r hall true (NPCC.Protocol.zeroPow2 k)
    exact ⟨x, hx⟩

/-- Every Alice message before depth `k` has both outputs among rows reaching
that node. The filtered row sets are the actual groups defined by the messages. -/
def EveryPrefixBranchActive : Finset X → ℕ → Protocol X Y Z → Prop
  | _, 0, _ => True
  | _, _ + 1, Protocol.leaf _ => False
  | R, k + 1, Protocol.aNode a l r =>
      (R.filter (fun x => a x = false)).Nonempty ∧
      (R.filter (fun x => a x = true)).Nonempty ∧
      EveryPrefixBranchActive (R.filter (fun x => a x = false)) k l ∧
      EveryPrefixBranchActive (R.filter (fun x => a x = true)) k r
  | _, _ + 1, Protocol.bNode _ _ _ => False

/-- Full code realisation rules out fixed messages at every shallow node. -/
theorem active_branches_of_complete_and_all_codes (R : Finset X)
    (k : ℕ) (P : Protocol X Y Z) (hc : CompleteAlicePrefix k P)
    (hall : ∀ w : Fin (2 ^ k), ∃ x ∈ R, NPCC.Protocol.prefixCodeRaw k P x = w) :
    EveryPrefixBranchActive R k P := by
  classical
  induction k generalizing R P with
  | zero => trivial
  | succ k ih =>
      cases P with
      | leaf z => exact hc.elim
      | bNode b l r => exact hc.elim
      | aNode a l r =>
          obtain ⟨hl, hr⟩ := both_branches_nonempty R k a l r hall
          refine ⟨hl, hr, ?_, ?_⟩
          · apply ih (R.filter (fun x => a x = false)) l hc.1
            intro w
            simpa using all_codes_branch R k a l r hall false w
          · apply ih (R.filter (fun x => a x = true)) r hc.2
            intro w
            simpa using all_codes_branch R k a l r hall true w

/-- Live control and actual realisation imply nonfixed Alice branching all
the way down the complete prefix, for the original retained rows. -/
theorem active_branches_of_firstK_and_all_codes (R : Finset X) (C : Finset Y)
    (k : ℕ) (P : Protocol X Y Z)
    (hrow : NPCC.Protocol.FirstKRowBitsOn R C k P) (hC : C.Nonempty)
    (hall : ∀ w : Fin (2 ^ k), ∃ x ∈ R, NPCC.Protocol.prefixCodeRaw k P x = w) :
    EveryPrefixBranchActive R k P :=
  active_branches_of_complete_and_all_codes R k P
    (complete_of_firstK_and_all_codes R C k P hrow hC hall) hall

/-- Every complete-prefix residual has the full additive depth saving. -/
theorem subtree_cost_add_le (k : ℕ) (P : Protocol X Y Z)
    (h : CompleteAlicePrefix k P) (w : Fin (2 ^ k)) :
    (NPCC.Protocol.rowSubtreeAtRaw k P w).cost + k ≤ P.cost := by
  induction k generalizing P with
  | zero => simp [NPCC.Protocol.rowSubtreeAtRaw]
  | succ k ih =>
      cases P with
      | leaf z => exact h.elim
      | bNode b l r => exact h.elim
      | aNode a l r =>
          have hl := ih l h.1 (NPCC.Protocol.bitTail w)
          have hr := ih r h.2 (NPCC.Protocol.bitTail w)
          have hcl : l.cost ≤ max l.cost r.cost := le_max_left _ _
          have hcr : r.cost ≤ max l.cost r.cost := le_max_right _ _
          simp only [NPCC.Protocol.rowSubtreeAtRaw, Protocol.cost]
          split <;> omega

/-- Evaluating the residual selected by a row's actual prefix gives precisely
the original protocol's answer, on any column. -/
theorem subtree_eval_of_prefix (k : ℕ) (P : Protocol X Y Z)
    (h : CompleteAlicePrefix k P) (w : Fin (2 ^ k)) (x : X) (y : Y)
    (hw : NPCC.Protocol.prefixCodeRaw k P x = w) :
    (NPCC.Protocol.rowSubtreeAtRaw k P w).eval x y = P.eval x y := by
  classical
  exact NPCC.Protocol.eval_rowSubtreeAtRaw_eq_of_prefix {x} {y} k P w
    (firstK_of_complete {x} {y} k P h) (by simp) (by simp) hw

end Paper2.SourceProtocolPrefixTree
