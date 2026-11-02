import Paper2.YaoEvents

/-!
# Normalization preserves the early strategy used by the payload event

Frozen v12: `yao:events` (ii) and the first paragraph of
`yao:payload-event`. Padding is by fixed zero bits, and normalization
changes only the final transmitted bit. The guard `2*t < d` keeps that
last bit after the early strategy; it is proved for the paper's parameters.
The boundary with no suffix is deliberately not asserted.
-/

namespace Paper2.Yao

open Workspace.Types.Protocol

variable {X Y : Type*}

theorem afterAlice_alternates (P : Protocol X Y Bool) (x : X)
    (ha : Alternates .alice P) : Alternates .bob (afterAlice P x) := by
  cases P with
  | leaf b => trivial
  | aNode a l r => cases hx : a x <;> simp [afterAlice, hx, ha.1, ha.2]
  | bNode b l r => exact False.elim ha

theorem afterBob_alternates (P : Protocol X Y Bool) (b : Bool)
    (ha : Alternates .bob P) : Alternates .alice (afterBob P b) := by
  cases P with
  | leaf c => trivial
  | aNode a l r => exact False.elim ha
  | bNode f l r => cases b <;> simp [afterBob, ha.1, ha.2]

theorem afterRound_alternates (P : Protocol X Y Bool) (x : X) (b : Bool)
    (ha : Alternates .alice P) : Alternates .alice (afterRound P x b) :=
  afterBob_alternates _ b (afterAlice_alternates P x ha)

theorem padTree_aliceMessage (P : Protocol X Y Bool) (d : ℕ) (x : X)
    (ha : Alternates .alice P) :
    aliceMessage (padTree P .alice (d + 1)) x = aliceMessage P x := by
  cases P with
  | leaf b => rfl
  | aNode a l r => rfl
  | bNode b l r => exact False.elim ha

theorem padTree_afterAlice (P : Protocol X Y Bool) (d : ℕ) (x : X)
    (ha : Alternates .alice P) :
    afterAlice (padTree P .alice (d + 1)) x = padTree (afterAlice P x) .bob d := by
  cases P with
  | leaf b => rfl
  | aNode a l r => cases hx : a x <;> simp [afterAlice, padTree, hx]
  | bNode b l r => exact False.elim ha

theorem padTree_afterBob (P : Protocol X Y Bool) (d : ℕ) (b : Bool)
    (ha : Alternates .bob P) :
    afterBob (padTree P .bob (d + 1)) b = padTree (afterBob P b) .alice d := by
  cases P with
  | leaf c => cases b <;> rfl
  | aNode a l r => exact False.elim ha
  | bNode f l r => cases b <;> rfl

theorem padTree_afterRound (P : Protocol X Y Bool) (d : ℕ) (x : X) (b : Bool)
    (ha : Alternates .alice P) :
    afterRound (padTree P .alice (d + 2)) x b =
      padTree (afterRound P x b) .alice d := by
  rw [afterRound, padTree_afterAlice _ _ _ ha,
    padTree_afterBob _ _ _ (afterAlice_alternates _ _ ha)]
  rfl

/-- Padding by public zero bits leaves the whole early response tree
unchanged, including hypothetical Bob histories and stopped branches. -/
theorem earlyStrategy_padTree (t d : ℕ) (P : Protocol X Y Bool)
    (ha : Alternates .alice P) (hd : 2 * t ≤ d) (x : X) :
    earlyStrategy t (padTree P .alice d) x = earlyStrategy t P x := by
  induction t generalizing d P with
  | zero => rfl
  | succ t ih =>
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
      simp only [earlyStrategy, padTree_aliceMessage _ _ _ ha,
        padTree_afterRound _ _ _ _ ha]
      rw [ih k _ (afterRound_alternates _ _ _ ha) (by omega),
        ih k _ (afterRound_alternates _ _ _ ha) (by omega)]

theorem normalizeTree_aliceMessage (P : Protocol X Y Bool) (d : ℕ) (x : X) :
    aliceMessage (normalizeTree (d + 2) P) x = aliceMessage P x := by
  cases P <;> simp only [normalizeTree, aliceMessage]

theorem normalizeTree_afterAlice (P : Protocol X Y Bool) (d : ℕ) (x : X)
    (ha : Alternates .alice P) :
    afterAlice (normalizeTree (d + 2) P) x = normalizeTree (d + 1) (afterAlice P x) := by
  cases P with
  | leaf b => rfl
  | aNode a l r => cases hx : a x <;> simp [afterAlice, normalizeTree, hx]
  | bNode b l r => exact False.elim ha

theorem normalizeTree_afterBob (P : Protocol X Y Bool) (d : ℕ) (b : Bool)
    (ha : Alternates .bob P) :
    afterBob (normalizeTree (d + 2) P) b = normalizeTree (d + 1) (afterBob P b) := by
  cases P with
  | leaf c => rfl
  | aNode a l r => exact False.elim ha
  | bNode f l r => cases b <;> simp [normalizeTree, afterBob]

theorem normalizeTree_afterRound (P : Protocol X Y Bool) (d : ℕ) (x : X) (b : Bool)
    (ha : Alternates .alice P) :
    afterRound (normalizeTree (d + 3) P) x b =
      normalizeTree (d + 1) (afterRound P x b) := by
  rw [afterRound, normalizeTree_afterAlice _ _ _ ha,
    normalizeTree_afterBob _ _ _ (afterAlice_alternates _ _ ha)]
  rfl

/-- Final-bit normalization preserves an early strategy strictly before
the final level. Without the depth guard this statement would be false. -/
theorem earlyStrategy_normalizeTree (t d : ℕ) (P : Protocol X Y Bool)
    (ha : Alternates .alice P) (hd : 2 * t < d) (x : X) :
    earlyStrategy t (normalizeTree d P) x = earlyStrategy t P x := by
  induction t generalizing d P with
  | zero => rfl
  | succ t ih =>
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 3 := ⟨d - 3, by omega⟩
      simp only [earlyStrategy, normalizeTree_aliceMessage,
        normalizeTree_afterRound _ _ _ _ ha]
      rw [ih (k + 1) _ (afterRound_alternates _ _ _ ha) (by omega),
        ih (k + 1) _ (afterRound_alternates _ _ _ ha) (by omega)]

/-- The actual complete normal form preserves early responses and all
lookup entries. The assumptions are only the original cost, alternation,
and the strict depth guard; no normalized protocol is assumed to exist. -/
theorem exists_normalized_preserving_strategy (t r : ℕ) (P : Protocol X Y Bool)
    (ha : Alternates .alice P) (hcost : P.cost ≤ 2 * r + 1)
    (hguard : 2 * t < 2 * r + 1) :
    ∃ Q : Protocol X Y Bool,
      IsComplete Q (2 * r + 1) ∧ Alternates .alice Q ∧
      CanonicalLastLeaves (2 * r + 1) Q ∧
      (∀ x, earlyStrategy t Q x = earlyStrategy t P x) ∧
      ∀ x y, Q.eval x y = P.eval x y := by
  let R := padTree P .alice (2 * r + 1)
  have hc : IsComplete R (2 * r + 1) := padTree_isComplete P .alice _ hcost
  have hal : Alternates .alice R := padTree_alternates P .alice _ ha
  refine ⟨normalizeTree (2 * r + 1) R,
    normalizeTree_isComplete _ _ hc,
    normalizeTree_alternates _ _ _ hc hal,
    normalizeTree_canonical _ _ hc, ?_, ?_⟩
  · intro x
    rw [earlyStrategy_normalizeTree _ _ _ hal hguard,
      earlyStrategy_padTree _ _ _ ha (Nat.le_of_lt hguard)]
  · intro x y
    rw [normalizeTree_eval _ _ hc]
    exact padTree_eval P .alice _ x y

/-- Failure for arbitrary short public-output alternating protocols; no
completeness or canonical-leaf assumption remains. -/
def payloadShortProtocolFailure {X : Type*} [Fintype X] [DecidableEq X]
    (r t jmin samples : ℕ) (ws : Fin samples → (X → Bool)) : Prop :=
  ∃ J : Finset X, jmin ≤ J.card ∧
    ∃ P : Protocol J (Fin samples) Bool,
      P.cost ≤ 2 * r + 1 ∧ Alternates .alice P ∧
      (∃ σ : ResponseStrategy t, ∀ x, earlyStrategy t P x = σ) ∧
      ∀ x l, P.eval x l = ws l x.val

theorem payloadShortProtocolFailure_normalized {X : Type*} [Fintype X] [DecidableEq X]
    (r t jmin samples : ℕ) (hguard : 2 * t < 2 * r + 1)
    (ws : Fin samples → (X → Bool))
    (h : payloadShortProtocolFailure r t jmin samples ws) :
    payloadProtocolFailure r t jmin samples ws := by
  obtain ⟨J, hj, P, hc, ha, ⟨σ, hσ⟩, he⟩ := h
  obtain ⟨Q, hQc, hQa, hQn, hQs, hQe⟩ :=
    exists_normalized_preserving_strategy t r P ha hc hguard
  refine ⟨J, hj, Q, hQc, hQa, hQn, ⟨σ, ?_⟩, ?_⟩
  · intro x
    exact (hQs x).trans (hσ x)
  · intro x l
    exact (hQe x l).trans (he x l)

/-- Full payload sampling property for bounded-cost protocols. The sole
extra guard ensures that normalization does not change an early Alice bit. -/
theorem payload_short_protocol_failure_le {X : Type*} [Fintype X] [DecidableEq X]
    (r t a jmin delta samples lambda : ℕ) (ht : 1 ≤ t)
    (hd : 2 * r + 1 = (2 * t - 1) + 2 * a)
    (hguard : 2 * t < 2 * r + 1)
    (hgap : (2 ^ a + t - 2) + delta ≤ jmin)
    (hbudget : Fintype.card X * (aliceNodes r + 1) + lambda ≤ delta * samples) :
    ((payloadLaw X).iid samples).prob
      (payloadShortProtocolFailure r t jmin samples) ≤ (1 / 2 : ℝ) ^ lambda := by
  apply (FiniteLaw.prob_mono _
    (payloadShortProtocolFailure_normalized r t jmin samples hguard)).trans
  exact payload_protocol_failure_le r t a jmin delta samples lambda ht hd hgap hbudget

/-- The paper's explicit parameters satisfy the normalization guard. This
is the complete payload half T29(ii): arbitrary depth-at-most-D protocols,
all post-sample retained position sets and Alice maps, every Bob completion,
and an exact public sample count. -/
theorem payload_explicit_counts_short_failure_le {X : Type*} [Fintype X] [DecidableEq X]
    (b t lambda : ℕ) (ht : 4 ≤ t) :
    let r := b + 3 * t - 3
    let m := payloadSampleCount (Fintype.card X) r (payloadDelta b t) lambda
    ((payloadLaw X).iid m).prob
      (payloadShortProtocolFailure r t (payloadMinimum b t) m) ≤ (1 / 2 : ℝ) ^ lambda := by
  dsimp only
  apply (FiniteLaw.prob_mono _
    (payloadShortProtocolFailure_normalized _ _ _ _ (by omega))).trans
  exact payload_explicit_counts_failure_le b t lambda ht

/-- At depth one, normalization can change the first response. This is why
the earlier strategy-preservation results retain their strict depth guard. -/
theorem normalization_final_response_can_change :
    let P : Protocol Unit Unit Bool := .aNode (fun _ => false) (.leaf true) (.leaf true)
    earlyStrategy 1 (normalizeTree 1 P) () ≠ earlyStrategy 1 P () := by
  decide

end Paper2.Yao
