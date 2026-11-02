import Paper2.YaoCapacity
import Paper2.ProductProjections
import Paper2.ClassicalSeparation

/-!
# The payload sampling event for strict alternation

Locked source: v12, `sections/07-yao.tex`, `yao:events` (ii), and
`appendices/B-yao.tex`, `yao:payload-event`.

The tests below enumerate actual Alice maps on the complete normalized
Alice-first tree and every retained set. Bob's choices are not enumerated:
the column catalogue already permits every completion. The probability
space is independent fair payload bits, with repeated sample labels kept.
-/

namespace Paper2.Yao

open Workspace.Types.Protocol
open scoped BigOperators

universe u

/-- Alice nodes in a complete Alice-first tree of odd depth `2*r+1`. -/
def aliceNodes : ℕ → ℕ
  | 0 => 1
  | r + 1 => 1 + 4 * aliceNodes r

/-- Exactly the choices of Alice maps, with normalized final output bits.
There are no choices of Bob maps or public leaf labels in this type. -/
def AlicePlan (X : Type u) : ℕ → Type u
  | 0 => X → Bool
  | r + 1 => (X → Bool) × (AlicePlan X r × AlicePlan X r) ×
      (AlicePlan X r × AlicePlan X r)

instance planFintype (X : Type u) [Fintype X] [DecidableEq X] :
    (r : ℕ) → Fintype (AlicePlan X r)
  | 0 => inferInstanceAs (Fintype (X → Bool))
  | r + 1 => by
      letI := planFintype X r
      exact inferInstanceAs (Fintype ((X → Bool) × (AlicePlan X r × AlicePlan X r) ×
        (AlicePlan X r × AlicePlan X r)))

theorem card_alicePlan (X : Type u) [Fintype X] [DecidableEq X] (r : ℕ) :
    Fintype.card (AlicePlan X r) = 2 ^ (Fintype.card X * aliceNodes r) := by
  induction r with
  | zero =>
      change Fintype.card (X → Bool) = 2 ^ (Fintype.card X * 1)
      rw [Fintype.card_fun, Fintype.card_bool, Nat.mul_one]
  | succ r ih =>
      change Fintype.card ((X → Bool) × (AlicePlan X r × AlicePlan X r) ×
        (AlicePlan X r × AlicePlan X r)) = _
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, ih]
      simp only [← pow_add]
      congr 1
      simp [aliceNodes]
      ring

/-- A representative with constant Bob maps. Its catalogue permits all
other Bob maps, so using a representative loses no completion. -/
def AlicePlan.protocol {X : Type u} : (r : ℕ) → AlicePlan X r → Protocol X Unit Bool
  | 0, f => .aNode f (.leaf false) (.leaf true)
  | r + 1, p => .aNode p.1
      (.bNode (fun _ => false) (protocol r p.2.1.1) (protocol r p.2.1.2))
      (.bNode (fun _ => false) (protocol r p.2.2.1) (protocol r p.2.2.2))

theorem AlicePlan.protocol_complete {X : Type u} (r : ℕ) (p : AlicePlan X r) :
    IsComplete (p.protocol r) (2 * r + 1) := by
  induction r with
  | zero => exact ⟨trivial, trivial⟩
  | succ r ih =>
      have hd : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
      rw [hd]
      exact ⟨⟨ih _, ih _⟩, ⟨ih _, ih _⟩⟩

theorem AlicePlan.protocol_alternates {X : Type u} (r : ℕ) (p : AlicePlan X r) :
    Alternates .alice (p.protocol r) := by
  induction r with
  | zero => exact ⟨trivial, trivial⟩
  | succ r ih => exact ⟨⟨ih _, ih _⟩, ⟨ih _, ih _⟩⟩

theorem AlicePlan.protocol_canonical {X : Type u} (r : ℕ) (p : AlicePlan X r) :
    CanonicalLastLeaves (2 * r + 1) (p.protocol r) := by
  induction r with
  | zero => exact ⟨rfl, rfl⟩
  | succ r ih =>
      have hd : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by omega
      rw [hd]
      exact ⟨⟨ih _, ih _⟩, ⟨ih _, ih _⟩⟩

/-- The finite plan enumeration covers every complete normalized protocol;
it forgets only Bob's local maps, which do not affect the column catalogue. -/
theorem exists_alicePlan_forget {X Y : Type*} (r : ℕ) (P : Protocol X Y Bool)
    (hc : IsComplete P (2 * r + 1)) (ha : Alternates .alice P)
    (hn : CanonicalLastLeaves (2 * r + 1) P) :
    ∃ p : AlicePlan X r, PartialProtocol.forget P = PartialProtocol.forget (p.protocol r) := by
  induction r generalizing P with
  | zero =>
      obtain ⟨f, l, q, rfl⟩ := alice_root_of_complete P 0 hc ha
      rcases hn with ⟨rfl, rfl⟩
      exact ⟨f, rfl⟩
  | succ r ih =>
      have hd : 2 * (r + 1) + 1 = ((2 * r + 1) + 1) + 1 := by omega
      rw [hd] at hc hn
      obtain ⟨f, l, q, rfl⟩ := alice_root_of_complete P ((2 * r + 1) + 1) hc ha
      cases l with
      | leaf b => exact False.elim hc.1
      | aNode f' l' r' => exact False.elim ha.1
      | bNode b ll lr =>
          cases q with
          | leaf b => exact False.elim hc.2
          | aNode f' l' r' => exact False.elim ha.2
          | bNode b' ql qr =>
              have hcanon :
                  (CanonicalLastLeaves (2 * r + 1) ll ∧ CanonicalLastLeaves (2 * r + 1) lr) ∧
                  (CanonicalLastLeaves (2 * r + 1) ql ∧ CanonicalLastLeaves (2 * r + 1) qr) := by
                simpa only [CanonicalLastLeaves] using hn
              obtain ⟨pll, hll⟩ := ih ll hc.1.1 ha.1.1 hcanon.1.1
              obtain ⟨plr, hlr⟩ := ih lr hc.1.2 ha.1.2 hcanon.1.2
              obtain ⟨pql, hql⟩ := ih ql hc.2.1 ha.2.1 hcanon.2.1
              obtain ⟨pqr, hqr⟩ := ih qr hc.2.2 ha.2.2 hcanon.2.2
              refine ⟨(f, (pll, plr), (pql, pqr)), ?_⟩
              simp only [AlicePlan.protocol, PartialProtocol.forget, hll, hlr, hql, hqr]

/-- Extend a map off the retained rows using a fixed default bit. This
extension is used only in the union-bound proof, never by the sampler. -/
def extendAliceMap {X : Type*} [DecidableEq X] (J : Finset X) (f : J → Bool) : X → Bool :=
  fun x => if h : x ∈ J then f ⟨x, h⟩ else false

def AlicePlan.extend {X : Type*} [DecidableEq X] (J : Finset X) :
    (r : ℕ) → AlicePlan J r → AlicePlan X r
  | 0, f => extendAliceMap J f
  | r + 1, p => (extendAliceMap J p.1,
      (extend J r p.2.1.1, extend J r p.2.1.2),
      (extend J r p.2.2.1, extend J r p.2.2.2))

theorem AlicePlan.comap_extend {X : Type*} [DecidableEq X]
    (J : Finset X) (r : ℕ) (p : AlicePlan J r) :
    Workspace.UpperBound.Protocol.comap (fun x : J => x.val) id
      ((p.extend J r).protocol r) = p.protocol r := by
  have he (f : J → Bool) : (fun x : J => extendAliceMap J f x.val) = f := by
    funext x
    simp only [extendAliceMap, dif_pos x.property]
  induction r with
  | zero => simp only [AlicePlan.extend, AlicePlan.protocol,
      Workspace.UpperBound.Protocol.comap, he]
  | succ r ih =>
      simp only [AlicePlan.extend, AlicePlan.protocol,
        Workspace.UpperBound.Protocol.comap, he]
      exact congrArg₂ (Protocol.aNode p.1)
        (congrArg₂ (Protocol.bNode (fun _ : Unit => false)) (ih _) (ih _))
        (congrArg₂ (Protocol.bNode (fun _ : Unit => false)) (ih _) (ih _))

/-- Independent fair bits at every payload position. -/
noncomputable def payloadLaw (X : Type*) [Fintype X] [DecidableEq X] : FiniteLaw (X → Bool) :=
  FiniteLaw.pi (fun _ : X => FiniteLaw.uniform Bool)

theorem payload_prob_finset {X : Type*} [Fintype X] [DecidableEq X] (C : Finset (X → Bool)) :
    (payloadLaw X).prob (fun x => x ∈ C) = (C.card : ℝ) * (1 / 2 : ℝ) ^ Fintype.card X := by
  classical
  have hw (x : X → Bool) : (payloadLaw X).weight x = (1 / 2 : ℝ) ^ Fintype.card X := by
    simp [payloadLaw, FiniteLaw.pi, FiniteLaw.uniform]
  simp only [FiniteLaw.prob, hw]
  simp

theorem payload_prob_restrict {X : Type*} [Fintype X] [DecidableEq X] (J : Finset X)
    (E : (J → Bool) → Prop) :
    (payloadLaw X).prob (fun w => E (fun x : J => w x.val)) =
      (payloadLaw J).prob E := by
  classical
  exact FiniteLaw.pi_prob_restrict _ Subtype.val Subtype.val_injective E

/-- One fixed normalized protocol, one retained set and one common early
strategy: its compatible probability is bounded by the proven catalogue.
No independence or lower-bound conclusion is assumed for the retained set. -/
theorem payload_fixed_test_le {X Y : Type*} [Fintype X] [DecidableEq X]
    (t a : ℕ) (ht : 1 ≤ t) (P : Protocol X Y Bool) (J : Finset X)
    (hc : IsComplete P ((2 * t - 1) + 2 * a)) (ha : Alternates .alice P)
    (hn : CanonicalLastLeaves ((2 * t - 1) + 2 * a) P)
    (σ : ResponseStrategy t) (hσ : ∀ x ∈ J, earlyStrategy t P x = σ) :
    (payloadLaw X).prob (fun w => (fun x : J => w x.val) ∈
      columnCatalogue (Workspace.UpperBound.Protocol.comap
        (fun x : J => x.val) id P)) ≤
      (2 : ℝ) ^ (2 ^ a + t - 2) * (1 / 2 : ℝ) ^ J.card := by
  classical
  rw [payload_prob_restrict, payload_prob_finset]
  have hb := common_strategy_capacity t a ht
    (Workspace.UpperBound.Protocol.comap (fun x : J => x.val) id P)
    (isComplete_comap P _ _ _ hc) (alternates_comap P _ _ _ ha)
    (canonicalLastLeaves_comap P _ _ _ hn) σ (by
      intro x
      simpa [earlyStrategy_comap] using hσ x.val x.property)
  simpa only [Fintype.card_coe, Nat.cast_pow, Nat.cast_ofNat] using
    mul_le_mul_of_nonneg_right (show
      ((columnCatalogue (Workspace.UpperBound.Protocol.comap
        (fun x : J => x.val) id P)).card : ℝ) ≤ (2 : ℝ) ^ (2 ^ a + t - 2) by
      exact_mod_cast hb)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (Fintype.card J))

/-- A capacity deficit of `delta` gives the exact dyadic probability bound. -/
theorem dyadic_capacity_deficit (c j delta : ℕ) (h : c + delta ≤ j) :
    (2 : ℝ) ^ c * (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ delta := by
  rw [one_div_pow, mul_one_div, one_div_pow]
  apply (div_le_div_iff₀ (pow_pos (by norm_num) j) (pow_pos (by norm_num) delta)).mpr
  rw [one_mul, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h

/-- The fixed test checks a genuine retained set and a genuine assignment
of Alice maps. Its common strategy may be chosen after seeing the test. -/
def payloadTest {X : Type*} [Fintype X] [DecidableEq X]
    (r t jmin : ℕ) (p : AlicePlan X r) (J : Finset X) (w : X → Bool) : Prop :=
  jmin ≤ J.card ∧
    (∃ σ : ResponseStrategy t, ∀ x ∈ J, earlyStrategy t (p.protocol r) x = σ) ∧
    (fun x : J => w x.val) ∈ columnCatalogue
      (Workspace.UpperBound.Protocol.comap (fun x : J => x.val) id (p.protocol r))

theorem payload_test_prob_le {X : Type*} [Fintype X] [DecidableEq X]
    (r t a jmin delta : ℕ) (ht : 1 ≤ t)
    (hd : 2 * r + 1 = (2 * t - 1) + 2 * a)
    (hgap : (2 ^ a + t - 2) + delta ≤ jmin)
    (p : AlicePlan X r) (J : Finset X) :
    (payloadLaw X).prob (payloadTest r t jmin p J) ≤ (1 / 2 : ℝ) ^ delta := by
  classical
  by_cases hj : jmin ≤ J.card
  · by_cases hs : ∃ σ : ResponseStrategy t,
        ∀ x ∈ J, earlyStrategy t (p.protocol r) x = σ
    · obtain ⟨σ, hσ⟩ := hs
      have hb := payload_fixed_test_le t a ht (p.protocol r) J
        (hd ▸ p.protocol_complete r) (p.protocol_alternates r)
        (hd ▸ p.protocol_canonical r) σ hσ
      apply (FiniteLaw.prob_mono (payloadLaw X) (fun _ hw => hw.2.2)).trans
      exact hb.trans (dyadic_capacity_deficit _ _ _ (hgap.trans hj))
    · have he : payloadTest r t jmin p J = fun _ => False := by
        funext w
        exact propext ⟨fun h => hs h.2.1, False.elim⟩
      rw [he, FiniteLaw.prob_false]
      positivity
  · have he : payloadTest r t jmin p J = fun _ => False := by
      funext w
      exact propext ⟨fun h => hj h.1, False.elim⟩
    rw [he, FiniteLaw.prob_false]
    positivity

theorem card_payload_tests (X : Type*) [Fintype X] [DecidableEq X] (r : ℕ) :
    Fintype.card (AlicePlan X r × Finset X) =
      2 ^ (Fintype.card X * (aliceNodes r + 1)) := by
  rw [Fintype.card_prod, card_alicePlan, Fintype.card_finset, ← pow_add]
  congr 1

/-- The simultaneous payload event. The quantifiers range over all retained
sets and all normalized Alice maps, not over choices fixed before sampling.
The sample budget is a transparent integer inequality, not an event or
capacity certificate. -/
theorem payload_all_tests_failure_le {X : Type*} [Fintype X] [DecidableEq X]
    (r t a jmin delta samples lambda : ℕ) (ht : 1 ≤ t)
    (hd : 2 * r + 1 = (2 * t - 1) + 2 * a)
    (hgap : (2 ^ a + t - 2) + delta ≤ jmin)
    (hbudget : Fintype.card X * (aliceNodes r + 1) + lambda ≤ delta * samples) :
    ((payloadLaw X).iid samples).prob
      (fun ws => ∃ p : AlicePlan X r, ∃ J : Finset X,
        ∀ l, payloadTest r t jmin p J (ws l)) ≤ (1 / 2 : ℝ) ^ lambda := by
  classical
  have hb := FiniteLaw.iid_prob_some_domain_le (payloadLaw X) samples
    (Finset.univ : Finset (AlicePlan X r × Finset X))
    (fun z => payloadTest r t jmin z.1 z.2) ((1 / 2 : ℝ) ^ delta)
    (fun z _ => payload_test_prob_le r t a jmin delta ht hd hgap z.1 z.2)
  have he : (fun ws : Fin samples → (X → Bool) =>
      ∃ z ∈ (Finset.univ : Finset (AlicePlan X r × Finset X)),
        ∀ l, payloadTest r t jmin z.1 z.2 (ws l)) =
      (fun ws => ∃ p : AlicePlan X r, ∃ J : Finset X,
        ∀ l, payloadTest r t jmin p J (ws l)) := by
    funext ws
    simp
  rw [he] at hb
  apply hb.trans
  rw [Finset.card_univ, card_payload_tests, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
  exact dyadic_capacity_deficit _ _ _ hbudget

/-- The actual bad event for complete normalized protocols on sampled
lookup tables. Bob sees sample labels, including repeated payload values.
Both the retained positions and the protocol may be chosen after sampling. -/
def payloadProtocolFailure {X : Type*} [Fintype X] [DecidableEq X]
    (r t jmin samples : ℕ) (ws : Fin samples → (X → Bool)) : Prop :=
  ∃ J : Finset X, jmin ≤ J.card ∧
    ∃ P : Protocol J (Fin samples) Bool,
      IsComplete P (2 * r + 1) ∧ Alternates .alice P ∧
      CanonicalLastLeaves (2 * r + 1) P ∧
      (∃ σ : ResponseStrategy t, ∀ x, earlyStrategy t P x = σ) ∧
      ∀ x l, P.eval x l = ws l x.val

theorem payloadProtocolFailure_covered {X : Type*} [Fintype X] [DecidableEq X]
    (r t jmin samples : ℕ) (ws : Fin samples → (X → Bool))
    (h : payloadProtocolFailure r t jmin samples ws) :
    ∃ p : AlicePlan X r, ∃ J : Finset X,
      ∀ l, payloadTest r t jmin p J (ws l) := by
  classical
  obtain ⟨J, hj, P, hc, ha, hn, ⟨σ, hσ⟩, he⟩ := h
  obtain ⟨p, hp⟩ := exists_alicePlan_forget r P hc ha hn
  have hcata := catalogue_eq_of_forget_eq hp
  refine ⟨p.extend J r, J, ?_⟩
  intro l
  refine ⟨hj, ⟨σ, ?_⟩, ?_⟩
  · intro x hx
    have hcmap := congrArg (fun Q => earlyStrategy t Q (⟨x, hx⟩ : J))
      (p.comap_extend J r)
    dsimp only at hcmap
    rw [earlyStrategy_comap] at hcmap
    rw [hcmap]
    rw [← Partial.earlyStrategy_forget, ← hp, Partial.earlyStrategy_forget]
    exact hσ ⟨x, hx⟩
  · rw [AlicePlan.comap_extend, ← hcata]
    have hm := actualColumn_mem_catalogue P l
    simpa only [he] using hm

/-- The payload half of the sampling lemma for actual normalized lookup
protocols, with explicit integer capacity and sample-budget conditions. -/
theorem payload_protocol_failure_le {X : Type*} [Fintype X] [DecidableEq X]
    (r t a jmin delta samples lambda : ℕ) (ht : 1 ≤ t)
    (hd : 2 * r + 1 = (2 * t - 1) + 2 * a)
    (hgap : (2 ^ a + t - 2) + delta ≤ jmin)
    (hbudget : Fintype.card X * (aliceNodes r + 1) + lambda ≤ delta * samples) :
    ((payloadLaw X).iid samples).prob
      (payloadProtocolFailure r t jmin samples) ≤ (1 / 2 : ℝ) ^ lambda := by
  apply (FiniteLaw.prob_mono _ (payloadProtocolFailure_covered r t jmin samples)).trans
  exact payload_all_tests_failure_le r t a jmin delta samples lambda ht hd hgap hbudget

/-! ## The manuscript's dyadic parameters and exact sample ceiling -/

theorem aliceNodes_closed (r : ℕ) : 3 * aliceNodes r + 1 = 2 ^ (2 * r + 2) := by
  induction r with
  | zero => norm_num [aliceNodes]
  | succ r ih =>
      have he : 2 * (r + 1) + 2 = (2 * r + 2) + 2 := by omega
      rw [he, pow_add]
      norm_num only [pow_two, Nat.reduceMul]
      simp only [aliceNodes]
      omega

def payloadDelta (b t : ℕ) : ℕ := 2 ^ (b + (t - 4))

def payloadMinimum (b t : ℕ) : ℕ := 2 ^ (b + 2 * t - 2) + 2 * payloadDelta b t + 1

/-- This is precisely the integer ceiling in the paper, not a search for
a good sample and not an expected number of draws. -/
def payloadSampleCount (n r delta lambda : ℕ) : ℕ :=
  (n * (aliceNodes r + 1) + lambda + delta - 1) / delta

theorem payloadSampleCount_budget (n r delta lambda : ℕ) (hd : 0 < delta) :
    n * (aliceNodes r + 1) + lambda ≤ delta * payloadSampleCount n r delta lambda := by
  exact (ceilDiv_le_iff_le_mul hd).mp (show
    (n * (aliceNodes r + 1) + lambda) ⌈/⌉ delta ≤
      payloadSampleCount n r delta lambda from le_rfl)

theorem payloadDelta_positive (b t : ℕ) : 0 < payloadDelta b t := by
  exact pow_pos (by decide) _

theorem payloadDelta_source (b t : ℕ) (ht : 4 ≤ t) :
    payloadDelta b t = (2 ^ t * 2 ^ b) / 16 := by
  have he : t + b = (b + (t - 4)) + 4 := by omega
  rw [← pow_add, he, pow_add]
  norm_num only [Nat.reducePow]
  exact (Nat.mul_div_cancel _ (by decide : 0 < 16)).symm

theorem payloadMinimum_source (b t : ℕ) (ht : 4 ≤ t) :
    payloadMinimum b t =
      (2 ^ (2 * t) * 2 ^ b) / 4 + (2 ^ t * 2 ^ b) / 8 + 1 := by
  have he : 2 * t + b = (b + 2 * t - 2) + 2 := by omega
  have hf : t + b = (b + (t - 4)) + 3 + 1 := by omega
  have hfour : (2 ^ (2 * t) * 2 ^ b) / 4 = 2 ^ (b + 2 * t - 2) := by
    rw [← pow_add, he, pow_add]
    norm_num only [Nat.reducePow]
    exact Nat.mul_div_cancel _ (by decide : 0 < 4)
  have height : (2 ^ t * 2 ^ b) / 8 = 2 * 2 ^ (b + (t - 4)) := by
    rw [← pow_add, hf, pow_add, pow_add]
    norm_num only [Nat.reducePow]
    rw [show (2 ^ (b + (t - 4)) * 8) * 2 =
      (2 * 2 ^ (b + (t - 4))) * 8 by ring, Nat.mul_div_cancel _ (by decide : 0 < 8)]
  rw [hfour, height]
  rfl

private theorem linear_le_pow_two (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem payload_strategy_slack (b t : ℕ) (ht : 4 ≤ t) : t ≤ payloadDelta b t + 3 := by
  have hp := linear_le_pow_two (t - 4)
  have hm : 2 ^ (t - 4) ≤ 2 ^ (b + (t - 4)) :=
    Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)
  unfold payloadDelta
  omega

theorem payload_parameter_gap (b t : ℕ) (ht : 4 ≤ t) :
    (2 ^ (b + 2 * t - 2) + t - 2) + payloadDelta b t ≤ payloadMinimum b t := by
  have hs := payload_strategy_slack b t ht
  have hp : 1 ≤ 2 ^ (b + 2 * t - 2) := Nat.one_le_pow _ _ (by decide)
  unfold payloadMinimum
  omega

/-- The explicit source count gives the payload failure probability claimed
in T29(ii), for the normalized complete form. The carrier can be any indexed
set of payload positions; its actual cardinality sets the public budget. -/
theorem payload_explicit_counts_failure_le {X : Type*} [Fintype X] [DecidableEq X]
    (b t lambda : ℕ) (ht : 4 ≤ t) :
    let r := b + 3 * t - 3
    let m := payloadSampleCount (Fintype.card X) r (payloadDelta b t) lambda
    ((payloadLaw X).iid m).prob
      (payloadProtocolFailure r t (payloadMinimum b t) m) ≤ (1 / 2 : ℝ) ^ lambda := by
  dsimp only
  apply payload_protocol_failure_le (b + 3 * t - 3) t (b + 2 * t - 2)
    (payloadMinimum b t) (payloadDelta b t)
  · omega
  · omega
  · exact payload_parameter_gap b t ht
  · exact payloadSampleCount_budget _ _ _ _ (payloadDelta_positive b t)

end Paper2.Yao
