import Paper2.YaoNormalization
import Paper2.YaoStrategyCard
import Paper2.ProtocolDomains

/-!
# Early Alice strategies on all hypothetical Bob histories

Statement source: locked Paper 2 v12, `sections/07-yao.tex:172--202`,
including `yao:strategy-count` (T27). A strategy is extracted from an actual
protocol: Alice follows her actual local message, while both possible Bob
replies are explored. Bob's message maps are ignored, not fixed to their
values on one sampled column. The connection to complete alternating
protocols is explicit below.

The complete finite strategy type is counted in `YaoStrategyCard`; this
module proves that the actual strategies belong to that type and gives
their exact hypothetical-history semantics. No capacity or hardness claim
is assumed or proved merely from the strategy-type cardinality.
-/

namespace Paper2.Yao

open Workspace.Types.Protocol

universe u v
variable {X : Type u} {Y : Type v}

/-- Alice's actual root message. The fallback value only totalizes the
definition; a legal positive-depth Alice-starting tree has an Alice root. -/
def aliceMessage : Protocol X Y Bool → X → Bool
  | .aNode a _ _, x => a x
  | _, _ => false

/-- Follow Alice's actual bit. At a non-Alice root, leave the tree unchanged. -/
def afterAlice : Protocol X Y Bool → X → Protocol X Y Bool
  | .aNode a l r, x => if a x then r else l
  | P, _ => P

/-- Follow a hypothetical Bob bit, irrespective of Bob's map or local input. -/
def afterBob : Protocol X Y Bool → Bool → Protocol X Y Bool
  | .bNode _ l r, b => if b then r else l
  | P, _ => P

/-- One Alice--Bob pair, using the real Alice input and a prescribed Bob bit. -/
def afterRound (P : Protocol X Y Bool) (x : X) (b : Bool) : Protocol X Y Bool :=
  afterBob (afterAlice P x) b

/-- Residual tree after the supplied hypothetical Bob history. Alice's own
previous messages are determined recursively from her input. -/
def afterHistory (P : Protocol X Y Bool) (x : X) : List Bool → Protocol X Y Bool
  | [] => P
  | b :: bs => afterHistory (afterRound P x b) x bs

/-- Full early strategy, extracted without consulting any Bob input. The
two stored continuations are both explored, even if one cannot occur for
any column under the particular Bob maps in the starting tree. -/
def earlyStrategy : (t : ℕ) → Protocol X Y Bool → X → ResponseStrategy t
  | 0, _, _ => PUnit.unit
  | t + 1, P, x =>
      (aliceMessage P x, earlyStrategy t (afterRound P x false) x,
        earlyStrategy t (afterRound P x true) x)

namespace ResponseStrategy

/-- Read the response at a hypothetical Bob history. Histories reaching or
exceeding the number of stored Alice turns return `none`. -/
def response : {t : ℕ} → ResponseStrategy t → List Bool → Option Bool
  | 0, _, _ => none
  | _ + 1, σ, [] => some σ.1
  | _ + 1, σ, false :: bs => response σ.2.1 bs
  | _ + 1, σ, true :: bs => response σ.2.2 bs

theorem response_some {t : ℕ} (σ : ResponseStrategy t) (bs : List Bool)
    (h : bs.length < t) : ∃ b, σ.response bs = some b := by
  induction bs generalizing t with
  | nil => cases t <;> simp_all [response]
  | cons b bs ih =>
      cases t with
      | zero => simp at h
      | succ t =>
          cases b <;> apply ih <;> simpa using h

theorem response_none_of_le {t : ℕ} (σ : ResponseStrategy t) (bs : List Bool)
    (h : t ≤ bs.length) : σ.response bs = none := by
  induction bs generalizing t with
  | nil => cases t <;> simp_all [response]
  | cons b bs ih =>
      cases t with
      | zero => rfl
      | succ t => cases b <;> apply ih <;> simpa using h

end ResponseStrategy

/-- Every stored response is the actual local message at the corresponding
residual protocol reached by that hypothetical Bob history. -/
theorem earlyStrategy_response (t : ℕ) (P : Protocol X Y Bool) (x : X)
    (bs : List Bool) (h : bs.length < t) :
    (earlyStrategy t P x).response bs = some (aliceMessage (afterHistory P x bs) x) := by
  induction bs generalizing t P with
  | nil => cases t <;> simp_all [earlyStrategy, ResponseStrategy.response, afterHistory]
  | cons b bs ih =>
      cases t with
      | zero => simp at h
      | succ t =>
          cases b <;>
            simpa [earlyStrategy, ResponseStrategy.response, afterHistory] using
              ih t (afterRound P x _) (by simpa using h)

/-- Equal strategies mean equal responses at every hypothetical history,
including histories not realized by any input column. -/
theorem equal_earlyStrategy_response {t : ℕ} {P Q : Protocol X Y Bool} {x x' : X}
    (hσ : earlyStrategy t P x = earlyStrategy t Q x')
    (bs : List Bool) (hlen : bs.length < t) :
    aliceMessage (afterHistory P x bs) x = aliceMessage (afterHistory Q x' bs) x' := by
  have h := congrArg (fun σ : ResponseStrategy t => σ.response bs) hσ
  change (earlyStrategy t P x).response bs = (earlyStrategy t Q x').response bs at h
  rw [earlyStrategy_response _ _ _ _ hlen, earlyStrategy_response _ _ _ _ hlen] at h
  exact Option.some.inj h

/-- Positive-depth legality rules out the fallback in `aliceMessage`. -/
theorem alice_root_of_complete (P : Protocol X Y Bool) (d : ℕ)
    (hc : IsComplete P (d + 1)) (ha : Alternates .alice P) :
    ∃ a l r, P = .aNode a l r := by
  cases P with
  | leaf b => exact False.elim hc
  | aNode a l r => exact ⟨a, l, r, rfl⟩
  | bNode b l r => exact False.elim ha

theorem afterAlice_complete (P : Protocol X Y Bool) (x : X) (d : ℕ)
    (hc : IsComplete P (d + 1)) (ha : Alternates .alice P) :
    IsComplete (afterAlice P x) d ∧ Alternates .bob (afterAlice P x) := by
  obtain ⟨a, l, r, rfl⟩ := alice_root_of_complete P d hc ha
  cases hx : a x <;> simp [afterAlice, hx, hc.1, hc.2, ha.1, ha.2]

theorem afterBob_complete (P : Protocol X Y Bool) (b : Bool) (d : ℕ)
    (hc : IsComplete P (d + 1)) (ha : Alternates .bob P) :
    IsComplete (afterBob P b) d ∧ Alternates .alice (afterBob P b) := by
  cases P with
  | leaf c => exact False.elim hc
  | aNode a l r => exact False.elim ha
  | bNode f l r => cases b <;> simp [afterBob, hc.1, hc.2, ha.1, ha.2]

theorem afterRound_complete (P : Protocol X Y Bool) (x : X) (b : Bool) (d : ℕ)
    (hc : IsComplete P (d + 2)) (ha : Alternates .alice P) :
    IsComplete (afterRound P x b) d ∧ Alternates .alice (afterRound P x b) := by
  have h1 := afterAlice_complete P x (d + 1) hc ha
  exact afterBob_complete (afterAlice P x) b d h1.1 h1.2

/-- All hypothetical prefixes stay inside legal Alice-starting trees, with
the exact remaining depth. No existence of a realizing Bob input is needed. -/
theorem afterHistory_complete (P : Protocol X Y Bool) (x : X) (bs : List Bool) (d : ℕ)
    (hc : IsComplete P (2 * bs.length + d)) (ha : Alternates .alice P) :
    IsComplete (afterHistory P x bs) d ∧ Alternates .alice (afterHistory P x bs) := by
  induction bs generalizing P with
  | nil => simpa [afterHistory] using And.intro hc ha
  | cons b bs ih =>
      have hc' : IsComplete P ((2 * bs.length + d) + 2) := by
        convert hc using 1
        simp [List.length_cons]
        omega
      have h1 := afterRound_complete P x b (2 * bs.length + d) hc' ha
      exact ih (afterRound P x b) h1.1 h1.2

/-! Bob's completion maps do not affect the extracted strategy. -/

namespace Partial

open Paper2.PartialProtocol

def aliceMessage : PartialProtocol X → X → Bool
  | .alice a _ _, x => a x
  | _, _ => false

def afterAlice : PartialProtocol X → X → PartialProtocol X
  | .alice a l r, x => if a x then r else l
  | P, _ => P

def afterBob : PartialProtocol X → Bool → PartialProtocol X
  | .bob l r, b => if b then r else l
  | P, _ => P

def afterRound (P : PartialProtocol X) (x : X) (b : Bool) : PartialProtocol X :=
  afterBob (afterAlice P x) b

def earlyStrategy : (t : ℕ) → PartialProtocol X → X → ResponseStrategy t
  | 0, _, _ => PUnit.unit
  | t + 1, P, x =>
      (aliceMessage P x, earlyStrategy t (afterRound P x false) x,
        earlyStrategy t (afterRound P x true) x)

theorem forget_aliceMessage (P : Protocol X Y Bool) (x : X) :
    aliceMessage (PartialProtocol.forget P) x = Yao.aliceMessage P x := by
  cases P <;> rfl

theorem forget_afterAlice (P : Protocol X Y Bool) (x : X) :
    PartialProtocol.forget (Yao.afterAlice P x) = afterAlice (PartialProtocol.forget P) x := by
  cases P with
  | leaf b => rfl
  | aNode a l r => cases h : a x <;> simp [Yao.afterAlice, afterAlice, PartialProtocol.forget, h]
  | bNode b l r => rfl

theorem forget_afterBob (P : Protocol X Y Bool) (b : Bool) :
    PartialProtocol.forget (Yao.afterBob P b) = afterBob (PartialProtocol.forget P) b := by
  cases P with
  | leaf c => rfl
  | aNode a l r => rfl
  | bNode f l r => cases b <;> rfl

theorem forget_afterRound (P : Protocol X Y Bool) (x : X) (b : Bool) :
    PartialProtocol.forget (Yao.afterRound P x b) = afterRound (PartialProtocol.forget P) x b := by
  rw [Yao.afterRound, forget_afterBob, forget_afterAlice]
  rfl

theorem earlyStrategy_forget (t : ℕ) (P : Protocol X Y Bool) (x : X) :
    earlyStrategy t (PartialProtocol.forget P) x = Yao.earlyStrategy t P x := by
  induction t generalizing P with
  | zero => rfl
  | succ t ih =>
      simp only [earlyStrategy, Yao.earlyStrategy, forget_aliceMessage]
      rw [← forget_afterRound, ← forget_afterRound, ih, ih]

/-- The actual strategy on a completed protocol depends only on Alice's
fixed maps. This holds uniformly over all Bob completions and column types. -/
theorem earlyStrategy_complete (t : ℕ) (P : PartialProtocol X)
    (c : P.Completion Y) (x : X) :
    Yao.earlyStrategy t (P.complete c) x = earlyStrategy t P x := by
  have hf : PartialProtocol.forget (P.complete c) = P := by
    induction P with
    | leaf b => rfl
    | alice a l r ihl ihr => simp [PartialProtocol.complete, PartialProtocol.forget, ihl, ihr]
    | bob l r ihl ihr => simp [PartialProtocol.complete, PartialProtocol.forget, ihl, ihr]
  rw [← earlyStrategy_forget, hf]

end Partial

/-- T27: the set of concrete strategies extracted from any row set has at
most the exact strategy alphabet size. No finiteness of the row carrier
is required, since the codomain itself is finite. -/
theorem earlyStrategies_card_le (t : ℕ) (P : Protocol X Y Bool) (U : Set X) :
    ((fun x => earlyStrategy t P x) '' U).ncard ≤ 2 ^ (2 ^ t - 1) := by
  have h := Set.ncard_le_card ((fun x => earlyStrategy t P x) '' U)
  simpa [responseStrategy_card] using h

theorem partial_earlyStrategies_card_le (t : ℕ) (P : PartialProtocol X) (U : Set X) :
    ((fun x => Partial.earlyStrategy t P x) '' U).ncard ≤ 2 ^ (2 ^ t - 1) := by
  have h := Set.ncard_le_card ((fun x => Partial.earlyStrategy t P x) '' U)
  simpa [responseStrategy_card] using h

/-- Two Alice turns really store the root bit and both possible responses
to the first Bob reply, not only the reply selected by one input column. -/
def twoTurnExample : Protocol (Bool × Bool) Unit Bool :=
  .aNode (fun _ => true)
    (.bNode (fun _ => false)
      (.aNode Prod.fst (.leaf false) (.leaf true))
      (.aNode Prod.snd (.leaf false) (.leaf true)))
    (.bNode (fun _ => false)
      (.aNode Prod.fst (.leaf false) (.leaf true))
      (.aNode Prod.snd (.leaf false) (.leaf true)))

theorem twoTurnExample_strategy :
    earlyStrategy 2 twoTurnExample (false, true) =
      (true, (false, PUnit.unit, PUnit.unit), (true, PUnit.unit, PUnit.unit)) := rfl

/-- Bob always sends zero in the example, yet the hypothetical one-branch
response is present and correctly extracted. -/
theorem unreachable_bob_history_recorded :
    (earlyStrategy 2 twoTurnExample (false, true)).response [true] = some true := rfl

end Paper2.Yao
