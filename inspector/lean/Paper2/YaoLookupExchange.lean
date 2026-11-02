import Paper2.YaoModel

/-!
# Alternating exchange of two fixed-length bit strings

Statement source: Paper 2, locked `2026-09-22-protocol-labels-v12`,
`sections/07-yao.tex`, the short protocol preceding `yao:budget`.

The schedule there exchanges two strings in alternating pairs, then continues
using the publicly transmitted strings. This module constructs the actual
protocol tree for that operation, for either starter. The continuation is
chosen from the transcript, not from uncommunicated private data. Zero-length
strings consume no bits. No hardness or source-construction claim is made.
-/

namespace Paper2.Yao.StrictProtocol

open Workspace.Types.Protocol

universe u v
variable {X : Type u} {Y : Type v}

/-- One message from each player, in the order specified by `s`. The four
continuations are indexed by Alice's and Bob's transmitted bits, respectively.
After two turns the next scheduled speaker is again `s`. -/
def exchangePair (s : Turn) (a : X → Bool) (b : Y → Bool)
    (K : Bool → Bool → StrictProtocol X Y s) : StrictProtocol X Y s :=
  match s with
  | .alice => alice a (bob b (K false false) (K false true))
      (bob b (K true false) (K true true))
  | .bob => bob b (alice a (K false false) (K true false))
      (alice a (K false true) (K true true))

@[simp] theorem exchangePair_eval (s : Turn) (a : X → Bool) (b : Y → Bool)
    (K : Bool → Bool → StrictProtocol X Y s) (x : X) (y : Y) :
    (exchangePair s a b K).eval x y = (K (a x) (b y)).eval x y := by
  cases s <;> cases ha : a x <;> cases hb : b y <;>
    simp [exchangePair, alice, bob, eval, Protocol.eval, ha, hb]

theorem exchangePair_cost_le (s : Turn) (a : X → Bool) (b : Y → Bool)
    (K : Bool → Bool → StrictProtocol X Y s) (L : ℕ)
    (hK : ∀ u v, (K u v).cost ≤ L) :
    (exchangePair s a b K).cost ≤ 2 + L := by
  have h00 := hK false false
  have h01 := hK false true
  have h10 := hK true false
  have h11 := hK true true
  cases s <;>
    simp only [exchangePair, alice, bob, cost, Protocol.cost] at * <;> omega

/-- Alternating exchange of two `n`-bit strings. Each pair reveals their
next coordinates. The final continuation receives the two complete strings,
including their values along branches that no input realizes. -/
def exchange : (n : ℕ) → (s : Turn) →
    (X → Fin n → Bool) → (Y → Fin n → Bool) →
    ((Fin n → Bool) → (Fin n → Bool) → StrictProtocol X Y s) →
    StrictProtocol X Y s
  | 0, _, _, _, K => K Fin.elim0 Fin.elim0
  | n + 1, s, a, b, K =>
      exchangePair s (fun x => a x 0) (fun y => b y 0)
        (fun u v => exchange n s (fun x => Fin.tail (a x)) (fun y => Fin.tail (b y))
          (fun u' v' => K (Fin.cons u u') (Fin.cons v v')))

@[simp] theorem exchange_eval (n : ℕ) (s : Turn)
    (a : X → Fin n → Bool) (b : Y → Fin n → Bool)
    (K : (Fin n → Bool) → (Fin n → Bool) → StrictProtocol X Y s)
    (x : X) (y : Y) :
    (exchange n s a b K).eval x y = (K (a x) (b y)).eval x y := by
  induction n generalizing s with
  | zero =>
      have ha : a x = Fin.elim0 := Subsingleton.elim _ _
      have hb : b y = Fin.elim0 := Subsingleton.elim _ _
      simp [exchange, ha, hb]
  | succ n ih =>
      simp only [exchange, exchangePair_eval, ih, Fin.cons_self_tail]

/-- Every branch of the exchange has `2 * n` charged bits before entering
its selected continuation. This bound also covers unreachable transcripts. -/
theorem exchange_cost_le (n : ℕ) (s : Turn)
    (a : X → Fin n → Bool) (b : Y → Fin n → Bool)
    (K : (Fin n → Bool) → (Fin n → Bool) → StrictProtocol X Y s)
    (L : ℕ) (hK : ∀ u v, (K u v).cost ≤ L) :
    (exchange n s a b K).cost ≤ 2 * n + L := by
  induction n generalizing s with
  | zero => simpa [exchange] using hK Fin.elim0 Fin.elim0
  | succ n ih =>
      apply le_trans (exchangePair_cost_le _ _ _ _ (2 * n + L) ?_)
      · omega
      · intro u v
        exact ih s _ _ _ (fun u' v' => hK (Fin.cons u u') (Fin.cons v v'))

end Paper2.Yao.StrictProtocol
