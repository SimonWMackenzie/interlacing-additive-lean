import Paper2.YaoFrame
import Paper2.YaoResourceBounds

/-! Unit 5 segment Y9-clock (lane a-yao-owner-3): the explicit clocks of the Yao
table machine (`yaoClock`, `yaoT`) and of the framed machine (`frameClock`)
are polynomially bounded in the input length `|encode x|` (hence in
`|encode x| + |bits.val|`), for every fixed `t ≥ 1` and `lambda`.

Method: a closure calculus `PolyIn f := ∃ C d, ∀ x, f x ≤ C * (|encode x| + 1)^d`
(sum, product, truncated difference, constants), plus atom bounds taken by exact
name from the admitted `YaoResourceBounds` (`paddedEdgeCount_lt`,
`bits_le_height`, `selectorCount_le`, `payloadCount_le`, `padded_tapeBitCount_le`,
`aliceNodes_add_one_le`) and the frozen codec's `encode_length`.  Every
clock is unfolded to its literal definition; per-`(t, lambda)` constants such as
`Fintype.card (Clearable t lambda)`, `BitMachineStackGrowth.perStep …`,
`2 ^ (6*t-4)` are kept symbolic (never evaluated). -/

noncomputable section

namespace Paper2.YaoClockPoly

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open Paper2.Yao
open Paper2.YaoLowerBound
open Paper2.YaoLowerBound.Materialization
open Paper2.YaoLookup
open Paper2.YaoMaterialization
open Paper2.YaoSourceCodec
open Paper2.UnaryFieldListParserScratch
open Paper2.RecursiveLabelCodecScratch
open Paper2.YaoPrelude
open Paper2.YaoMachine
open Paper2.YaoFrame
open Paper2.YaoCtrlBlock
open Paper2.YaoOneEntry
open Paper2.YaoEntryControllerJoin

set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

/-- `f` is polynomially bounded in the code length. -/
def PolyIn {t : ℕ} (f : YaoSource t → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ x, f x ≤ C * ((encode x).length + 1) ^ d

section calculus

variable {t : ℕ}

theorem poly_const (c : ℕ) : PolyIn (fun _ : YaoSource t => c) :=
  ⟨c, 0, fun _ => by simp⟩

theorem poly_mono {f g : YaoSource t → ℕ} (h : ∀ x, f x ≤ g x) (hg : PolyIn g) : PolyIn f := by
  obtain ⟨C, d, hC⟩ := hg
  exact ⟨C, d, fun x => (h x).trans (hC x)⟩

theorem pow_mono_n (n a b : ℕ) (hab : a ≤ b) : (n + 1) ^ a ≤ (n + 1) ^ b :=
  Nat.pow_le_pow_right (by omega) hab

theorem poly_add {f g : YaoSource t → ℕ} (hf : PolyIn f) (hg : PolyIn g) :
    PolyIn (fun x => f x + g x) := by
  obtain ⟨C, d, hC⟩ := hf
  obtain ⟨D, e, hD⟩ := hg
  refine ⟨C + D, d + e, fun x => ?_⟩
  have h1 := pow_mono_n (encode x).length d (d + e) (by omega)
  have h2 := pow_mono_n (encode x).length e (d + e) (by omega)
  have := hC x; have := hD x
  calc f x + g x ≤ C * ((encode x).length + 1) ^ d + D * ((encode x).length + 1) ^ e := by omega
    _ ≤ C * ((encode x).length + 1) ^ (d + e) + D * ((encode x).length + 1) ^ (d + e) := by
      gcongr
    _ = (C + D) * ((encode x).length + 1) ^ (d + e) := by ring

theorem poly_mul {f g : YaoSource t → ℕ} (hf : PolyIn f) (hg : PolyIn g) :
    PolyIn (fun x => f x * g x) := by
  obtain ⟨C, d, hC⟩ := hf
  obtain ⟨D, e, hD⟩ := hg
  refine ⟨C * D, d + e, fun x => ?_⟩
  calc f x * g x ≤ (C * ((encode x).length + 1) ^ d) * (D * ((encode x).length + 1) ^ e) :=
        Nat.mul_le_mul (hC x) (hD x)
    _ = C * D * ((encode x).length + 1) ^ (d + e) := by ring

theorem poly_sub {f g : YaoSource t → ℕ} (hf : PolyIn f) : PolyIn (fun x => f x - g x) :=
  poly_mono (fun x => Nat.sub_le _ _) hf

theorem poly_pow {f : YaoSource t → ℕ} (hf : PolyIn f) (k : ℕ) :
    PolyIn (fun x => f x ^ k) := by
  induction k with
  | zero => simpa using poly_const (t := t) 1
  | succ k ih => simpa [pow_succ] using poly_mul ih hf

theorem natField_length_le (n : ℕ) : (natField n).length ≤ 2 * n + 1 := by
  rw [natField, field_length]
  have : n.bits.length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  omega

theorem poly_natField {f : YaoSource t → ℕ} (hf : PolyIn f) :
    PolyIn (fun x => (natField (f x)).length) :=
  poly_mono (fun x => natField_length_le (f x)) (poly_add (poly_mul (poly_const 2) hf) (poly_const 1))

end calculus

/-! ## Atoms -/

section atoms

variable {t : ℕ}

theorem v_le_len (x : YaoSource t) : x.1 ≤ (encode x).length := by
  rw [encode_length]; omega

theorem e_le_len (x : YaoSource t) : x.2.1 ≤ (encode x).length := by
  rw [encode_length]; omega

theorem poly_len : PolyIn (fun x : YaoSource t => (encode x).length) :=
  ⟨1, 1, fun x => by simp⟩

theorem poly_len_nil : PolyIn (fun x : YaoSource t => (encode x ++ []).length) := by
  simpa using poly_len (t := t)

theorem poly_v : PolyIn (fun x : YaoSource t => x.1) := poly_mono v_le_len poly_len

theorem poly_e : PolyIn (fun x : YaoSource t => x.2.1) := poly_mono e_le_len poly_len

theorem poly_H : PolyIn (fun x : YaoSource t => paddedEdgeCount x.2.1) := by
  refine poly_mono (g := fun x => 2 * (encode x).length + 2) (fun x => ?_)
    (poly_add (poly_mul (poly_const 2) poly_len) (poly_const 2))
  show paddedEdgeCount x.2.1 ≤ 2 * (encode x).length + 2
  have h1 := Paper2.YaoResources.paddedEdgeCount_lt x.2.1
  have h2 := e_le_len x
  have : max 1 x.2.1 ≤ (encode x).length + 1 := by omega
  omega

theorem poly_H' : PolyIn (fun x : YaoSource t => 2 ^ paddedEdgeBits x.2.1) := poly_H

theorem poly_b : PolyIn (fun x : YaoSource t => paddedEdgeBits x.2.1) :=
  poly_mono (fun x => Paper2.YaoResources.bits_le_height _) poly_H'

theorem poly_sel (lambda : ℕ) :
    PolyIn (fun x : YaoSource t => selectorCount t (paddedEdgeBits x.2.1) lambda) :=
  poly_mono (fun x => Paper2.YaoResources.selectorCount_le t _ lambda)
    (poly_mul (poly_const _) poly_H')

theorem poly_pay (lambda : ℕ) (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => payloadCount t (paddedEdgeBits x.2.1) lambda) :=
  poly_mono (fun x => Paper2.YaoResources.payloadCount_le t _ lambda ht)
    (poly_mul (poly_const _) (poly_pow poly_H' 2))

theorem poly_tape (lambda : ℕ) (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => tapeBitCount t (paddedEdgeBits x.2.1) lambda) := by
  refine ⟨8 * Paper2.YaoResources.bitCoefficient t lambda, 3, fun x => ?_⟩
  refine (Paper2.YaoResources.padded_tapeBitCount_le t x.2.1 lambda ht).trans ?_
  have h2 := e_le_len x
  have : max 1 x.2.1 ≤ (encode x).length + 1 := by omega
  gcongr

theorem poly_alice (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => aliceNodes (paddedEdgeBits x.2.1 + 3 * t - 3)) :=
  poly_mono (g := fun x => Paper2.YaoResources.treeCoefficient t * (2 ^ paddedEdgeBits x.2.1) ^ 2)
    (fun x => by
      have := Paper2.YaoResources.aliceNodes_add_one_le t (paddedEdgeBits x.2.1) ht
      show aliceNodes (paddedEdgeBits x.2.1 + 3 * t - 3) ≤
        Paper2.YaoResources.treeCoefficient t * (2 ^ paddedEdgeBits x.2.1) ^ 2
      omega)
    (poly_mul (poly_const _) (poly_pow poly_H' 2))

theorem poly_powA :
    PolyIn (fun x : YaoSource t =>
      2 ^ (6 * t - 4 + (paddedEdgeBits x.2.1 + paddedEdgeBits x.2.1))) :=
  poly_mono (fun x => by rw [pow_add, pow_add])
    (poly_mul (poly_const _) (poly_mul poly_H' poly_H'))

theorem poly_powC :
    PolyIn (fun x : YaoSource t => 2 ^ (t - 4 + paddedEdgeBits x.2.1)) :=
  poly_mono (fun x => by rw [pow_add]) (poly_mul (poly_const _) poly_H')

theorem poly_tokens :
    PolyIn (fun x : YaoSource t => (tokens (List.ofFn (flatten x.2.2))).length) := by
  refine poly_mono (fun x => ?_) poly_len
  simp only [encode, bodyCodec, piCodec_encode_eq_tokens, List.length_append]
  omega

end atoms

/-- One structural step of the polynomial-closure calculus, matched syntactically
(reducible transparency): constants, named atoms and hypotheses first, then sum /
product / truncated difference / constant power. -/
macro "poly_step" : tactic => `(tactic| first
  | with_reducible exact poly_const _
  | with_reducible assumption
  | with_reducible exact poly_v
  | with_reducible exact poly_e
  | with_reducible exact poly_H
  | with_reducible exact poly_H'
  | with_reducible exact poly_b
  | with_reducible exact poly_len
  | with_reducible exact poly_len_nil
  | with_reducible exact poly_tokens
  | with_reducible exact poly_powA
  | with_reducible exact poly_powC
  | with_reducible refine poly_natField ?_
  | with_reducible refine poly_add ?_ ?_
  | with_reducible refine poly_mul ?_ ?_
  | with_reducible refine poly_sub ?_
  | with_reducible refine poly_pow ?_ _)

/-! ## The clocks -/

theorem yaoT_poly (t lambda : ℕ) (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => Paper2.YaoEntryRuns.yaoT t lambda x.2.2) := by
  have hpay := poly_pay (t := t) lambda ht
  have htape := poly_tape (t := t) lambda ht
  have hsel := poly_sel (t := t) lambda
  unfold Paper2.YaoEntryRuns.yaoT entryClock coreClock startMax blockClock
    Paper2.YaoUniformClock.controllerUniform
    Paper2.YaoEntryParameterJoin.scalarBudget Paper2.YaoUniformClock.routeCap
    Paper2.YaoEntryParameterJoin.payloadBaseValue Paper2.YaoUniformClock.selectorUniform
    Paper2.YaoUniformClock.payloadUniform
    MatrixTemplateAddressSetup.bound MatrixAddressMachine.exactTime rowCount columnCount
  repeat' poly_step

theorem yaoClock_poly (t lambda : ℕ) (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => yaoClock lambda x) := by
  have hpay := poly_pay (t := t) lambda ht
  have htape := poly_tape (t := t) lambda ht
  have hsel := poly_sel (t := t) lambda
  have halice := poly_alice (t := t) ht
  have hT := yaoT_poly t lambda ht
  unfold yaoClock preludeFullClock preludeClock countClock clearMax countBound payClock
    partAClock partBClock partCClock payX dimsClock MatrixTableWriter.writerBound
    MatrixAddressMachine.exactTime rowCount columnCount
  repeat' poly_step

theorem frameClock_poly (t lambda : ℕ) (ht : 1 ≤ t) :
    PolyIn (fun x : YaoSource t => frameClock lambda x) := by
  have hpay := poly_pay (t := t) lambda ht
  have hsel := poly_sel (t := t) lambda
  have hY := yaoClock_poly t lambda ht
  unfold frameClock rowCount columnCount
  simp only [List.length_append]
  repeat' poly_step

/-- Y9-clock, stated in `|encode x| + |bits.val|`: one fixed polynomial bounds the
framed machine's clock for every source and every tape. -/
theorem frameClock_poly_input (t lambda : ℕ) (ht : 1 ≤ t) :
    ∃ C d : ℕ, ∀ (x : YaoSource t) (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda),
      frameClock lambda x ≤ C * ((encode x).length + bits.val.length + 1) ^ d := by
  obtain ⟨C, d, h⟩ := frameClock_poly t lambda ht
  refine ⟨C, d, fun x bits => (h x).trans ?_⟩
  gcongr
  omega

theorem yaoClock_poly_input (t lambda : ℕ) (ht : 1 ≤ t) :
    ∃ C d : ℕ, ∀ (x : YaoSource t) (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda),
      yaoClock lambda x ≤ C * ((encode x).length + bits.val.length + 1) ^ d := by
  obtain ⟨C, d, h⟩ := yaoClock_poly t lambda ht
  refine ⟨C, d, fun x bits => (h x).trans ?_⟩
  gcongr
  omega

theorem yaoT_poly_input (t lambda : ℕ) (ht : 1 ≤ t) :
    ∃ C d : ℕ, ∀ (x : YaoSource t) (bits : SerializedTape t (paddedEdgeBits x.2.1) lambda),
      Paper2.YaoEntryRuns.yaoT t lambda x.2.2 ≤ C * ((encode x).length + bits.val.length + 1) ^ d := by
  obtain ⟨C, d, h⟩ := yaoT_poly t lambda ht
  refine ⟨C, d, fun x bits => (h x).trans ?_⟩
  gcongr
  omega

end Paper2.YaoClockPoly

end

#print axioms Paper2.YaoClockPoly.poly_add
#print axioms Paper2.YaoClockPoly.poly_mul
#print axioms Paper2.YaoClockPoly.natField_length_le
#print axioms Paper2.YaoClockPoly.poly_H
#print axioms Paper2.YaoClockPoly.poly_tape
#print axioms Paper2.YaoClockPoly.poly_tokens
#print axioms Paper2.YaoClockPoly.yaoT_poly
#print axioms Paper2.YaoClockPoly.yaoClock_poly
#print axioms Paper2.YaoClockPoly.frameClock_poly
#print axioms Paper2.YaoClockPoly.frameClock_poly_input
#print axioms Paper2.YaoClockPoly.yaoClock_poly_input
#print axioms Paper2.YaoClockPoly.yaoT_poly_input
