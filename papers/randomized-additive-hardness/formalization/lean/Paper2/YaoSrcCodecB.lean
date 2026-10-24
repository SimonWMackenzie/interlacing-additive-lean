import Paper2.UnaryFieldListParser

/-! Unit 5 segment Y1 (lane a-yao-owner-1): the pure Yao source codec,
root decision R-Y1 Option B.

A Yao source is the consumer shape fixed by the banked materialization
theorems: `edges : Fin e → Fin (2^t*2^t) ↪ Fin v`.  The code is

  `unary v ++ unary e ++ (piCodec (finCodec v) (e*K)).encode (flatten edges)`

with `K = 2^t*2^t`, unary `n` = `true^n ++ [false]` (the admitted
`decodeUnary` numeral), and the body the admitted structural tuple codec,
edge-major and position-minor through `finProdFinEquiv`.  The body stream
is the one parsed on all inputs by the admitted
`UnaryFieldListParserScratch.observed_run_eq_piCodec`.  The decode is total:
it rejects truncation, out-of-range labels, and a repeated vertex in an
edge; `decodeAll` also rejects trailing bits.  `decode_eq_some_iff` is the
exact acceptance characterization (canonical codes only).

The lock prescribes no bit syntax; this is an implementation codec for the
already ordered typed hypergraph, not a changed constructor.  Row/column
indices and `SerializedTape` are untouched. -/

namespace Paper2.YaoSourceCodec

open Paper2.RecursiveLabelCodecScratch
open Paper2.UnaryFieldListParserScratch

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- The edge arity `K = s^2 = 2^t * 2^t` of the Yao source (Y:77-90). -/
abbrev arity (t : ℕ) : ℕ := 2 ^ t * 2 ^ t

/-- Vertex count, edge count, and ordered edges with distinct vertices. -/
abbrev YaoSource (t : ℕ) := Σ v : ℕ, Σ e : ℕ, Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v

/-- The unary numeral read by the admitted `decodeUnary`. -/
def unaryNat (n : ℕ) : List Bool := List.replicate n true ++ [false]

theorem decodeUnary_unaryNat (n : ℕ) (rest : List Bool) :
    decodeUnary (unaryNat n ++ rest) = some (n, rest) := by
  unfold unaryNat
  induction n with
  | zero => rfl
  | succ n ih =>
      have hc : List.replicate (n + 1) true ++ [false] ++ rest =
          true :: (List.replicate n true ++ [false] ++ rest) := by
        simp [List.replicate_succ]
      rw [hc, decodeUnary, ih]
      rfl

theorem decodeUnary_sound : (bits : List Bool) → (n : ℕ) → (rest : List Bool) →
    decodeUnary bits = some (n, rest) → bits = unaryNat n ++ rest
  | [], n, rest, h => by simp [decodeUnary] at h
  | false :: tail, n, rest, h => by
      simp only [decodeUnary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
  | true :: tail, n, rest, h => by
      simp only [decodeUnary] at h
      cases hd : decodeUnary tail with
      | none => simp [hd] at h
      | some p =>
          obtain ⟨m, r⟩ := p
          simp only [hd, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have ih := decodeUnary_sound tail m r hd
          simp [ih, unaryNat, List.replicate_succ]

theorem finCodec_decode_sound (a : ℕ) (bits rest : List Bool) (x : Fin a)
    (h : (finCodec a).decode bits = some (x, rest)) :
    bits = (finCodec a).encode x ++ rest := by
  simp only [finCodec] at h ⊢
  cases hd : decodeUnary bits with
  | none => simp [hd] at h
  | some p =>
      obtain ⟨m, r⟩ := p
      simp only [hd, Option.bind_eq_bind, Option.bind_some] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := decodeUnary_sound bits m r hd
        simpa [unaryNat, List.append_assoc] using this
      · simp at h

theorem decodeFields_sound (a : ℕ) : (N : ℕ) → (bits : List Bool) →
    (xs : List (Fin a)) → (rest : List Bool) →
    decodeFields a N bits = some (xs, rest) → bits = tokens xs ++ rest
  | 0, bits, xs, rest, h => by
      simp only [decodeFields, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [tokens]
  | N + 1, bits, xs, rest, h => by
      simp only [decodeFields] at h
      cases h1 : (finCodec a).decode bits with
      | none => simp [h1] at h
      | some p =>
          obtain ⟨x, r⟩ := p
          cases h2 : decodeFields a N r with
          | none => simp [h1, h2] at h
          | some q =>
              obtain ⟨ys, r'⟩ := q
              simp only [h1, h2, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [finCodec_decode_sound a bits r x h1,
                decodeFields_sound a N r ys r' h2]
              simp [tokens, List.append_assoc]

/-- Soundness of the admitted structural tuple decoder: an accepted prefix is
exactly the encoding of the decoded tuple. -/
theorem piCodec_decode_sound (a N : ℕ) (bits rest : List Bool) (f : Fin N → Fin a)
    (h : (piCodec (finCodec a) N).decode bits = some (f, rest)) :
    bits = (piCodec (finCodec a) N).encode f ++ rest := by
  have hf := decodeFields_eq_piCodec a N bits
  rw [h] at hf
  rw [piCodec_encode_eq_tokens]
  exact decodeFields_sound a N bits (List.ofFn f) rest (by simpa using hf)

/-- Edge-major, position-minor flattening of the ordered edge list. -/
def flatten {t v e : ℕ} (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v) :
    Fin (e * arity t) → Fin v :=
  fun k => edges (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

def unflatten {t v e : ℕ} (f : Fin (e * arity t) → Fin v) :
    Fin e → Fin (2 ^ t * 2 ^ t) → Fin v :=
  fun i j => f (finProdFinEquiv (i, j))

theorem flatten_val {t v e : ℕ} (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin e) (j : Fin (2 ^ t * 2 ^ t)) :
    flatten edges (finProdFinEquiv (i, j)) = edges i j := by
  simp [flatten]

theorem unflatten_flatten {t v e : ℕ} (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin e) : unflatten (flatten edges) i = edges i := by
  funext j
  simp [unflatten, flatten]

/-- The body codec: `e*K` bounded-unary vertex labels below `v`. -/
def bodyCodec (t v e : ℕ) : PrefixCodec (Fin (e * arity t) → Fin v) :=
  piCodec (finCodec v) (e * arity t)

def encode {t : ℕ} (x : YaoSource t) : List Bool :=
  unaryNat x.1 ++ unaryNat x.2.1 ++ (bodyCodec t x.1 x.2.1).encode (flatten x.2.2)

/-- Total prefix decoder; the injectivity filter rejects a repeated vertex
inside an edge. -/
def decode (t : ℕ) (bits : List Bool) : Option (YaoSource t × List Bool) := do
  let (v, r₁) ← decodeUnary bits
  let (e, r₂) ← decodeUnary r₁
  let (f, r₃) ← (bodyCodec t v e).decode r₂
  if h : ∀ i : Fin e, Function.Injective (unflatten f i) then
    some (⟨v, e, fun i => ⟨unflatten f i, h i⟩⟩, r₃)
  else none

/-- Whole-string decoder: trailing bits are rejected. -/
def decodeAll (t : ℕ) (bits : List Bool) : Option (YaoSource t) :=
  match decode t bits with
  | some (x, []) => some x
  | _ => none

theorem decode_encode {t : ℕ} (x : YaoSource t) (rest : List Bool) :
    decode t (encode x ++ rest) = some (x, rest) := by
  obtain ⟨v, e, edges⟩ := x
  have hinj : ∀ i : Fin e, Function.Injective (unflatten (flatten edges) i) := by
    intro i
    rw [unflatten_flatten]
    exact (edges i).injective
  simp only [decode, encode, List.append_assoc, decodeUnary_unaryNat,
    (bodyCodec t v e).roundtrip, Option.bind_eq_bind, Option.bind_some]
  rw [dif_pos hinj]
  congr
  funext i
  ext j
  simp [unflatten_flatten]

theorem decodeAll_encode {t : ℕ} (x : YaoSource t) :
    decodeAll t (encode x) = some x := by
  have h := decode_encode x []
  rw [List.append_nil] at h
  simp [decodeAll, h]

/-- Canonicality: every accepted prefix is literally the encoding of the
decoded source.  Hence noncanonical fields, truncation and out-of-range
labels are rejected. -/
theorem decode_sound {t : ℕ} (bits rest : List Bool) (x : YaoSource t)
    (h : decode t bits = some (x, rest)) : bits = encode x ++ rest := by
  simp only [decode] at h
  cases h1 : decodeUnary bits with
  | none => simp [h1] at h
  | some p₁ =>
    obtain ⟨v, r₁⟩ := p₁
    cases h2 : decodeUnary r₁ with
    | none => simp [h1, h2] at h
    | some p₂ =>
      obtain ⟨e, r₂⟩ := p₂
      cases h3 : (bodyCodec t v e).decode r₂ with
      | none => simp [h1, h2, h3] at h
      | some p₃ =>
        obtain ⟨f, r₃⟩ := p₃
        simp only [h1, h2, h3, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · rename_i hinj
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [decodeUnary_sound bits v r₁ h1, decodeUnary_sound r₁ e r₂ h2,
            piCodec_decode_sound v (e * arity t) r₂ r₃ f h3]
          have hf : flatten (fun i => (⟨unflatten f i, hinj i⟩ :
              Fin (2 ^ t * 2 ^ t) ↪ Fin v)) = f := by
            funext k
            show f (finProdFinEquiv ((finProdFinEquiv.symm k).1,
              (finProdFinEquiv.symm k).2)) = f k
            rw [Prod.mk.eta, Equiv.apply_symm_apply]
          simp only [encode, List.append_assoc, bodyCodec]
          rw [hf]
        · simp at h

/-- Exact acceptance characterization of the prefix decoder. -/
theorem decode_eq_some_iff {t : ℕ} (bits rest : List Bool) (x : YaoSource t) :
    decode t bits = some (x, rest) ↔ bits = encode x ++ rest := by
  constructor
  · exact decode_sound bits rest x
  · rintro rfl
    exact decode_encode x rest

/-- Exact acceptance characterization of the whole-string decoder. -/
theorem decodeAll_eq_some_iff {t : ℕ} (bits : List Bool) (x : YaoSource t) :
    decodeAll t bits = some x ↔ bits = encode x := by
  constructor
  · intro h
    unfold decodeAll at h
    split at h
    · rename_i y hy
      simp only [Option.some.injEq] at h
      subst h
      simpa using decode_sound bits [] y hy
    · simp at h
  · rintro rfl
    exact decodeAll_encode x

/-- Explicit rejection of a repeated vertex inside an edge. -/
theorem decode_rejects_repeat (t v e : ℕ) (f : Fin (e * arity t) → Fin v)
    (rest : List Bool) (i : Fin e) (j₁ j₂ : Fin (2 ^ t * 2 ^ t)) (hne : j₁ ≠ j₂)
    (hrep : unflatten f i j₁ = unflatten f i j₂) :
    decode t (unaryNat v ++ unaryNat e ++ (bodyCodec t v e).encode f ++ rest) = none := by
  have hni : ¬ ∀ i : Fin e, Function.Injective (unflatten f i) :=
    fun h => hne (h i hrep)
  simp only [decode, List.append_assoc, decodeUnary_unaryNat,
    (bodyCodec t v e).roundtrip, Option.bind_eq_bind, Option.bind_some]
  rw [dif_neg hni]

/-- Explicit rejection of a truncated or empty string: the empty string. -/
theorem decode_nil (t : ℕ) : decode t [] = none := by
  simp [decode, decodeUnary]

/-- Exact bit length of the code: two unary headers plus one bounded-unary
field of length `label+1` per incidence. -/
theorem encode_length {t : ℕ} (x : YaoSource t) :
    (encode x).length =
      (x.1 + 1) + (x.2.1 + 1) +
        ((List.ofFn (flatten x.2.2)).map (fun y => y.val + 1)).sum := by
  simp only [encode, bodyCodec, List.length_append, unaryNat, List.length_replicate,
    List.length_singleton, piCodec_encode_eq_tokens, tokens]
  congr 1
  rw [List.length_flatMap]
  congr 1
  simp only [finCodec, List.length_append, List.length_replicate, List.length_singleton]

/-- Polynomial size bound: `|code| ≤ v + e + 2 + e*K*v`. -/
theorem encode_length_le {t : ℕ} (x : YaoSource t) :
    (encode x).length ≤ x.1 + x.2.1 + 2 + x.2.1 * arity t * x.1 := by
  have hb := (bodyCodec t x.1 x.2.1).length_le (flatten x.2.2)
  have hm : (bodyCodec t x.1 x.2.1).maxLen = x.2.1 * arity t * x.1 := by
    simp [bodyCodec, piCodec_maxLen, finCodec]
  rw [hm] at hb
  simp only [encode, List.length_append, unaryNat, List.length_replicate,
    List.length_singleton]
  omega

#print axioms decode_encode
#print axioms decodeAll_encode
#print axioms decode_sound
#print axioms decode_eq_some_iff
#print axioms decodeAll_eq_some_iff
#print axioms decode_rejects_repeat
#print axioms encode_length
#print axioms encode_length_le

end Paper2.YaoSourceCodec
