import EthInapproximability.CurrentPaper.EncodedCommunication
import Mathlib.Data.Nat.Size

/-!
# Explicit loopless graph source language

Source: v8 `03-exact-hardness.tex`, the explicit graph reduction.
The vertex count is unary, so isolated vertices are charged in input length.
The edge count and endpoint labels use canonical self-delimiting binary fields.
This is polynomially comparable to the usual explicit graph representations;
no theorem about source hardness or machine runtime is assumed here.
-/

namespace EthInapproximability.CurrentPaper.EncodedGraph

open EncodedCommunication

structure Graph where
  vertices : ℕ
  edges : List (ℕ × ℕ)
  deriving DecidableEq

def Graph.Valid (g : Graph) : Prop :=
  ∀ p ∈ g.edges, p.1 < g.vertices ∧ p.2 < g.vertices ∧ p.1 ≠ p.2

instance (g : Graph) : Decidable g.Valid := inferInstanceAs
  (Decidable (∀ p ∈ g.edges, p.1 < g.vertices ∧ p.2 < g.vertices ∧ p.1 ≠ p.2))

def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: tail => some (0, tail)
  | true :: tail => do
      let (n, rest) ← readUnary tail
      pure (n + 1, rest)

theorem readUnary_append (n : ℕ) (rest : List Bool) :
    readUnary (unary n ++ rest) = some (n, rest) := by
  induction n with
  | zero => simp [unary, readUnary]
  | succ n ih =>
      rw [show unary (n + 1) = true :: unary n by simp [unary, List.replicate_succ]]
      simp only [List.cons_append, readUnary, ih]
      rfl

theorem readUnary_sound {input rest : List Bool} {n : ℕ}
    (h : readUnary input = some (n, rest)) : unary n ++ rest = input := by
  induction input generalizing n with
  | nil => simp [readUnary] at h
  | cons b tail ih =>
    cases b with
    | false =>
      simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [unary]
    | true =>
      cases hp : readUnary tail with
      | none => simp [readUnary, hp] at h
      | some p =>
        obtain ⟨k, suffix⟩ := p
        simp only [readUnary, hp, pure, Bind.bind, Option.bind, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simpa [unary, List.replicate_succ] using congrArg (List.cons true) (ih hp)

def edgeFields : List (ℕ × ℕ) → List Bool
  | [] => []
  | p :: ps => natField p.1 ++ natField p.2 ++ edgeFields ps

def readEdges : ℕ → List Bool → Option (List (ℕ × ℕ) × List Bool)
  | 0, input => some ([], input)
  | n + 1, input => do
      let (u, tail₁) ← readNat input
      let (v, tail₂) ← readNat tail₁
      let (ps, rest) ← readEdges n tail₂
      pure ((u, v) :: ps, rest)

theorem readEdges_append (ps : List (ℕ × ℕ)) (rest : List Bool) :
    readEdges ps.length (edgeFields ps ++ rest) = some (ps, rest) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp [edgeFields, readEdges, List.append_assoc, readNat_append, ih]

theorem readEdges_sound {k : ℕ} {input rest : List Bool} {ps : List (ℕ × ℕ)}
    (h : readEdges k input = some (ps, rest)) :
    ps.length = k ∧ edgeFields ps ++ rest = input := by
  induction k generalizing input ps with
  | zero =>
    simp only [readEdges, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [edgeFields]
  | succ k ih =>
    cases h₁ : readNat input with
    | none => simp [readEdges, h₁] at h
    | some p₁ =>
      obtain ⟨u, tail₁⟩ := p₁
      cases h₂ : readNat tail₁ with
      | none => simp [readEdges, h₁, h₂] at h
      | some p₂ =>
        obtain ⟨v, tail₂⟩ := p₂
        cases h₃ : readEdges k tail₂ with
        | none => simp [readEdges, h₁, h₂, h₃] at h
        | some p₃ =>
          obtain ⟨qs, suffix⟩ := p₃
          simp only [readEdges, h₁, h₂, h₃, pure, Bind.bind, Option.bind,
            Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hlength, hsound⟩ := ih h₃
          constructor
          · simpa using congrArg Nat.succ hlength
          · simp only [edgeFields, List.append_assoc, hsound, readNat_sound h₂,
              readNat_sound h₁]

def encode (g : Graph) : List Bool :=
  unary g.vertices ++ natField g.edges.length ++ edgeFields g.edges

def decode (input : List Bool) : Option Graph := do
  let (vertices, tail₁) ← readUnary input
  let (count, tail₂) ← readNat tail₁
  let (edges, rest) ← readEdges count tail₂
  let g : Graph := ⟨vertices, edges⟩
  if rest = [] ∧ g.Valid then some g else none

theorem decode_encode (g : Graph) (hg : g.Valid) : decode (encode g) = some g := by
  have he := readEdges_append g.edges []
  simp only [List.append_nil] at he
  simp [decode, encode, List.append_assoc, readUnary_append, readNat_append,
    he, hg]

theorem decode_spec {input : List Bool} {g : Graph} (h : decode input = some g) :
    g.Valid ∧ encode g = input := by
  unfold decode at h
  cases h₁ : readUnary input with
  | none => simp [h₁] at h
  | some p₁ =>
    obtain ⟨n, tail₁⟩ := p₁
    cases h₂ : readNat tail₁ with
    | none => simp [h₁, h₂] at h
    | some p₂ =>
      obtain ⟨k, tail₂⟩ := p₂
      cases h₃ : readEdges k tail₂ with
      | none => simp [h₁, h₂, h₃] at h
      | some p₃ =>
        obtain ⟨edges, rest⟩ := p₃
        simp only [h₁, h₂, h₃, Bind.bind, Option.bind] at h
        split at h
        · rename_i hv
          obtain ⟨rfl, hv⟩ := hv
          cases Option.some.inj h
          refine ⟨hv, ?_⟩
          obtain ⟨hl, hs⟩ := readEdges_sound h₃
          simp only [List.append_nil] at hs
          simp only [encode, hl, hs, List.append_assoc, readNat_sound h₂,
            readUnary_sound h₁]
        · contradiction

theorem decode_valid {input : List Bool} {g : Graph} (h : decode input = some g) :
    g.Valid := (decode_spec h).1

theorem decode_sound {input : List Bool} {g : Graph} (h : decode input = some g) :
    encode g = input := (decode_spec h).2

theorem edgeFields_length_lower (edges : List (ℕ × ℕ)) :
    2 * edges.length ≤ (edgeFields edges).length := by
  induction edges with
  | nil => simp [edgeFields]
  | cons p ps ih =>
      simp only [edgeFields, List.length_append, natField, field_length, List.length_cons]
      omega

theorem encode_length_lower (g : Graph) :
    g.vertices + 2 * g.edges.length + 2 ≤ (encode g).length := by
  have h := edgeFields_length_lower g.edges
  simp only [encode, unary, List.length_append, List.length_replicate,
    List.length_singleton, natField, field_length]
  omega

/-- Isolated vertices, as well as edge occurrences, count toward actual input length. -/
theorem decoded_size_bound {input : List Bool} {g : Graph}
    (h : decode input = some g) :
    g.vertices + 2 * g.edges.length + 2 ≤ input.length := by
  rw [← decode_sound h]
  exact encode_length_lower g

theorem decoded_vertices_bound {input : List Bool} {g : Graph}
    (h : decode input = some g) : g.vertices ≤ input.length := by
  have := decoded_size_bound h
  omega

theorem decoded_edges_bound {input : List Bool} {g : Graph}
    (h : decode input = some g) : g.edges.length ≤ input.length := by
  have := decoded_size_bound h
  omega

theorem natField_length_upper (n : ℕ) : (natField n).length ≤ 2 * n + 1 := by
  rw [natField, field_length, Nat.size_eq_bits_len]
  have h := Nat.size_le.mpr (Nat.lt_two_pow_self : n < 2 ^ n)
  omega

theorem edgeFields_length_upper (n : ℕ) (edges : List (ℕ × ℕ))
    (h : ∀ p ∈ edges, p.1 < n ∧ p.2 < n) :
    (edgeFields edges).length ≤ edges.length * (4 * n + 2) := by
  induction edges with
  | nil => simp [edgeFields]
  | cons p ps ih =>
      have hp := h p (by simp)
      have hi := ih (fun q hq => h q (by simp [hq]))
      have hu := natField_length_upper p.1
      have hv := natField_length_upper p.2
      simp only [edgeFields, List.length_append, List.length_cons]
      nlinarith

theorem encode_length_upper (g : Graph) (hg : g.Valid) :
    (encode g).length ≤ g.vertices + 2 + g.edges.length * (4 * g.vertices + 4) := by
  have h := edgeFields_length_upper g.vertices g.edges
    (fun p hp => ⟨(hg p hp).1, (hg p hp).2.1⟩)
  have he := natField_length_upper g.edges.length
  simp only [encode, unary, List.length_append, List.length_replicate,
    List.length_singleton]
  nlinarith

/-- The actual ordered edge-occurrence adapter used by the finite reduction. -/
def endpoints (g : Graph) (hg : g.Valid) (i : Fin g.edges.length) :
    Fin 2 → Fin g.vertices :=
  fun b => if b = 0 then ⟨(g.edges.get i).1, (hg _ (List.get_mem ..)).1⟩
    else ⟨(g.edges.get i).2, (hg _ (List.get_mem ..)).2.1⟩

@[simp] theorem endpoints_zero (g : Graph) (hg : g.Valid) (i : Fin g.edges.length) :
    (endpoints g hg i 0).val = (g.edges.get i).1 := by simp [endpoints]

@[simp] theorem endpoints_one (g : Graph) (hg : g.Valid) (i : Fin g.edges.length) :
    (endpoints g hg i 1).val = (g.edges.get i).2 := by simp [endpoints]

theorem endpoints_injective (g : Graph) (hg : g.Valid) (i : Fin g.edges.length) :
    Function.Injective (endpoints g hg i) := by
  intro b c he
  have hne := (hg _ (List.get_mem g.edges i)).2.2
  have hb : b = 0 ∨ b = 1 := by omega
  have hc : c = 0 ∨ c = 1 := by omega
  rcases hb with rfl | rfl <;> rcases hc with rfl | rfl
  · rfl
  · exact (hne (by simpa only [endpoints_zero, endpoints_one] using congrArg Fin.val he)).elim
  · exact (hne (by simpa only [endpoints_zero, endpoints_one] using congrArg Fin.val he.symm)).elim
  · rfl

def Colourable (g : Graph) (hg : g.Valid) : Prop :=
  ∃ colour : Fin g.vertices → Fin 4,
    ∀ i : Fin g.edges.length, colour (endpoints g hg i 0) ≠ colour (endpoints g hg i 1)

def Language : Set (List Bool) :=
  { input | ∃ g, ∃ hg : g.Valid, decode input = some g ∧ Colourable g hg }

theorem language_iff_decoded {input : List Bool} {g : Graph}
    (h : decode input = some g) : input ∈ Language ↔ Colourable g (decode_valid h) := by
  constructor
  · rintro ⟨g', hg', hd, hc⟩
    rw [h] at hd
    cases Option.some.inj hd
    exact hc
  · intro hc
    exact ⟨g, decode_valid h, h, hc⟩

theorem encode_mem_iff (g : Graph) (hg : g.Valid) :
    encode g ∈ Language ↔ Colourable g hg :=
  language_iff_decoded (decode_encode g hg)

theorem malformed_not_mem {input : List Bool} (h : decode input = none) :
    input ∉ Language := by
  rintro ⟨g, hg, hd, _⟩
  rw [h] at hd
  contradiction

end EthInapproximability.CurrentPaper.EncodedGraph
