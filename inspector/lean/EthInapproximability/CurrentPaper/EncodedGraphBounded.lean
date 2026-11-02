import EthInapproximability.CurrentPaper.EncodedGraph

/-!
# Early-rejecting bounded graph parser specification

Source: frozen v8 fixed bit-machine graph encoding convention. This is an
executable parser specification with a literal input-length edge-count cap
and immediate endpoint checks. Its equality to the original all-input
graph parser is proved; no finite-machine runtime is asserted here.
-/

namespace EthInapproximability.CurrentPaper.EncodedGraphBounded

open EncodedCommunication EncodedGraph

def ValidEdges (n : ℕ) (edges : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ edges, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2

instance (n : ℕ) (edges : List (ℕ × ℕ)) : Decidable (ValidEdges n edges) := inferInstanceAs
  (Decidable (∀ p ∈ edges, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2))

theorem validEdges_cons (n u v : ℕ) (edges : List (ℕ × ℕ)) :
    ValidEdges n ((u, v) :: edges) ↔
      (u < n ∧ v < n ∧ u ≠ v) ∧ ValidEdges n edges := by
  simp [ValidEdges]

def readCheckedEdges (n : ℕ) : ℕ → List Bool → Option (List (ℕ × ℕ) × List Bool)
  | 0, bits => some ([], bits)
  | count + 1, bits => do
      let (u, tail₁) ← readNat bits
      if u < n then do
        let (v, tail₂) ← readNat tail₁
        if v < n ∧ u ≠ v then do
          let (edges, rest) ← readCheckedEdges n count tail₂
          pure ((u, v) :: edges, rest)
        else none
      else none

theorem readCheckedEdges_eq (n count : ℕ) (bits : List Bool) :
    readCheckedEdges n count bits =
      (readEdges count bits).bind (fun p => if ValidEdges n p.1 then some p else none) := by
  induction count generalizing bits with
  | zero => simp [readCheckedEdges, readEdges, ValidEdges]
  | succ count ih =>
      cases h₁ : readNat bits with
      | none => simp [readCheckedEdges, readEdges, h₁]
      | some p₁ =>
        obtain ⟨u, tail₁⟩ := p₁
        cases h₂ : readNat tail₁ with
        | none => simp [readCheckedEdges, readEdges, h₁, h₂]
        | some p₂ =>
          obtain ⟨v, tail₂⟩ := p₂
          cases h₃ : readEdges count tail₂ with
          | none => simp [readCheckedEdges, readEdges, h₁, h₂, ih, h₃]
          | some p₃ =>
            obtain ⟨edges, rest⟩ := p₃
            by_cases hu : u < n <;> by_cases hv : v < n ∧ u ≠ v <;>
              by_cases he : ValidEdges n edges <;>
              simp [readCheckedEdges, readEdges, h₁, h₂, ih, h₃,
                validEdges_cons, hu, hv, he]

theorem readCheckedEdges_sound {n count : ℕ} {bits rest : List Bool}
    {edges : List (ℕ × ℕ)} (h : readCheckedEdges n count bits = some (edges, rest)) :
    readEdges count bits = some (edges, rest) ∧ ValidEdges n edges := by
  rw [readCheckedEdges_eq] at h
  cases hp : readEdges count bits with
  | none => simp [hp] at h
  | some p =>
      simp only [hp, Option.bind_some] at h
      split at h
      · rename_i hv
        cases Option.some.inj h
        exact ⟨rfl, hv⟩
      · contradiction

theorem readCheckedEdges_append (n : ℕ) (edges : List (ℕ × ℕ))
    (h : ValidEdges n edges) (rest : List Bool) :
    readCheckedEdges n edges.length (edgeFields edges ++ rest) = some (edges, rest) := by
  simp [readCheckedEdges_eq, readEdges_append, h]

def decode (input : List Bool) : Option Graph := do
  let (n, tail₁) ← readUnary input
  let (count, tail₂) ← readNat tail₁
  if count ≤ input.length then do
    let (edges, rest) ← readCheckedEdges n count tail₂
    if rest = [] then some ⟨n, edges⟩ else none
  else none

theorem decode_encode (g : Graph) (hg : g.Valid) : decode (encode g) = some g := by
  have he := readCheckedEdges_append g.vertices g.edges hg []
  simp only [List.append_nil] at he
  have hcount : g.edges.length ≤ (encode g).length := by
    have := encode_length_lower g
    omega
  simp only [encode, List.append_assoc] at hcount
  unfold decode
  simp only [encode, List.append_assoc, readUnary_append, readNat_append,
    Bind.bind, Option.bind]
  simp only [hcount, ↓reduceIte, he]

theorem decode_sound {input : List Bool} {g : Graph} (h : decode input = some g) :
    EncodedGraph.decode input = some g := by
  unfold decode at h
  cases h₁ : readUnary input with
  | none => simp [h₁] at h
  | some p₁ =>
    obtain ⟨n, tail₁⟩ := p₁
    cases h₂ : readNat tail₁ with
    | none => simp [h₁, h₂] at h
    | some p₂ =>
      obtain ⟨count, tail₂⟩ := p₂
      simp only [h₁, h₂, Bind.bind, Option.bind] at h
      split at h
      · cases h₃ : readCheckedEdges n count tail₂ with
        | none => simp [h₃] at h
        | some p₃ =>
          obtain ⟨edges, rest⟩ := p₃
          simp only [h₃] at h
          split at h
          · rename_i hrest
            subst rest
            cases Option.some.inj h
            obtain ⟨hr, hv⟩ := readCheckedEdges_sound h₃
            have hv' : (EncodedGraph.Graph.mk n edges).Valid := hv
            simp [EncodedGraph.decode, h₁, h₂, hr, hv']
          · contradiction
      · contradiction

theorem decode_eq (input : List Bool) : decode input = EncodedGraph.decode input := by
  cases hd : decode input with
  | some g => exact (decode_sound hd).symm
  | none =>
      cases hg : EncodedGraph.decode input with
      | none => rfl
      | some g =>
          have hs := EncodedGraph.decode_sound hg
          have hv := EncodedGraph.decode_valid hg
          have hc := decode_encode g hv
          rw [hs, hd] at hc
          contradiction

theorem readCheckedEdges_suffix_length {n count : ℕ} {bits rest : List Bool}
    {edges : List (ℕ × ℕ)} (h : readCheckedEdges n count bits = some (edges, rest)) :
    rest.length ≤ bits.length := by
  have hs := (readEdges_sound (readCheckedEdges_sound h).1).2
  have hl := congrArg List.length hs
  simp only [List.length_append] at hl
  omega

theorem readCheckedEdges_count_bound {n count : ℕ} {bits rest : List Bool}
    {edges : List (ℕ × ℕ)} (h : readCheckedEdges n count bits = some (edges, rest)) :
    2 * count + rest.length ≤ bits.length := by
  obtain ⟨hc, hs⟩ := readEdges_sound (readCheckedEdges_sound h).1
  have hl := congrArg List.length hs
  have he := edgeFields_length_lower edges
  simp only [List.length_append] at hl
  omega

end EthInapproximability.CurrentPaper.EncodedGraphBounded
