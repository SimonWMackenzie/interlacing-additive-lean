import CurrentAdditive.PreservingV2Run
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

set_option maxHeartbeats 1000000

namespace CurrentAdditive.GaussListContext.IndexedV2Clock

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussListContext

theorem bits_length_le (n : Nat) : n.bits.length ≤ n := by
  exact UnaryBinaryEncoding.bits_length_le n

theorem fieldCost_le (xs : List (List Bool)) (L : Nat)
    (h : ∀ x ∈ xs, x.length ≤ L) :
    IndexedFieldProgram.fieldCost xs ≤ 25 * xs.length * (L + 1)^2 := by
  induction xs with
  | nil => simp [IndexedFieldProgram.fieldCost]
  | cons x tail ih =>
      have hx : x.length ≤ L := h x (by simp)
      have ht : ∀ y ∈ tail, y.length ≤ L :=
        fun y hy => h y (by simp [hy])
      have htail := ih ht
      have hbits := bits_length_le x.length
      have hterm : 20 * (x.length + 1) *
          (x.length.bits.length + 1) + 2 * x.length + 5 ≤
          25 * (L + 1)^2 := by
        nlinarith [sq_nonneg ((L : ℤ) - x.length)]
      change
        (20 * (x.length + 1) * (x.length.bits.length + 1) +
          2 * x.length + 5) + IndexedFieldProgram.fieldCost tail ≤
          25 * (tail.length + 1) * (L + 1)^2
      calc
        _ ≤ 25 * (L + 1)^2 +
            25 * tail.length * (L + 1)^2 :=
              Nat.add_le_add hterm htail
        _ = _ := by ring

theorem fields_length_ge_count (xs : List (List Bool)) :
    xs.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x tail ih =>
      have hhead : 1 ≤ (EncodedCommunication.natField x.length).length := by
        simp [EncodedCommunication.natField,
          EncodedCommunication.field_length]
      simp only [SourceListEncoding.fields, List.length_cons,
        List.length_append]
      omega

theorem fields_item_length_le (xs : List (List Bool))
    (x : List Bool) (hx : x ∈ xs) :
    x.length ≤ (SourceListEncoding.fields xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y tail ih =>
      rcases List.mem_cons.mp hx with rfl | htail
      · simp only [SourceListEncoding.fields, List.length_append]
        omega
      · have h := ih htail
        simp only [SourceListEncoding.fields, List.length_append]
        omega

theorem fieldCost_encoded_le (xs : List (List Bool)) :
    IndexedFieldProgram.fieldCost xs ≤
      25 * ((SourceListEncoding.encode xs).length + 1)^3 := by
  let L := (SourceListEncoding.fields xs).length
  have hcost := fieldCost_le xs L
    (fun x hx => fields_item_length_le xs x hx)
  have hcount := fields_length_ge_count xs
  have henc : L ≤ (SourceListEncoding.encode xs).length := by
    simp [L, SourceListEncoding.encode]
  have hn : xs.length ≤ (SourceListEncoding.encode xs).length + 1 := by
    omega
  have hL : L + 1 ≤ (SourceListEncoding.encode xs).length + 1 := by omega
  have hmul := Nat.mul_le_mul hn (Nat.pow_le_pow_left hL 2)
  nlinarith [hmul]

theorem fields_append (xs ys : List (List Bool)) :
    SourceListEncoding.fields (xs ++ ys) =
      SourceListEncoding.fields xs ++ SourceListEncoding.fields ys := by
  induction xs with
  | nil => simp [SourceListEncoding.fields]
  | cons x tail ih =>
      simp only [List.cons_append, SourceListEncoding.fields, ih]
      simp only [List.append_assoc]

theorem fieldCost_prefix_le (xs ys : List (List Bool)) :
    IndexedFieldProgram.fieldCost xs ≤
      25 * ((SourceListEncoding.encode (xs ++ ys)).length + 1)^3 := by
  let L := (SourceListEncoding.encode (xs ++ ys)).length
  have hfield : (SourceListEncoding.fields xs).length ≤ L := by
    dsimp [L, SourceListEncoding.encode]
    rw [fields_append]
    simp only [List.length_append]
    omega
  have hitems : ∀ x ∈ xs, x.length ≤ L := by
    intro x hx
    exact (fields_item_length_le xs x hx).trans hfield
  have hcost := fieldCost_le xs L hitems
  have hcount : xs.length ≤ L + 1 := by
    have h := fields_length_ge_count xs
    omega
  have hmul := Nat.mul_le_mul hcount (Nat.le_refl ((L + 1)^2))
  nlinarith [hmul]

theorem preserving_lookup_cubic (pre : List (List Bool))
    (word : List Bool) (suffix : List (List Bool)) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    ∃ t ≤ 50 * (source.length + 1)^3,
      PreservingV2Program.run t
        (PreservingV2Program.initial source pre.length) =
      ⟨none,
       PreservingV2Program.v2Control (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true, false), none)),
       ![SourceListEncoding.fields suffix, [], [], [], [],
         List.replicate word.length true, word, [], source, []]⟩ := by
  dsimp only
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  obtain ⟨t, ht, hr⟩ := PreservingV2Program.select_preserving pre word suffix
  have hcost := fieldCost_prefix_le (pre ++ [word]) suffix
  have hshape : (pre ++ [word]) ++ suffix = pre ++ word :: suffix := by
    simp [List.append_assoc]
  rw [hshape] at hcost
  have hbits : (pre ++ word :: suffix).length.bits.length ≤ source.length := by
    have h1 := bits_length_le (pre ++ word :: suffix).length
    have h2 := fields_length_ge_count (pre ++ word :: suffix)
    have h3 : (SourceListEncoding.fields (pre ++ word :: suffix)).length ≤
        source.length := by simp [source, SourceListEncoding.encode]
    omega
  refine ⟨t, ?_, hr⟩
  dsimp [source] at *
  nlinarith [sq_nonneg ((SourceListEncoding.encode
    (pre ++ word :: suffix)).length : ℤ)]

#print axioms fieldCost_le
#print axioms fieldCost_encoded_le
#print axioms preserving_lookup_cubic

end CurrentAdditive.GaussListContext.IndexedV2Clock
