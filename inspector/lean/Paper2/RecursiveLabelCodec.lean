import Paper2.RecursiveEntries
import Paper2.SourceConstruction
import Paper2.ParameterizedCanonicalSource
import Paper2.PublicScheduleChecks

/-! Prefix-free, finite, computable encodings of actual recursive source
labels. No enumeration of an entire carrier is used. -/

namespace Paper2.RecursiveLabelCodecScratch

open SourceMatrix RecursiveEntries

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- A concrete prefix parser with a charged maximum encoded length. -/
structure PrefixCodec (α : Type) where
  encode : α → List Bool
  decode : List Bool → Option (α × List Bool)
  roundtrip : ∀ x rest, decode (encode x ++ rest) = some (x, rest)
  maxLen : ℕ
  length_le : ∀ x, (encode x).length ≤ maxLen

def boolCodec : PrefixCodec Bool where
  encode b := [b]
  decode
    | [] => none
    | b :: rest => some (b, rest)
  roundtrip := by intro b rest; rfl
  maxLen := 1
  length_le := by intro b; simp

/-- Unary numerals avoid any noncomputable finite-carrier indexing. -/
def decodeUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest => do
      let (v, tail) ← decodeUnary rest
      pure (v + 1, tail)

private theorem decodeUnary_replicate (v : ℕ) (rest : List Bool) :
    decodeUnary (List.replicate v true ++ false :: rest) = some (v, rest) := by
  induction v with
  | zero => rfl
  | succ v ih => simp [List.replicate, decodeUnary, ih]

def finCodec (a : ℕ) : PrefixCodec (Fin a) where
  encode x := List.replicate x.val true ++ [false]
  decode bits := do
    let (v, rest) ← decodeUnary bits
    if h : v < a then some (⟨v, h⟩, rest) else none
  roundtrip := by
    intro x rest
    simp [decodeUnary_replicate, List.append_assoc, x.isLt]
  maxLen := a
  length_le := by
    intro x
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    omega

def prodCodec {α β : Type} (ca : PrefixCodec α) (cb : PrefixCodec β) :
    PrefixCodec (α × β) where
  encode x := ca.encode x.1 ++ cb.encode x.2
  decode bits := do
    let (a, rest) ← ca.decode bits
    let (b, tail) ← cb.decode rest
    pure ((a, b), tail)
  roundtrip := by
    intro x rest
    simp [List.append_assoc, ca.roundtrip, cb.roundtrip]
  maxLen := ca.maxLen + cb.maxLen
  length_le := by
    intro x
    simp only [List.length_append]
    exact Nat.add_le_add (ca.length_le x.1) (cb.length_le x.2)

def sumCodec {α β : Type} (ca : PrefixCodec α) (cb : PrefixCodec β) :
    PrefixCodec (α ⊕ β) where
  encode
    | .inl x => false :: ca.encode x
    | .inr y => true :: cb.encode y
  decode
    | [] => none
    | false :: rest => do
        let (a, tail) ← ca.decode rest
        pure (.inl a, tail)
    | true :: rest => do
        let (b, tail) ← cb.decode rest
        pure (.inr b, tail)
  roundtrip := by
    intro x rest
    cases x with
    | inl a => simp [ca.roundtrip]
    | inr b => simp [cb.roundtrip]
  maxLen := 1 + max ca.maxLen cb.maxLen
  length_le := by
    intro x
    cases x with
    | inl a =>
        simp only [List.length_cons]
        have h := (ca.length_le a).trans (le_max_left ca.maxLen cb.maxLen)
        omega
    | inr b =>
        simp only [List.length_cons]
        have h := (cb.length_le b).trans (le_max_right ca.maxLen cb.maxLen)
        omega

def transportCodec {α β : Type} (e : α ≃ β) (ca : PrefixCodec α) :
    PrefixCodec β where
  encode y := ca.encode (e.symm y)
  decode bits := (ca.decode bits).map (fun z => (e z.1, z.2))
  roundtrip := by
    intro y rest
    simp [ca.roundtrip]
  maxLen := ca.maxLen
  length_le := by
    intro y
    exact ca.length_le (e.symm y)

def emptyPiCodec {α : Type} : PrefixCodec (Fin 0 → α) where
  encode _ := []
  decode bits := some (Fin.elim0, bits)
  roundtrip := by
    intro x rest
    simp only [List.nil_append]
    have h : (Fin.elim0 : Fin 0 → α) = x := by
      funext i
      exact i.elim0
    simp [h]
  maxLen := 0
  length_le := by intro x; simp

/-- A fixed arity tuple is encoded coordinate by coordinate, without enumerating
the carrier of the coordinate type. -/
def piCodec {α : Type} (ca : PrefixCodec α) : (n : ℕ) → PrefixCodec (Fin n → α)
  | 0 => emptyPiCodec
  | n + 1 =>
      transportCodec
        { toFun := fun z => Fin.cons z.1 z.2
          invFun := fun f => (f 0, Fin.tail f)
          left_inv := by intro z; simp [Fin.tail_cons]
          right_inv := by intro f; exact Fin.cons_self_tail f }
        (prodCodec ca (piCodec ca n))

def outerColumnCodec {Y : Type} (q₁ q₂ s : ℕ) (cy : PrefixCodec Y) :
    PrefixCodec (OuterColumn q₁ q₂ s Y) :=
  prodCodec (finCodec q₂) (piCodec cy (q₁ + s + 1))

def rawColumnCodec {Y : Type} (q₁ q₂ s : ℕ) (cy : PrefixCodec Y) :
    PrefixCodec (RawColumn q₁ q₂ s Y) :=
  prodCodec (piCodec cy (s + 1))
    (piCodec (outerColumnCodec q₁ q₂ s cy) s)

def rawRowCodec {X I : Type} (q₁ q₂ s : ℕ)
    (cx : PrefixCodec X) (ci : PrefixCodec I) :
    PrefixCodec (RawRow q₁ q₂ s X I) :=
  sumCodec
    (prodCodec (finCodec s)
      (piCodec (prodCodec (finCodec q₁) cx) q₂))
    (prodCodec ci cx)

def taggedEquiv {Y : Type} (q₁ q₂ s : ℕ) :
    (RawColumn q₁ q₂ s Y ⊕
      ((Fin s → OuterColumn q₁ q₂ s Y) ⊕ OuterColumn q₁ q₂ s Y)) ≃
      TaggedColumn q₁ q₂ s Y where
  toFun
    | .inl z => .unrestricted z
    | .inr (.inl js) => .fixedTail js
    | .inr (.inr j) => .diagonal j
  invFun
    | .unrestricted z => .inl z
    | .fixedTail js => .inr (.inl js)
    | .diagonal j => .inr (.inr j)
  left_inv := by intro x; cases x with | inl z => rfl | inr x => cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

def taggedColumnCodec {Y : Type} (q₁ q₂ s : ℕ) (cy : PrefixCodec Y) :
    PrefixCodec (TaggedColumn q₁ q₂ s Y) :=
  transportCodec (taggedEquiv q₁ q₂ s)
    (sumCodec (rawColumnCodec q₁ q₂ s cy)
      (sumCodec (piCodec (outerColumnCodec q₁ q₂ s cy) s)
        (outerColumnCodec q₁ q₂ s cy)))

/-- Both actual recursive carriers, with a decoder and length bound obtained
uniformly from the three base label codecs. -/
def carrierCodecs {X₀ Y₀ I : Type} (s q₁ q₂ w Q : ℕ)
    (cx₀ : PrefixCodec X₀) (cy₀ : PrefixCodec Y₀) (ci : PrefixCodec I) :
    (k : ℕ) → PrefixCodec (Row X₀ Y₀ I s q₁ q₂ w Q k) ×
      PrefixCodec (Column X₀ Y₀ I s q₁ q₂ w Q k)
  | 0 => (cx₀, cy₀)
  | k + 1 =>
      let previous := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k
      (piCodec (prodCodec (finCodec w)
          (taggedColumnCodec q₁ q₂ s previous.2)) Q,
       prodCodec (finCodec Q)
          (piCodec (rawRowCodec q₁ q₂ s previous.1 ci) w))

theorem piCodec_maxLen {α : Type} (ca : PrefixCodec α) (n : ℕ) :
    (piCodec ca n).maxLen = n * ca.maxLen := by
  induction n with
  | zero => simp [piCodec, emptyPiCodec]
  | succ n ih =>
      simp [piCodec, transportCodec, prodCodec, ih, Nat.succ_mul, Nat.add_comm]

/-- The seed row is a Boolean lookup table, the seed column an address,
and the source item retains its group and vertex/auxiliary tag. -/
def defaultItemCodec (n s : ℕ) :
    PrefixCodec (SourceConstruction.Items s (Fin n)) :=
  prodCodec (finCodec (4 * s))
    (sumCodec (finCodec n) (finCodec (s - 3)))

def defaultCarrierCodecs (n p s q₁ q₂ w Q : ℕ) (k : ℕ) :
    PrefixCodec
      (Row (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k) ×
    PrefixCodec
      (Column (Fin p → Bool) (Fin p) (SourceConstruction.Items s (Fin n))
        s q₁ q₂ w Q k) :=
  carrierCodecs s q₁ q₂ w Q (piCodec boolCodec p)
    (finCodec p) (defaultItemCodec n s) k

/-- The codec instantiated at the literal public source schedule. This is a
definition of algorithms, not a choice of an enumeration of either carrier. -/
def scheduledCarrierCodecs (n m L Δ : ℕ) (γ : ℚ) (k : ℕ) :=
  defaultCarrierCodecs n (LookupSeed.width L)
    (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k

theorem scheduled_row_roundtrip (n m L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k)
    (rest : List Bool) :
    (scheduledCarrierCodecs n m L Δ γ k).1.decode
      ((scheduledCarrierCodecs n m L Δ γ k).1.encode x ++ rest) =
        some (x, rest) :=
  (scheduledCarrierCodecs n m L Δ γ k).1.roundtrip x rest

theorem scheduled_column_roundtrip (n m L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k)
    (rest : List Bool) :
    (scheduledCarrierCodecs n m L Δ γ k).2.decode
      ((scheduledCarrierCodecs n m L Δ γ k).2.encode y ++ rest) =
        some (y, rest) :=
  (scheduledCarrierCodecs n m L Δ γ k).2.roundtrip y rest

theorem default_seed_row_maxLen (n p s q₁ q₂ w Q : ℕ) :
    (defaultCarrierCodecs n p s q₁ q₂ w Q 0).1.maxLen = p := by
  simp [defaultCarrierCodecs, carrierCodecs, piCodec_maxLen, boolCodec]

theorem default_seed_column_maxLen (n p s q₁ q₂ w Q : ℕ) :
    (defaultCarrierCodecs n p s q₁ q₂ w Q 0).2.maxLen = p := by
  rfl

theorem default_item_maxLen (n s : ℕ) :
    (defaultItemCodec n s).maxLen =
      4 * s + (1 + max n (s - 3)) := by
  rfl

theorem encoded_length_le_maxLen {α : Type} (ca : PrefixCodec α)
    (x : α) : (ca.encode x).length ≤ ca.maxLen := ca.length_le x

private theorem tagged_maxLen_le {Y : Type} (q₁ q₂ s : ℕ)
    (cy : PrefixCodec Y) (H : ℕ) (hcy : cy.maxLen ≤ H) (hH : 1 ≤ H) :
    (taggedColumnCodec q₁ q₂ s cy).maxLen ≤
      (2 + (s + 1) + (2 * s + 1) * (q₂ + q₁ + s + 1)) * H := by
  let D := q₂ + q₁ + s + 1
  let O := q₂ + (q₁ + s + 1) * cy.maxLen
  have hO : O ≤ D * H := by
    have h₁ := Nat.mul_le_mul_left (q₁ + s + 1) hcy
    have h₂ := Nat.mul_le_mul_left q₂ hH
    dsimp [O, D]
    nlinarith
  have hR : (s + 1) * cy.maxLen + s * O ≤
      ((s + 1) + s * D) * H := by
    have h₁ := Nat.mul_le_mul_left (s + 1) hcy
    have h₂ := Nat.mul_le_mul_left s hO
    nlinarith
  have hF : s * O ≤ s * D * H := by
    have := Nat.mul_le_mul_left s hO
    nlinarith
  simp only [taggedColumnCodec, transportCodec, sumCodec, rawColumnCodec,
    outerColumnCodec, prodCodec, finCodec, piCodec_maxLen]
  change 1 + max ((s + 1) * cy.maxLen + s * O)
    (1 + max (s * O) O) ≤ _
  have hmax : max ((s + 1) * cy.maxLen + s * O)
      (1 + max (s * O) O) ≤
      ((s + 1) * cy.maxLen + s * O) + 1 + s * O + O := by
    omega
  calc
    1 + max ((s + 1) * cy.maxLen + s * O) (1 + max (s * O) O) ≤
        2 + ((s + 1) * cy.maxLen + s * O) + s * O + O := by omega
    _ ≤ 2 + (((s + 1) + s * D) * H) + (s * D * H) + D * H := by omega
    _ ≤ (2 + (s + 1) + (2 * s + 1) * D) * H := by
      nlinarith

private theorem rawRow_maxLen_le {X I : Type} (q₁ q₂ s : ℕ)
    (cx : PrefixCodec X) (ci : PrefixCodec I) (H : ℕ)
    (hx : cx.maxLen ≤ H) (hi : ci.maxLen ≤ H) (hH : 1 ≤ H) :
    (rawRowCodec q₁ q₂ s cx ci).maxLen ≤
      (3 + s + q₂ * q₁ + q₂) * H := by
  have h₁ := Nat.mul_le_mul_left q₂ hx
  simp only [rawRowCodec, sumCodec, prodCodec, finCodec, piCodec_maxLen]
  have hleft : s + q₂ * (q₁ + cx.maxLen) ≤
      (s + q₂ * q₁ + q₂) * H := by
    have hq₁ := Nat.mul_le_mul_left (q₂ * q₁) hH
    have hs := Nat.mul_le_mul_left s hH
    nlinarith
  have hright : ci.maxLen + cx.maxLen ≤ 2 * H := by omega
  have hm : max (s + q₂ * (q₁ + cx.maxLen))
      (ci.maxLen + cx.maxLen) ≤
      (s + q₂ * q₁ + q₂) * H + 2 * H := by omega
  nlinarith

/-- A deliberately coarse arithmetic multiplier for one actual full-product
successor; it charges every tuple coordinate and every constructor tag. -/
def labelStepCap (s q₁ q₂ w Q : ℕ) : ℕ :=
  max (Q * (w + 2 + (s + 1) +
      (2 * s + 1) * (q₂ + q₁ + s + 1)))
    (Q + w * (3 + s + q₂ * q₁ + q₂)) + 1

theorem carrierCodecs_maxLen_le {X₀ Y₀ I : Type}
    (s q₁ q₂ w Q : ℕ) (cx₀ : PrefixCodec X₀)
    (cy₀ : PrefixCodec Y₀) (ci : PrefixCodec I) (k : ℕ) :
    let M := max 1 (max cx₀.maxLen (max cy₀.maxLen ci.maxLen))
    let T := labelStepCap s q₁ q₂ w Q
    (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).1.maxLen ≤ M * T ^ k ∧
    (carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k).2.maxLen ≤ M * T ^ k := by
  let M := max 1 (max cx₀.maxLen (max cy₀.maxLen ci.maxLen))
  let T := labelStepCap s q₁ q₂ w Q
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hci : ci.maxLen ≤ M := by dsimp [M]; omega
  have hT : 1 ≤ T := by dsimp [T, labelStepCap]; omega
  induction k with
  | zero =>
      dsimp [carrierCodecs]
      constructor <;> dsimp [M] <;> omega
  | succ k ih =>
      let C := carrierCodecs s q₁ q₂ w Q cx₀ cy₀ ci k
      let H := M * T ^ k
      have hH : 1 ≤ H := by
        have hp : 1 ≤ T ^ k := one_le_pow₀ hT
        dsimp [H]
        nlinarith
      have hcx : C.1.maxLen ≤ H := ih.1
      have hcy : C.2.maxLen ≤ H := ih.2
      have hciH : ci.maxLen ≤ H := by
        have hp : 1 ≤ T ^ k := one_le_pow₀ hT
        have hMH : M ≤ H := by
          dsimp [H]
          nlinarith
        omega
      have htag := tagged_maxLen_le q₁ q₂ s C.2 H hcy hH
      have hraw := rawRow_maxLen_le q₁ q₂ s C.1 ci H hcx hciH hH
      have hrow :
          (piCodec (prodCodec (finCodec w)
            (taggedColumnCodec q₁ q₂ s C.2)) Q).maxLen ≤
            (Q * (w + 2 + (s + 1) +
              (2 * s + 1) * (q₂ + q₁ + s + 1))) * H := by
        simp only [piCodec_maxLen, prodCodec, finCodec]
        have hw := Nat.mul_le_mul_left w hH
        have hsum : w + (taggedColumnCodec q₁ q₂ s C.2).maxLen ≤
            (w + 2 + (s + 1) +
              (2 * s + 1) * (q₂ + q₁ + s + 1)) * H := by
          nlinarith
        have := Nat.mul_le_mul_left Q hsum
        nlinarith
      have hcol :
          (prodCodec (finCodec Q)
            (piCodec (rawRowCodec q₁ q₂ s C.1 ci) w)).maxLen ≤
            (Q + w * (3 + s + q₂ * q₁ + q₂)) * H := by
        simp only [prodCodec, finCodec, piCodec_maxLen]
        have hQ := Nat.mul_le_mul_left Q hH
        have hr := Nat.mul_le_mul_left w hraw
        nlinarith
      change (piCodec (prodCodec (finCodec w)
        (taggedColumnCodec q₁ q₂ s C.2)) Q).maxLen ≤ M * T ^ (k + 1) ∧
        (prodCodec (finCodec Q)
          (piCodec (rawRowCodec q₁ q₂ s C.1 ci) w)).maxLen ≤ M * T ^ (k + 1)
      have hrowT : Q * (w + 2 + (s + 1) +
          (2 * s + 1) * (q₂ + q₁ + s + 1)) ≤ T := by
        dsimp [T, labelStepCap]
        omega
      have hcolT : Q + w * (3 + s + q₂ * q₁ + q₂) ≤ T := by
        dsimp [T, labelStepCap]
        omega
      constructor
      · calc
          _ ≤ (Q * (w + 2 + (s + 1) +
                  (2 * s + 1) * (q₂ + q₁ + s + 1))) * H := hrow
          _ ≤ T * H := Nat.mul_le_mul_right H hrowT
          _ = M * T ^ (k + 1) := by dsimp [H]; rw [pow_succ]; ring
      · calc
          _ ≤ (Q + w * (3 + s + q₂ * q₁ + q₂)) * H := hcol
          _ ≤ T * H := Nat.mul_le_mul_right H hcolT
          _ = M * T ^ (k + 1) := by dsimp [H]; rw [pow_succ]; ring

theorem labelStepCap_le_cube (s q₁ q₂ w Q B : ℕ)
    (hB : 1 ≤ B) (hs : s ≤ B) (hq₁ : q₁ ≤ B)
    (hq₂ : q₂ ≤ B) (hw : w ≤ B) (hQ : Q ≤ B) :
    labelStepCap s q₁ q₂ w Q ≤ 32 * B ^ 3 := by
  have hB2 : B ≤ B ^ 2 := by nlinarith
  have hB3 : B ^ 2 ≤ B ^ 3 := by
    have := Nat.mul_le_mul_left (B ^ 2) hB
    nlinarith
  have hrow : Q * (w + 2 + (s + 1) +
      (2 * s + 1) * (q₂ + q₁ + s + 1)) ≤
      B * (B + 2 + (B + 1) + (2 * B + 1) * (3 * B + 1)) := by
    gcongr; omega
  have hcol : Q + w * (3 + s + q₂ * q₁ + q₂) ≤
      B + B * (3 + B + B * B + B) := by
    gcongr
  have hrow' : B * (B + 2 + (B + 1) +
      (2 * B + 1) * (3 * B + 1)) ≤ 24 * B ^ 3 := by
    nlinarith
  have hcol' : B + B * (3 + B + B * B + B) ≤ 8 * B ^ 3 := by
    nlinarith
  unfold labelStepCap
  omega

theorem scheduled_codec_maxLen_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ)
    (hn : n ≤ 2 ^ L) :
    (scheduledCarrierCodecs n m L Δ γ k).1.maxLen ≤
        2 ^ (26 * (k + 1) * L) ∧
    (scheduledCarrierCodecs n m L Δ γ k).2.maxLen ≤
        2 ^ (26 * (k + 1) * L) := by
  rcases hc with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hover, hL, hseed⟩
  let B := 2 ^ (7 * L)
  let p := LookupSeed.width L
  let s := SourceProfileParameters.width L
  let q₁ := s - 2
  let q₂ := SourceProfileParameters.outerWidth L
  let w := ParameterizedCanonicalSource.restorationWidth L
  let Q := ParameterizedCanonicalSource.coverWidth n m L Δ γ
  let ci := defaultItemCodec n s
  let M := max 1 (max p (max p ci.maxLen))
  let T := labelStepCap s q₁ q₂ w Q
  have hB : 1 ≤ B := by dsimp [B]; exact Nat.one_le_two_pow
  have hExp : SourceProfileParameters.exponent L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    omega
  have hOuter : SourceProfileParameters.outerExponent L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    omega
  have hr : ParameterizedCanonicalSource.restorationDepth L ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    dsimp [ParameterizedCanonicalSource.restorationDepth]
    omega
  have hq : ParameterizedCanonicalSource.coverDepth n m L Δ γ ≤ 7 * L := by
    unfold SourceOverheadBounds.overhead at hover
    dsimp [ParameterizedCanonicalSource.coverDepth]
    omega
  have hp : p ≤ B := by
    change 2 ^ LookupSeed.exponent L ≤ 2 ^ (7 * L)
    exact pow_le_pow_right₀ (by omega) (by omega)
  have hs : s ≤ B := by
    change 2 ^ SourceProfileParameters.exponent L ≤ 2 ^ (7 * L)
    exact pow_le_pow_right₀ (by omega) hExp
  have hq₁ : q₁ ≤ B := (Nat.sub_le _ _).trans hs
  have hq₂ : q₂ ≤ B := by
    change 2 ^ SourceProfileParameters.outerExponent L ≤ 2 ^ (7 * L)
    exact pow_le_pow_right₀ (by omega) hOuter
  have hw : w ≤ B := by
    change 2 ^ ParameterizedCanonicalSource.restorationDepth L ≤ 2 ^ (7 * L)
    exact pow_le_pow_right₀ (by omega) hr
  have hQ : Q ≤ B := by
    rw [show Q = 2 ^ ParameterizedCanonicalSource.coverDepth n m L Δ γ from
      SourceOverheadBounds.actualQ_pow (V := Fin n) (E := Fin m) L γ Δ]
    exact pow_le_pow_right₀ (by omega) hq
  have hnB : n ≤ B := by
    calc
      n ≤ 2 ^ L := hn
      _ ≤ 2 ^ (7 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hci : ci.maxLen ≤ 6 * B := by
    rw [show ci.maxLen = 4 * s + (1 + max n (s - 3)) from
      default_item_maxLen n s]
    omega
  have hM : M ≤ 8 * B := by dsimp [M]; omega
  have hT : T ≤ 32 * B ^ 3 :=
    labelStepCap_le_cube s q₁ q₂ w Q B hB hs hq₁ hq₂ hw hQ
  have hMpow : M ≤ 2 ^ (8 * L) := by
    calc
      M ≤ 8 * B := hM
      _ = 2 ^ (3 + 7 * L) := by norm_num [B, pow_add]
      _ ≤ 2 ^ (8 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hTpow : T ≤ 2 ^ (26 * L) := by
    calc
      T ≤ 32 * B ^ 3 := hT
      _ = 2 ^ (5 + 21 * L) := by
        have he : 21 * L = (7 * L) * 3 := by omega
        rw [he, pow_add, pow_mul]
        norm_num [B]
      _ ≤ 2 ^ (26 * L) := pow_le_pow_right₀ (by omega) (by omega)
  have hb := carrierCodecs_maxLen_le s q₁ q₂ w Q
    (piCodec boolCodec p) (finCodec p) ci k
  have hb' : (scheduledCarrierCodecs n m L Δ γ k).1.maxLen ≤ M * T ^ k ∧
      (scheduledCarrierCodecs n m L Δ γ k).2.maxLen ≤ M * T ^ k := by
    simp only [piCodec_maxLen, boolCodec, mul_one] at hb
    change (scheduledCarrierCodecs n m L Δ γ k).1.maxLen ≤ M * T ^ k ∧
      (scheduledCarrierCodecs n m L Δ γ k).2.maxLen ≤ M * T ^ k at hb
    exact hb
  have htarget : M * T ^ k ≤ 2 ^ (26 * (k + 1) * L) := by
    have hpow := Nat.pow_le_pow_left hTpow k
    calc
      M * T ^ k ≤ 2 ^ (8 * L) * (2 ^ (26 * L)) ^ k :=
        Nat.mul_le_mul hMpow hpow
      _ = 2 ^ ((8 + 26 * k) * L) := by rw [← pow_mul, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (26 * (k + 1) * L) := by
        have he : 8 + 26 * k ≤ 26 * (k + 1) := by omega
        exact pow_le_pow_right₀ (by omega) (Nat.mul_le_mul_right L he)
  exact ⟨hb'.1.trans htarget, hb'.2.trans htarget⟩

theorem scheduled_row_encoded_length_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (hn : n ≤ 2 ^ L)
    (x : Row (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k) :
    ((scheduledCarrierCodecs n m L Δ γ k).1.encode x).length ≤
      2 ^ (26 * (k + 1) * L) :=
  ((scheduledCarrierCodecs n m L Δ γ k).1.length_le x).trans
    (scheduled_codec_maxLen_le L Δ γ k hc hn).1

theorem scheduled_column_encoded_length_le {n m : ℕ} [NeZero n]
    (L Δ : ℕ) (γ : ℚ) (k : ℕ)
    (hc : CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) L Δ γ) (hn : n ≤ 2 ^ L)
    (y : Column (Fin (LookupSeed.width L) → Bool) (Fin (LookupSeed.width L))
      (SourceConstruction.Items (SourceProfileParameters.width L) (Fin n))
      (SourceProfileParameters.width L) (SourceProfileParameters.width L - 2)
      (SourceProfileParameters.outerWidth L)
      (ParameterizedCanonicalSource.restorationWidth L)
      (ParameterizedCanonicalSource.coverWidth n m L Δ γ) k) :
    ((scheduledCarrierCodecs n m L Δ γ k).2.encode y).length ≤
      2 ^ (26 * (k + 1) * L) :=
  ((scheduledCarrierCodecs n m L Δ γ k).2.length_le y).trans
    (scheduled_codec_maxLen_le L Δ γ k hc hn).2

end Paper2.RecursiveLabelCodecScratch
