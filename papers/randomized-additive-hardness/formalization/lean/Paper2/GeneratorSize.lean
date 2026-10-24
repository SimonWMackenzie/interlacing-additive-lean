import Paper2.GeneratorSource
import Paper2.GeneratorSerialization
import Mathlib.Tactic

/-! Exact unary serialization accounting for the actual recursive generator. -/

namespace Paper2.GeneratorSize

open Paper2.GeneratorCode Paper2.GeneratorSource Paper2.GeneratorSerialization

set_option maxHeartbeats 1000000

theorem copies_size (n : Nat) (c : Code) :
    codeSize (copies n c) = n * (codeSize c + 3) + 4 := by
  induction n with
  | zero => simp [copies, codeSize]
  | succ n ih => simp [copies, codeSize, ih, Nat.succ_mul]; omega

theorem outer_size (q₁ q₂ s : Nat) (c : Code) :
    codeSize (outerCode q₁ q₂ s c) =
      q₂ + 11 + (q₁ + s + 1) * (codeSize c + 3) := by
  simp [outerCode, codeSize, copies_size]
  omega

theorem raw_size (q₁ q₂ s : Nat) (c : Code) :
    codeSize (rawCode q₁ q₂ s c) =
      11 + (s + 1) * (codeSize c + 3) +
        s * (codeSize (outerCode q₁ q₂ s c) + 3) := by
  simp [rawCode, codeSize, copies_size]
  omega

theorem fixedTail_size (q₁ q₂ s : Nat) (c : Code) :
    codeSize (fixedTailCode q₁ q₂ s c) =
      s * (codeSize (outerCode q₁ q₂ s c) + 3) + 4 := by
  simp [fixedTailCode, copies_size]

theorem tagged_size (q₁ q₂ s : Nat) (c : Code) :
    codeSize (taggedCode q₁ q₂ s c) =
      802 + codeSize (rawCode q₁ q₂ s c) +
        codeSize (fixedTailCode q₁ q₂ s c) +
        codeSize (outerCode q₁ q₂ s c) := by
  simp [taggedCode, codeSize]
  omega

theorem template_size (q₁ q₂ : Nat) (c : Code) :
    codeSize (templateCode q₁ q₂ c) =
      q₂ * (codeSize c + q₁ + 10) + 4 := by
  simp [templateCode, copies_size, codeSize]
  omega

theorem templateRow_size (q₁ q₂ s : Nat) (c : Code) :
    codeSize (templateRowCode q₁ q₂ s c) =
      s + 7 + codeSize (templateCode q₁ q₂ c) := by
  simp [templateRowCode, codeSize]
  omega

theorem vertexLabels_size (n s : Nat) :
    codeSize (vertexLabelsCode (V := Fin n) s) = 4 * s + n + 20 := by
  simp [vertexLabelsCode, codeSize]
  omega

theorem auxiliaryLabels_size (s : Nat) :
    codeSize (auxiliaryLabelsCode s) = 4 * s + (s - 3) + 20 := by
  simp [auxiliaryLabelsCode, codeSize]
  omega

theorem rows_size (q₁ q₂ s : Nat) (vertices auxiliaries c : Code) :
    codeSize (rowsCode q₁ q₂ s vertices auxiliaries c) =
      1572 + codeSize (templateRowCode q₁ q₂ s c) +
        codeSize vertices + codeSize auxiliaries + 2 * codeSize c := by
  simp [rowsCode, codeSize]
  omega

theorem graphRows_size (n q₁ q₂ s : Nat) (c : Code) :
    codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c) =
      1572 + codeSize (templateRowCode q₁ q₂ s c) +
        (4 * s + n + 20) + (4 * s + (s - 3) + 20) +
        2 * codeSize c := by
  simp [graphRowsCode, rows_size, vertexLabels_size, auxiliaryLabels_size]

theorem recursive_row_size (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).1 =
      Q * (w + 10 +
        codeSize (taggedCode q₁ q₂ s
          (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2)) + 4 := by
  simp [recursiveCodes, copies_size, codeSize]
  omega

theorem recursive_col_size (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).2 =
      Q + 11 + w *
        (codeSize (graphRowsCode (V := Fin n) q₁ q₂ s
          (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1) + 3) := by
  simp [recursiveCodes, copies_size, codeSize]
  omega

def scale (n p s q₁ q₂ w Q : Nat) : Nat :=
  n + p + s + q₁ + q₂ + w + Q + 513

theorem scale_ge (n p s q₁ q₂ w Q : Nat) :
    513 ≤ scale n p s q₁ q₂ w Q := by
  unfold scale
  omega

theorem scalar_le_scale (n p s q₁ q₂ w Q : Nat) :
    n ≤ scale n p s q₁ q₂ w Q ∧
    p ≤ scale n p s q₁ q₂ w Q ∧
    s + 1 ≤ scale n p s q₁ q₂ w Q ∧
    q₁ + s + 1 ≤ scale n p s q₁ q₂ w Q ∧
    q₂ + 11 ≤ scale n p s q₁ q₂ w Q ∧
    w + 10 ≤ scale n p s q₁ q₂ w Q ∧
    Q + 11 ≤ scale n p s q₁ q₂ w Q := by
  unfold scale
  omega

private theorem inflate (T c : Nat) (hT : 3 ≤ T) :
    c + 3 ≤ T * (c + 1) := by
  nlinarith

theorem outer_le_scale (n p s q₁ q₂ w Q : Nat) (c : Code) :
    codeSize (outerCode q₁ q₂ s c) ≤
      (scale n p s q₁ q₂ w Q)^3 * (codeSize c + 1) := by
  let T := scale n p s q₁ q₂ w Q
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have h1 : q₂ + 11 ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.2.2.2.1
  have h2 : q₁ + s + 1 ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.2.2.1
  have h3 : codeSize c + 3 ≤ T * (codeSize c + 1) := inflate T _ (by omega)
  rw [outer_size]
  calc
    q₂ + 11 + (q₁ + s + 1) * (codeSize c + 3)
        ≤ T + T * (T * (codeSize c + 1)) := by gcongr
    _ ≤ T ^ 3 * (codeSize c + 1) := by
      have hx : 1 ≤ codeSize c + 1 := by omega
      have hsq : T + 1 ≤ T ^ 2 := by nlinarith
      have hm := Nat.mul_le_mul_right (codeSize c + 1) hsq
      nlinarith

theorem raw_le_scale (n p s q₁ q₂ w Q : Nat) (c : Code) :
    codeSize (rawCode q₁ q₂ s c) ≤
      (scale n p s q₁ q₂ w Q)^5 * (codeSize c + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hs : s + 1 ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.2.1
  have hC : codeSize c + 3 ≤ T * X := inflate T _ (by omega)
  have hO : codeSize (outerCode q₁ q₂ s c) ≤ T^3 * X :=
    outer_le_scale _ _ _ _ _ _ _ _
  have h1 : T^2 * X ≤ T^4 * X := by
    gcongr <;> omega
  have h2 : 4*T ≤ T^4 * X := by
    have hpow : 4 ≤ T^3 * X := by
      have ht3 : 4 ≤ T^3 := by nlinarith
      calc
        4 ≤ T^3 := ht3
        _ = T^3 * 1 := by omega
        _ ≤ T^3 * X := Nat.mul_le_mul_left _ hX
    calc
      4*T = T*4 := by omega
      _ ≤ T*(T^3*X) := Nat.mul_le_mul_left T hpow
      _ = T^4*X := by ring
  have h3 : 3*(T^4*X) ≤ T^5*X := by
    calc
      3*(T^4*X) = (3*T^4)*X := by ring
      _ ≤ (T*T^4)*X := by gcongr; omega
      _ = T^5*X := by ring
  rw [raw_size]
  calc
    11 + (s + 1) * (codeSize c + 3) +
        s * (codeSize (outerCode q₁ q₂ s c) + 3)
      ≤ T + T*(T*X) + T*(T^3*X+3) := by gcongr <;> omega
    _ ≤ T^5*X := by nlinarith

private theorem step_le (T X a b e : Nat)
    (hT : 5 ≤ T) (hX : 1 ≤ X) (ha : a ≤ T)
    (hb : b ≤ X) (he : e ≤ T) :
    e + a * (b + 3) ≤ T^2 * X := by
  calc
    e + a * (b + 3) ≤ T + T * (X + 3) := by gcongr
    _ ≤ T^2 * X := by
      have h5 : 5*T ≤ T^2 := by nlinarith
      have hm := Nat.mul_le_mul_right X h5
      nlinarith

private theorem pow_lift (T X a b : Nat) (hT : 1 ≤ T)
    (_hX : 1 ≤ X) (hab : a ≤ b) :
    T^a * X ≤ T^b * X := by
  gcongr

theorem fixedTail_le_scale (n p s q₁ q₂ w Q : Nat) (c : Code) :
    codeSize (fixedTailCode q₁ q₂ s c) ≤
      (scale n p s q₁ q₂ w Q)^5 * (codeSize c + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hs : s ≤ T := by have h := (scalar_le_scale n p s q₁ q₂ w Q).2.2.1; omega
  have hO : codeSize (outerCode q₁ q₂ s c) ≤ T^3 * X :=
    outer_le_scale _ _ _ _ _ _ _ _
  have hY : 1 ≤ T^3 * X := by
    have ht : 1 ≤ T^3 := by exact Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc
    codeSize (fixedTailCode q₁ q₂ s c) =
        4 + s * (codeSize (outerCode q₁ q₂ s c) + 3) := by
          rw [fixedTail_size]; omega
    _ ≤ T^2*(T^3*X) :=
      step_le T (T^3*X) s (codeSize (outerCode q₁ q₂ s c)) 4
        (by omega) hY hs hO (by omega)
    _ = T^5*X := by ring

theorem tagged_le_scale (n p s q₁ q₂ w Q : Nat) (c : Code) :
    codeSize (taggedCode q₁ q₂ s c) ≤
      (scale n p s q₁ q₂ w Q)^6 * (codeSize c + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hR : codeSize (rawCode q₁ q₂ s c) ≤ T^5*X :=
    raw_le_scale _ _ _ _ _ _ _ _
  have hF : codeSize (fixedTailCode q₁ q₂ s c) ≤ T^5*X :=
    fixedTail_le_scale _ _ _ _ _ _ _ _
  have hO : codeSize (outerCode q₁ q₂ s c) ≤ T^3*X :=
    outer_le_scale _ _ _ _ _ _ _ _
  have hO' : codeSize (outerCode q₁ q₂ s c) ≤ T^5*X :=
    hO.trans (pow_lift T X 3 5 (by omega) hX (by omega))
  have h802 : 802 ≤ T^5*X := by
    have hsq : 802 ≤ T^2 := by nlinarith
    have hp : T^2 ≤ T^5 := by gcongr <;> omega
    have h : 802 ≤ T^5 := hsq.trans hp
    calc
      802 ≤ T^5 := h
      _ = T^5*1 := by omega
      _ ≤ T^5*X := Nat.mul_le_mul_left _ hX
  rw [tagged_size]
  have hm : 4*(T^5*X) ≤ T^6*X := by
    calc
      4*(T^5*X) = (4*T^5)*X := by ring
      _ ≤ (T*T^5)*X := by gcongr; omega
      _ = T^6*X := by ring
  change 802 + codeSize (rawCode q₁ q₂ s c) +
    codeSize (fixedTailCode q₁ q₂ s c) +
    codeSize (outerCode q₁ q₂ s c) ≤ T^6*X
  omega

theorem template_le_scale (n p s q₁ q₂ w Q : Nat) (c : Code) :
    codeSize (templateCode q₁ q₂ c) ≤
      (scale n p s q₁ q₂ w Q)^3 * (codeSize c + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hq : q₁ + 7 ≤ T := by unfold T scale; omega
  have hq₂ : q₂ ≤ T := by unfold T scale; omega
  have hb : codeSize c + q₁ + 7 ≤ T*X := by
    have hm := Nat.mul_le_mul_right (codeSize c) (show 1 ≤ T by omega)
    dsimp [X]
    nlinarith
  calc
    codeSize (templateCode q₁ q₂ c) =
        4 + q₂ * (codeSize c + q₁ + 7 + 3) := by
          rw [template_size]; ring
    _ ≤ T^2*(T*X) :=
      step_le T (T*X) q₂ (codeSize c + q₁ + 7) 4
        (by omega) (by nlinarith) hq₂ hb (by omega)
    _ = T^3*X := by ring

theorem templateRow_le_scale (n p s q₁ q₂ w Q : Nat) (c : Code) :
    codeSize (templateRowCode q₁ q₂ s c) ≤
      (scale n p s q₁ q₂ w Q)^4 * (codeSize c + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hs : s + 7 ≤ T := by unfold T scale; omega
  have ht : codeSize (templateCode q₁ q₂ c) ≤ T^3*X :=
    template_le_scale _ _ _ _ _ _ _ _
  have hsmall : T ≤ T^3*X := by
    have hh : T ≤ T^3 := by
      have hp : T^1 ≤ T^3 := by gcongr <;> omega
      simpa using hp
    exact hh.trans (by nlinarith)
  have htwo : 2*(T^3*X) ≤ T^4*X := by
    calc
      2*(T^3*X) = (2*T^3)*X := by ring
      _ ≤ (T*T^3)*X := by gcongr; omega
      _ = T^4*X := by ring
  rw [templateRow_size]
  change s + 7 + codeSize (templateCode q₁ q₂ c) ≤ T^4*X
  omega

private theorem sum5_le (T Y a b c d e : Nat) (hT : 5 ≤ T)
    (ha : a ≤ Y) (hb : b ≤ Y) (hc : c ≤ Y)
    (hd : d ≤ Y) (he : e ≤ Y) :
    a + b + c + d + e ≤ T*Y := by
  have hm : 5*Y ≤ T*Y := Nat.mul_le_mul_right Y hT
  omega

theorem graphRows_le_scale (n p s q₁ q₂ w Q : Nat) (c : Code) :
    codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c) ≤
      (scale n p s q₁ q₂ w Q)^5 * (codeSize c + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hn : n ≤ T := (scalar_le_scale _ _ _ _ _ _ _).1
  have hs : s ≤ T := by have h := (scalar_le_scale n p s q₁ q₂ w Q).2.2.1; omega
  have htemplate : codeSize (templateRowCode q₁ q₂ s c) ≤ T^4*X :=
    templateRow_le_scale _ _ _ _ _ _ _ _
  have hpow : T^2*X ≤ T^4*X := pow_lift T X 2 4 (by omega) hX (by omega)
  have hbase : T^2 ≤ T^2*X := by
    calc
      T^2 = T^2*1 := by omega
      _ ≤ T^2*X := Nat.mul_le_mul_left _ hX
  have hconst : 1572 ≤ T^4*X := by
    have hh : 1572 ≤ T^2 := by nlinarith
    exact hh.trans (hbase.trans hpow)
  have hvertex : 4*s+n+20 ≤ T^4*X := by
    have hh : 4*s+n+20 ≤ T^2 := by nlinarith
    exact hh.trans (hbase.trans hpow)
  have haux : 4*s+(s-3)+20 ≤ T^4*X := by
    have hh : 4*s+(s-3)+20 ≤ T^2 := by
      have hsub : s-3 ≤ s := Nat.sub_le s 3
      nlinarith
    exact hh.trans (hbase.trans hpow)
  have hc : 2*codeSize c ≤ T^4*X := by
    calc
      2*codeSize c ≤ 2*X := by omega
      _ ≤ T^2*X := by gcongr; nlinarith
      _ ≤ T^4*X := hpow
  rw [graphRows_size]
  change 1572 + codeSize (templateRowCode q₁ q₂ s c) +
    (4*s+n+20) + (4*s+(s-3)+20) + 2*codeSize c ≤ T^5*X
  calc
    1572 + codeSize (templateRowCode q₁ q₂ s c) +
        (4*s+n+20) + (4*s+(s-3)+20) + 2*codeSize c
      ≤ T*(T^4*X) :=
        sum5_le T (T^4*X) 1572
          (codeSize (templateRowCode q₁ q₂ s c))
          (4*s+n+20) (4*s+(s-3)+20) (2*codeSize c)
          (by omega) hconst htemplate hvertex haux hc
    _ = T^5*X := by ring

theorem recursive_row_le_scale (n p s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).1 ≤
      (scale n p s q₁ q₂ w Q)^8 *
        (codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let c := (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ X := by omega
  have hQ : Q ≤ T := by unfold T scale; omega
  have hw : w + 10 ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.2.2.2.2.1
  have htag : codeSize (taggedCode q₁ q₂ s c) ≤ T^6*X :=
    tagged_le_scale _ _ _ _ _ _ _ _
  have hpow : T^2*X ≤ T^7*X := pow_lift T X 2 7 (by omega) hX (by omega)
  have hbase : T^2 ≤ T^2*X := by
    calc
      T^2 = T^2*1 := by omega
      _ ≤ T^2*X := Nat.mul_le_mul_left _ hX
  have h4 : 4 ≤ T^7*X := by
    have hh : 4 ≤ T^2 := by nlinarith
    exact hh.trans (hbase.trans hpow)
  have h3 : 3*(T^7*X) ≤ T^8*X := by
    calc
      3*(T^7*X) = (3*T^7)*X := by ring
      _ ≤ (T*T^7)*X := by gcongr; omega
      _ = T^8*X := by ring
  rw [recursive_row_size]
  change Q*(w+10+codeSize (taggedCode q₁ q₂ s c))+4 ≤ T^8*X
  calc
    Q*(w+10+codeSize (taggedCode q₁ q₂ s c))+4
      ≤ T*(T+T^6*X)+4 := by gcongr
    _ ≤ T^8*X := by nlinarith

theorem recursive_col_le_scale (n p s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).2 ≤
      (scale n p s q₁ q₂ w Q)^7 *
        (codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1 + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let c := (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1
  let X := codeSize c + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hX : 1 ≤ T^5*X := by
    calc
      1 ≤ T^5 := Nat.one_le_pow _ _ (by omega)
      _ = T^5*1 := by omega
      _ ≤ T^5*X := Nat.mul_le_mul_left _ (by dsimp [X]; omega)
  have hw : w ≤ T := by unfold T scale; omega
  have hQ : Q+11 ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.2.2.2.2.2
  have hgraph : codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c) ≤ T^5*X :=
    graphRows_le_scale _ _ _ _ _ _ _ _
  calc
    codeSize (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).2 =
        Q+11+w*(codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c)+3) := by
          exact recursive_col_size _ _ _ _ _ _ _ _ _
    _ ≤ T^2*(T^5*X) :=
      step_le T (T^5*X) w
        (codeSize (graphRowsCode (V := Fin n) q₁ q₂ s c)) (Q+11)
        (by omega) hX hw hgraph hQ
    _ = T^7*X := by ring

theorem recursive_total_step (n p s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    let T := scale n p s q₁ q₂ w Q
    let old := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
    let new := recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)
    codeSize new.1 + codeSize new.2 + 1 ≤
      T^9 * (codeSize old.1 + codeSize old.2 + 1) := by
  let T := scale n p s q₁ q₂ w Q
  let old := recursiveCodes n s q₁ q₂ w Q row₀ col₀ k
  let new := recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)
  let Z := codeSize old.1 + codeSize old.2 + 1
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  have hZ : 1 ≤ Z := by dsimp [Z]; omega
  have hr₀ : codeSize new.1 ≤ T^8*(codeSize old.2+1) :=
    recursive_row_le_scale _ _ _ _ _ _ _ _ _ _
  have hc₀ : codeSize new.2 ≤ T^7*(codeSize old.1+1) :=
    recursive_col_le_scale _ _ _ _ _ _ _ _ _ _
  have hr : codeSize new.1 ≤ T^8*Z := by
    exact hr₀.trans (Nat.mul_le_mul_left _ (by dsimp [Z]; omega))
  have hc : codeSize new.2 ≤ T^8*Z := by
    calc
      codeSize new.2 ≤ T^7*(codeSize old.1+1) := hc₀
      _ ≤ T^7*Z := Nat.mul_le_mul_left _ (by dsimp [Z]; omega)
      _ ≤ T^8*Z := pow_lift T Z 7 8 (by omega) hZ (by omega)
  have hone : 1 ≤ T^8*Z := by
    calc
      1 ≤ T^8 := Nat.one_le_pow _ _ (by omega)
      _ = T^8*1 := by omega
      _ ≤ T^8*Z := Nat.mul_le_mul_left _ hZ
  have hm : 3*(T^8*Z) ≤ T^9*Z := by
    calc
      3*(T^8*Z) = (3*T^8)*Z := by ring
      _ ≤ (T*T^8)*Z := by gcongr; omega
      _ = T^9*Z := by ring
  change codeSize new.1 + codeSize new.2 + 1 ≤ T^9*Z
  omega

theorem seed_total_le_scale (n p s q₁ q₂ w Q k : Nat) :
    let pair := seedRecursiveCodes n p s q₁ q₂ w Q k
    codeSize pair.1 + codeSize pair.2 + 1 ≤
      (scale n p s q₁ q₂ w Q)^(9*(k+1)) := by
  let T := scale n p s q₁ q₂ w Q
  have hT : 513 ≤ T := scale_ge _ _ _ _ _ _ _
  induction k with
  | zero =>
      have hp : p ≤ T := (scalar_le_scale _ _ _ _ _ _ _).2.1
      have hbase : 7*p+9 ≤ T^2 := by nlinarith
      have hpow : T^2 ≤ T^9 := by gcongr <;> omega
      change codeSize (copies p .bit) + codeSize (.ticket p) + 1 ≤ T^9
      rw [copies_size]
      simp only [codeSize]
      omega
  | succ k ih =>
      have hs := recursive_total_step n p s q₁ q₂ w Q
        (copies p .bit) (.ticket p) k
      dsimp [seedRecursiveCodes] at ih ⊢
      calc
        codeSize (recursiveCodes n s q₁ q₂ w Q (copies p .bit) (.ticket p) (k+1)).1 +
          codeSize (recursiveCodes n s q₁ q₂ w Q (copies p .bit) (.ticket p) (k+1)).2 + 1
          ≤ T^9 *
            (codeSize (recursiveCodes n s q₁ q₂ w Q (copies p .bit) (.ticket p) k).1 +
              codeSize (recursiveCodes n s q₁ q₂ w Q (copies p .bit) (.ticket p) k).2 + 1) := hs
        _ ≤ T^9 * T^(9*(k+1)) := Nat.mul_le_mul_left _ ih
        _ = T^(9*((k+1)+1)) := by
          rw [← pow_add]
          congr 1
          omega

theorem seed_total_le_cap (M n p s q₁ q₂ w Q k : Nat)
    (hM : 512 ≤ M)
    (hn : n ≤ M) (hp : p ≤ M) (hs : s ≤ M)
    (hq₁ : q₁ ≤ M) (hq₂ : q₂ ≤ M)
    (hw : w ≤ M) (hQ : Q ≤ M) :
    let pair := seedRecursiveCodes n p s q₁ q₂ w Q k
    codeSize pair.1 + codeSize pair.2 + 1 ≤
      (M+1)^(18*(k+1)) := by
  let T := scale n p s q₁ q₂ w Q
  have hsum : T ≤ 7*M+513 := by unfold T scale; omega
  have hmul := Nat.mul_le_mul_right M hM
  have hT : T ≤ (M+1)^2 := by nlinarith
  have hpow : T^(9*(k+1)) ≤ ((M+1)^2)^(9*(k+1)) := by gcongr
  have hseed := seed_total_le_scale n p s q₁ q₂ w Q k
  calc
    codeSize (seedRecursiveCodes n p s q₁ q₂ w Q k).1 +
        codeSize (seedRecursiveCodes n p s q₁ q₂ w Q k).2 + 1
      ≤ T^(9*(k+1)) := hseed
    _ ≤ ((M+1)^2)^(9*(k+1)) := hpow
    _ = (M+1)^(18*(k+1)) := by
      have hexp : 2*(9*(k+1)) = 18*(k+1) := by omega
      rw [← pow_mul, hexp]

theorem scheduled_total_le_cap (M n m L Δ : Nat) (γ : ℚ) (k : Nat)
    (hM : 512 ≤ M)
    (hn : n ≤ M)
    (hp : LookupSeed.width L ≤ M)
    (hs : SourceProfileParameters.width L ≤ M)
    (hq₁ : SourceProfileParameters.width L - 2 ≤ M)
    (hq₂ : SourceProfileParameters.outerWidth L ≤ M)
    (hw : ParameterizedCanonicalSource.restorationWidth L ≤ M)
    (hQ : ParameterizedCanonicalSource.coverWidth n m L Δ γ ≤ M) :
    let pair := scheduledCodes n m L Δ γ k
    codeSize pair.1 + codeSize pair.2 + 1 ≤ (M+1)^(18*(k+1)) := by
  exact seed_total_le_cap M n
    (LookupSeed.width L) (SourceProfileParameters.width L)
    (SourceProfileParameters.width L - 2)
    (SourceProfileParameters.outerWidth L)
    (ParameterizedCanonicalSource.restorationWidth L)
    (ParameterizedCanonicalSource.coverWidth n m L Δ γ)
    k hM hn hp hs hq₁ hq₂ hw hQ

theorem nodes_le_codeSize (c : Code) : nodes c ≤ codeSize c := by
  induction c with
  | emit bits => simp [nodes, codeSize]; omega
  | ticket n => simp [nodes, codeSize]; omega
  | bit => simp [nodes, codeSize]
  | append left right ihl ihr => simp [nodes, codeSize]; omega
  | branch3 n a b first second third ihf ihs iht =>
      simp [nodes, codeSize]
      omega

theorem codeList_nodes_le_size (cs : List Code) :
    (cs.map nodes).sum ≤ codesSize cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [codesSize]
      exact Nat.add_le_add (nodes_le_codeSize c) ih

theorem state_weight_le_stateSize (st : State) :
    weight st ≤ stateSize st := by
  rcases st with ⟨todo, output⟩
  have h := codeList_nodes_le_size todo
  simp only [weight, stateSize]
  omega

theorem scheduled_nodes_le_cap (M n m L Δ : Nat) (γ : ℚ) (k : Nat)
    (hM : 512 ≤ M)
    (hn : n ≤ M)
    (hp : LookupSeed.width L ≤ M)
    (hs : SourceProfileParameters.width L ≤ M)
    (hq₁ : SourceProfileParameters.width L - 2 ≤ M)
    (hq₂ : SourceProfileParameters.outerWidth L ≤ M)
    (hw : ParameterizedCanonicalSource.restorationWidth L ≤ M)
    (hQ : ParameterizedCanonicalSource.coverWidth n m L Δ γ ≤ M) :
    let pair := scheduledCodes n m L Δ γ k
    nodes pair.1 + nodes pair.2 + 1 ≤ (M+1)^(18*(k+1)) := by
  have hc := scheduled_total_le_cap M n m L Δ γ k
    hM hn hp hs hq₁ hq₂ hw hQ
  have hr := nodes_le_codeSize (scheduledCodes n m L Δ γ k).1
  have hs := nodes_le_codeSize (scheduledCodes n m L Δ γ k).2
  omega

theorem scheduled_serialized_length_le_cap (M n m L Δ : Nat) (γ : ℚ) (k : Nat)
    (hM : 512 ≤ M)
    (hn : n ≤ M)
    (hp : LookupSeed.width L ≤ M)
    (hs : SourceProfileParameters.width L ≤ M)
    (hq₁ : SourceProfileParameters.width L - 2 ≤ M)
    (hq₂ : SourceProfileParameters.outerWidth L ≤ M)
    (hw : ParameterizedCanonicalSource.restorationWidth L ≤ M)
    (hQ : ParameterizedCanonicalSource.coverWidth n m L Δ γ ≤ M) :
    let pair := scheduledCodes n m L Δ γ k
    (encodeCode pair.1).length + (encodeCode pair.2).length + 1 ≤
      (M+1)^(18*(k+1)) := by
  simpa only [encodeCode_length] using
    scheduled_total_le_cap M n m L Δ γ k hM hn hp hs hq₁ hq₂ hw hQ

#print axioms copies_size
#print axioms tagged_size
#print axioms graphRows_size
#print axioms recursive_row_size
#print axioms recursive_col_size
#print axioms seed_total_le_cap
#print axioms scheduled_total_le_cap
#print axioms nodes_le_codeSize
#print axioms state_weight_le_stateSize
#print axioms scheduled_serialized_length_le_cap

end Paper2.GeneratorSize
