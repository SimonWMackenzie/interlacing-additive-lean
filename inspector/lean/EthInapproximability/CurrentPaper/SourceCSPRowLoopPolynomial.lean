import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalCost

/-!
# Cubic bound for the fixed source-row loop

For fixed Boolean-CSP alphabet and arity, the parser/query controller is a
fixed finite program. Its syntactic maximum pushes per transition is a
constant. The following coefficient is symbolic; no large concrete value is
reduced by the kernel.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopPolynomial

open SourceCSPRowLoopAll SourceCSPRowLoopCost

variable {n a q : Nat}

def queryCoefficient (a q : Nat) : Nat :=
  6 * q + (2 * a ^ q + 6) + 100 * q * (q + 1) ^ 2

def resetCoefficient (a q : Nat) : Nat :=
  (q * 5 + 4) * (q + pushConstant q a * queryCoefficient a q) +
    (q * 5 + 4) + 5 + 2 * q

def rowCoefficient (a q : Nat) : Nat :=
  queryCoefficient a q + 1 + resetCoefficient a q

theorem queryCost_quadratic
    (row : Row (n := n) (a := a) (q := q))
    (rest : List Bool) (L : Nat)
    (hsource : (SourceCSPCodec.rowFields row ++ rest).length ≤ L)
    (hn : n ≤ q * L) :
    queryCost row rest n ≤ queryCoefficient a q * (L + 1) ^ 2 := by
  let X := L + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X ^ 2 := by nlinarith [Nat.zero_le X]
  have hnX : n + 1 ≤ (q + 1) * X := by
    dsimp [X]
    nlinarith [Nat.zero_le (q * L)]
  have hsq : (n + 1) ^ 2 ≤ (q + 1) ^ 2 * X ^ 2 := by
    calc
      (n + 1) ^ 2 ≤ ((q + 1) * X) ^ 2 := Nat.pow_le_pow_left hnX 2
      _ = (q + 1) ^ 2 * X ^ 2 := by ring
  have hlinear : q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) ≤
      (6 * q) * X ^ 2 := by
    have h₁ : 2 * (SourceCSPCodec.rowFields row ++ rest).length + 4 ≤
        6 * X := by dsimp [X]; omega
    calc
      _ ≤ q * (6 * X) := Nat.mul_le_mul_left q h₁
      _ = (6 * q) * X := by ring
      _ ≤ (6 * q) * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have hfixed : 2 * a ^ q + 6 ≤ (2 * a ^ q + 6) * X ^ 2 := by
    have hx : 1 ≤ X ^ 2 := by nlinarith
    simpa only [mul_one] using Nat.mul_le_mul_left (2 * a ^ q + 6) hx
  have hquad : q * 100 * (n + 1) ^ 2 ≤
      (100 * q * (q + 1) ^ 2) * X ^ 2 := by
    calc
      _ ≤ (q * 100) * ((q + 1) ^ 2 * X ^ 2) :=
        Nat.mul_le_mul_left (q * 100) hsq
      _ = (100 * q * (q + 1) ^ 2) * X ^ 2 := by ring
  have heq : queryCost row rest n =
      q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) +
        (2 * a ^ q + 6) + q * 100 * (n + 1) ^ 2 := by
    unfold queryCost
    ring
  rw [heq]
  have hadd := Nat.add_le_add (Nat.add_le_add hlinear hfixed) hquad
  convert hadd using 1 <;> simp [queryCoefficient, X] <;> ring

theorem resetBound_quadratic
    (row : Row (n := n) (a := a) (q := q))
    (rest : List Bool) (L : Nat)
    (hsource : (SourceCSPCodec.rowFields row ++ rest).length ≤ L)
    (hn : n ≤ q * L) :
    resetBound row rest ≤ resetCoefficient a q * (L + 1) ^ 2 := by
  let X := L + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X ^ 2 := by nlinarith [Nat.zero_le X]
  have hq := queryCost_quadratic row rest L hsource hn
  have hcap : (List.replicate (n - 1) true).length ≤ q * X ^ 2 := by
    simp only [List.length_replicate]
    have hn' : n - 1 ≤ q * L := (Nat.sub_le n 1).trans hn
    have hL : L ≤ X ^ 2 := by dsimp [X] at hX2 ⊢; omega
    calc
      _ ≤ q * L := hn'
      _ ≤ q * X ^ 2 := Nat.mul_le_mul_left q hL
  have hinner : (List.replicate (n - 1) true).length +
      pushConstant q a * queryCost row rest n ≤
      (q + pushConstant q a * queryCoefficient a q) * X ^ 2 := by
    have hm := Nat.mul_le_mul_left (pushConstant q a) hq
    calc
      _ ≤ q * X ^ 2 +
          pushConstant q a * (queryCoefficient a q * X ^ 2) :=
        Nat.add_le_add hcap hm
      _ = (q + pushConstant q a * queryCoefficient a q) * X ^ 2 := by ring
  have hbase := Nat.mul_le_mul_left (q * 5 + 4) hinner
  have htail : (q * 5 + 4) + 2 +
      (2 * (List.replicate (n - 1) true).length + 2) + 1 ≤
      ((q * 5 + 4) + 5 + 2 * q) * X ^ 2 := by
    have hcap2 := Nat.mul_le_mul_left 2 hcap
    have h1 : 1 ≤ X ^ 2 := by nlinarith
    nlinarith [Nat.mul_le_mul_left ((q * 5 + 4) + 5) h1]
  unfold resetBound resetCoefficient
  dsimp only
  calc
    _ = (q * 5 + 4) *
          ((List.replicate (n - 1) true).length +
            pushConstant q a * queryCost row rest n) +
        ((q * 5 + 4) + 2 +
          (2 * (List.replicate (n - 1) true).length + 2) + 1) := by ring
    _ ≤ (q * 5 + 4) *
          ((q + pushConstant q a * queryCoefficient a q) * X ^ 2) +
        ((q * 5 + 4) + 5 + 2 * q) * X ^ 2 :=
      Nat.add_le_add hbase htail
    _ = _ := by ring

theorem rowBound_quadratic
    (row : Row (n := n) (a := a) (q := q))
    (rest : List Bool) (L : Nat)
    (hsource : (SourceCSPCodec.rowFields row ++ rest).length ≤ L)
    (hn : n ≤ q * L) :
    SourceCSPRowLoopTotalCost.rowBound row rest ≤
      rowCoefficient a q * (L + 1) ^ 2 := by
  have hq := queryCost_quadratic row rest L hsource hn
  have hr := resetBound_quadratic row rest L hsource hn
  have h1 : 1 ≤ (L + 1) ^ 2 := by nlinarith
  unfold SourceCSPRowLoopTotalCost.rowBound rowCoefficient
  nlinarith

theorem totalBound_cubic
    (rows : List (Row (n := n) (a := a) (q := q))) (L : Nat)
    (hbytes : (rowBytes rows).length ≤ L) (hn : n ≤ q * L) :
    SourceCSPRowLoopTotalCost.totalBound rows ≤
      rows.length * rowCoefficient a q * (L + 1) ^ 2 := by
  induction rows with
  | nil => simp [SourceCSPRowLoopTotalCost.totalBound]
  | cons row tail ih =>
      have hhead : (SourceCSPCodec.rowFields row ++ rowBytes tail).length ≤ L := by
        simpa only [rowBytes_cons] using hbytes
      have htail : (rowBytes tail).length ≤ L := by
        simp only [List.length_append] at hhead
        omega
      have hr := rowBound_quadratic row (rowBytes tail) L hhead hn
      have ht := ih htail
      simp only [SourceCSPRowLoopTotalCost.totalBound, List.length_cons]
      nlinarith

theorem encoded_totalBound_cubic {a q : Nat}
    (P : EncodedETHSource.ConstraintInstance a q)
    (hsize : SourceCSPCodec.ValidSize P) :
    SourceCSPRowLoopTotalCost.totalBound
        (SourceCSPRowLoopEncoded.rowList P) ≤
      rowCoefficient a q *
        ((EncodedETHSource.constraintBits P).length + 1) ^ 3 := by
  let L := (EncodedETHSource.constraintBits P).length
  have hm : P.constraints ≤ L := SourceCSPCodec.constraints_le_bits P
  have hn : P.vertices ≤ q * L :=
    hsize.trans (Nat.mul_le_mul_left q hm)
  have hb : (rowBytes (SourceCSPRowLoopEncoded.rowList P)).length ≤ L := by
    rw [SourceCSPRowLoopEncoded.rowList_bytes]
    have he := SourceCSPCodec.constraintBits_eq P
    change (SourceCSPPositiveHeader.rows P).length ≤
      (EncodedETHSource.constraintBits P).length
    rw [he]
    simp only [SourceCSPPositiveHeader.rows, List.length_append]
    omega
  have ht := totalBound_cubic (SourceCSPRowLoopEncoded.rowList P) L hb hn
  rw [SourceCSPRowLoopEncoded.rowList_length] at ht
  have hmX : P.constraints ≤ L + 1 := by omega
  have hh := Nat.mul_le_mul_right
    (rowCoefficient a q * (L + 1) ^ 2) hmX
  calc
    _ ≤ P.constraints * rowCoefficient a q * (L + 1) ^ 2 := ht
    _ ≤ (L + 1) * (rowCoefficient a q * (L + 1) ^ 2) := by
      convert hh using 1 <;> ring
    _ = rowCoefficient a q * (L + 1) ^ 3 := by ring

end EthInapproximability.CurrentPaper.SourceCSPRowLoopPolynomial
