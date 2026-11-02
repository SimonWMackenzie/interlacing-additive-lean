import CurrentAdditive.PhysicalProducer

namespace CurrentAdditive.V40ConstructorComposition
open EthInapproximability.CurrentPaper

def coefficient (ca da cb db push aux : Nat) :=
  ca+2*(ca*push+1)+cb*(aux+ca*push+1)^db
def degree (da db : Nat) := (da+1)*(db+1)

/-- A physically computed auxiliary parameter, bounded in the original
input length, remains charged after an intermediate packet drops that
original word. This is arithmetic for actual sequential machine runs. -/
theorem time_bound (n ca da cb db push aux a middle : Nat)
    (ha : a≤aux*(n+1)) (hm : middle≤n+ca*(n+1)^da*push) :
    ca*(n+1)^da+2*middle+2+cb*(a+middle+1)^db ≤
      coefficient ca da cb db push aux*(n+1)^degree da db := by
  let Z := n+1
  have hZ : 1≤Z := by dsimp[Z];omega
  have hp : Z^da≤Z^(da+1) := Nat.pow_le_pow_right hZ (by omega)
  have hZp : Z≤Z^(da+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hZ (show 1≤da+1 by omega)
  have hm' : middle+1≤(ca*push+1)*Z^(da+1) := by
    have h := Nat.mul_le_mul_left (ca*push) hp
    dsimp only [Z] at hZp hp h ⊢
    nlinarith
  have ha' : a≤aux*Z^(da+1) := ha.trans (Nat.mul_le_mul_left aux hZp)
  have hsum : a+middle+1≤(aux+ca*push+1)*Z^(da+1) := by nlinarith
  have hsecond : cb*(a+middle+1)^db ≤
      cb*(aux+ca*push+1)^db*Z^((da+1)*db) := by
    calc
      _ ≤ cb*((aux+ca*push+1)*Z^(da+1))^db := by gcongr
      _ = _ := by rw [mul_pow,←pow_mul];ring
  have hpa : Z^da≤Z^degree da db := Nat.pow_le_pow_right hZ (by unfold degree;nlinarith)
  have hpt : Z^(da+1)≤Z^degree da db := Nat.pow_le_pow_right hZ (by unfold degree;nlinarith)
  have hpb : Z^((da+1)*db)≤Z^degree da db := Nat.pow_le_pow_right hZ (by unfold degree;nlinarith)
  have h1 := Nat.mul_le_mul_left ca hpa
  have h2 := Nat.mul_le_mul_left (2*(ca*push+1)) hpt
  have h3 := Nat.mul_le_mul_left (cb*(aux+ca*push+1)^db) hpb
  change ca*Z^da+2*middle+2+cb*(a+middle+1)^db≤coefficient ca da cb db push aux*Z^degree da db
  unfold coefficient
  nlinarith

end CurrentAdditive.V40ConstructorComposition
