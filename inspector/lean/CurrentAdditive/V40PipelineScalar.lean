import CurrentAdditive.V39UniformResource

namespace CurrentAdditive.V40PipelineScalar
set_option maxHeartbeats 16000000

def degree (a b e dt : Nat) := (a+b+e+1)*(dt+1)+1
def coefficient (p t ct dt : Nat) := 2*p+11+ct*2^dt*(t+1)
def exponent (p t ct dt a b e : Nat) :=
  V39UniformResource.seedExponent (coefficient p t ct dt) (degree a b e dt)

theorem bound (q a b e p t ct dt lx tp packet word out : Nat) (hq : 2 ≤ q)
    (hx : lx ≤ q^a) (hp : tp ≤ q^b) (hpacket : packet ≤ lx+tp*p)
    (hword : word ≤ q^e) (hout : out ≤ word+ct*(word+1)^dt*t) :
    tp+2*packet+2+q^e+2*word+2+ct*(word+1)^dt ≤ q^(exponent p t ct dt a b e) ∧
    out ≤ q^(exponent p t ct dt a b e) := by
  let D := a+b+e+1
  let H := degree a b e dt
  have hq1 : 1 ≤ q := by omega
  have hD : 1 ≤ q^D := Nat.one_le_pow _ _ hq1
  have hA : q^a ≤ q^D := Nat.pow_le_pow_right hq1 (by dsimp [D];omega)
  have hB : q^b ≤ q^D := Nat.pow_le_pow_right hq1 (by dsimp [D];omega)
  have hE : q^e ≤ q^D := Nat.pow_le_pow_right hq1 (by dsimp [D];omega)
  have hxD := hx.trans hA
  have hpD := hp.trans hB
  have hwD := hword.trans hE
  have hpMul := Nat.mul_le_mul_right p hpD
  have hpacketD : packet ≤ (1+p)*q^D := by nlinarith
  have hw1 : word+1 ≤ 2*q^D := by omega
  have ht : ct*(word+1)^dt ≤ ct*2^dt*q^(D*dt) := by
    calc
      _  ≤  ct*(2*q^D)^dt := Nat.mul_le_mul_left ct (Nat.pow_le_pow_left hw1 dt)
      _ = _ := by rw [mul_pow,←pow_mul];ring
  have hDH : q^D ≤ q^H := Nat.pow_le_pow_right hq1 (by dsimp [D,H,degree];nlinarith)
  have htH : q^(D*dt) ≤ q^H := Nat.pow_le_pow_right hq1 (by dsimp [D,H,degree];nlinarith)
  have hT := ht.trans (Nat.mul_le_mul_left (ct*2^dt) htH)
  have hH : 1 ≤ q^H := Nat.one_le_pow _ _ hq1
  have hpH := hpD.trans hDH
  have hwH := hwD.trans hDH
  have heH := hE.trans hDH
  have hpacketH := hpacketD.trans (Nat.mul_le_mul_left (1+p) hDH)
  have htOut := Nat.mul_le_mul_right t hT
  have hr : tp+2*packet+2+q^e+2*word+2+ct*(word+1)^dt ≤
      coefficient p t ct dt*q^H := by
    unfold coefficient
    nlinarith
  have ho : out ≤ coefficient p t ct dt*q^H := by
    have ho0 : out ≤ (1+ct*2^dt*t)*q^H := by
      calc
        out ≤ word+ct*(word+1)^dt*t := hout
        _ ≤ q^H+ct*2^dt*q^H*t := Nat.add_le_add hwH htOut
        _ = _ := by ring
    have hc : 1+ct*2^dt*t ≤ coefficient p t ct dt := by
      simp only [coefficient, Nat.mul_add, Nat.mul_one]
      omega
    exact ho0.trans (Nat.mul_le_mul_right (q^H) hc)
  have habs := V39UniformResource.seed_envelope_le_power (coefficient p t ct dt) H q
    (coefficient p t ct dt*q^H) hq le_rfl
  have hf : coefficient p t ct dt*q^H ≤ q^(exponent p t ct dt a b e) := by
    change coefficient p t ct dt*q^H ≤ q^(V39UniformResource.seedExponent (coefficient p t ct dt) H)
    omega
  exact ⟨hr.trans hf,ho.trans hf⟩

#print axioms bound
end CurrentAdditive.V40PipelineScalar
