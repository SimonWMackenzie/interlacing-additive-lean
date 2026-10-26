import CurrentAdditive.GaussWholeStepProgram
import CurrentAdditive.GaussPivotPrepClock
import CurrentAdditive.GaussInitialByteDimensions
import CurrentAdditive.GaussCellPolynomialClock

namespace CurrentAdditive.GaussWholeStepSizeCaps
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussSearchGridInvoke (Bank low frame)
open GaussWholeStepProgram
open GaussCellPolynomialClock

def frontCap (n : Nat) : Nat := GaussPivotPrepClock.polynomialClock n+
  GaussSearchRuntime.polynomialClock n+40*(n+1)
def pushConstant : Nat := BitMachineStackGrowth.perStep program
def bankCap (n t : Nat) : Nat := n+pushConstant*t
def packetCap (n : Nat) : Nat := 8*n+4
def rewriteCap (n : Nat) : Nat :=
  2*packetCap n+2+n+2+
    MinimumRatioContext.MachineInvokeFull.uniformBound GaussSearchGridInvoke.M
      (List.replicate (packetCap n) true)
      (GaussGridInputPolynomial.gridPolynomialClock (packetCap n))+2

theorem state_sizes {m k : Nat} (s : GaussControlTrace.State m k) :
    s.r≤(GaussControlTrace.statePacket s).length ∧
    s.c≤(GaussControlTrace.statePacket s).length ∧
    m≤(GaussControlTrace.statePacket s).length := by
  have he:=GaussControlTrace.statePacket_length s
  have hm:=GaussInitialByteDimensions.rows_le_initial_bytes s.B
  omega

theorem front_clock_le {m k : Nat} (s : GaussControlTrace.State m k) :
    GaussPreparedGuard64.clock s+GaussGuardedFront64.activeClock s+2≤
      frontCap (GaussControlTrace.statePacket s).length := by
  have hp:=GaussPivotPrepClock.clock_le_polynomial s
  have hs:=state_sizes s
  have hm : max s.r m≤(GaussControlTrace.statePacket s).length := max_le hs.1 hs.2.2
  change GaussPivotPrepRun.clock s≤GaussPivotPrepClock.polynomialClock
    (GaussControlTrace.statePacket s).length at hp
  unfold GaussPreparedGuard64.clock GaussGuardedFront64.activeClock
    GaussPivotGuardRun.clock frontCap
  omega

theorem initial_length (word : List Bool) (j : Bank) :
    ((initial word).stk j).length≤word.length := by
  simp only [initial,rawInit]
  split_ifs <;> simp

/-- Every dirty register of the actual fixed whole-step program is charged
by its execution prefix, including registers not named by a local interface. -/
theorem run_bank_length (word : List Bool) (t : Nat) (j : Bank) :
    ((run t (initial word)).stk j).length≤bankCap word.length t := by
  exact (BitMachineStackGrowth.run_growth program (initial word) t j).trans
    (Nat.add_le_add_right (initial_length word j) _)

theorem packet_length (S : Fin 64 → List Bool) (n : Nat)
    (hS : ∀j,(S j).length≤n) :
    (GaussSearchGridInput64.packet S).length≤packetCap n := by
  rw [GaussSearchGridInput64.packet,BitMachineBankCodec.encode_length]
  have hs : (∑i : Fin 4,(GaussSearchGridInput64.words S i).length)≤4*n := by
    calc
      _ ≤ ∑_i : Fin 4,n := Finset.sum_le_sum (fun i _ => hS _)
      _ =4*n := by simp
  unfold packetCap
  omega

theorem rewrite_clock_le (S : Fin 64 → List Bool) (n : Nat)
    (hS : ∀j,(S j).length≤n) : GaussSearchGridInvoke.clock S≤rewriteCap n := by
  have hp:=packet_length S n hS
  have hg : GaussGridInputPolynomial.gridPolynomialClock
      (GaussSearchGridInput64.packet S).length≤
      GaussGridInputPolynomial.gridPolynomialClock (packetCap n) := by
    unfold GaussGridInputPolynomial.gridPolynomialClock
    gcongr
  unfold GaussSearchGridInvoke.clock rewriteCap
    MinimumRatioContext.MachineInvokeFull.uniformBound
  simp only [List.length_replicate]
  gcongr
  exact hS 22

theorem front_polynomial : PolynomialBound (fun _ n => frontCap n) := by
  unfold frontCap GaussPivotPrepClock.polynomialClock
    GaussStateRowCount.polynomialClock GaussRowCount.polynomialClock
    GaussRowCount.itemEnvelope GaussSearchRuntime.polynomialClock
  dsimp only
  repeat first
    | exact constant _
    | exact second
    | apply add
    | apply mul
    | apply power

theorem packet_polynomial : PolynomialBound (fun _ n => packetCap n) :=
  add (mul (constant 8) second) (constant 4)

theorem rewrite_polynomial : PolynomialBound (fun _ n => rewriteCap n) := by
  have hg : PolynomialBound (fun _ n => GaussGridInputPolynomial.gridPolynomialClock
      (packetCap n)) := by
    unfold GaussGridInputPolynomial.gridPolynomialClock
    exact mul (constant _) (power (add packet_polynomial (constant 1)) _)
  have hi:=uniform_invocation GaussSearchGridInvoke.M packet_polynomial hg
  exact add (add (add (add (add (mul (constant 2) packet_polynomial)
    (constant 2)) second) (constant 2)) hi) (constant 2)

theorem polynomial_compose {f : Nat → Nat} {g : Nat → Nat → Nat}
    (hf : PolynomialBound (fun _ n => f n)) (hg : PolynomialBound g) :
    PolynomialBound (fun s n => f (g s n)) := by
  obtain ⟨C,d,hf⟩:=hf
  apply mono (mul (constant C) (power (add hg (constant 1)) d))
  intro s n
  simpa only [Nat.zero_add] using hf 0 (g s n)

#print axioms front_clock_le
#print axioms run_bank_length
#print axioms rewrite_clock_le
#print axioms front_polynomial
#print axioms rewrite_polynomial
end
end CurrentAdditive.GaussWholeStepSizeCaps
