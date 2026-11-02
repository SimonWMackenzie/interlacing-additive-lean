import CurrentAdditive.V40WeightedSeed

namespace CurrentAdditive.V40WeightedSeedData
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper

def HasClock (A : Producer) : Prop :=
  ∃ C d : Nat, ∀ L, 2≤L → A.clock (List.replicate L true)≤C*(2^L+1)^d

theorem level_le_power (L : Nat) : L≤2^L := (Nat.lt_two_pow_self : L<2^L).le

private theorem add_seed_bound (S X P a : Nat) (hs : a≤S*P) (hp : X+1≤P) :
    16*X+2*X+2+a≤(S+20)*P := by nlinarith

theorem field_hasClock (A : Producer) (hA : HasClock A) : HasClock (field A) := by
  obtain ⟨C,d,h⟩ := hA
  refine ⟨C+2*(C*A.machine.pushBound+1)+4*(C*A.machine.pushBound+1),
    (d+1)*(1+1),?_⟩
  intro L hL
  have hc := h L hL
  have hi := level_le_power L
  have ho := BitMachine.output_length_bound A.machine (A.outputs (List.replicate L true))
  simp only [List.length_replicate] at ho
  have hout : (A.result (List.replicate L true)).length≤2^L+C*(2^L+1)^d*A.machine.pushBound :=
    ho.trans (Nat.add_le_add hi (Nat.mul_le_mul_right _ hc))
  have hb := BitMachineCompositionArithmetic.composition_time_bound (2^L) C d 4 1
    A.machine.pushBound (A.result (List.replicate L true)).length hout
  change A.clock (List.replicate L true)+2*(A.result (List.replicate L true)).length+2+
    (4*(A.result (List.replicate L true)).length+4)≤_
  simp only [pow_one] at hb
  omega

theorem concat_hasClock (A B : Producer) (hA : HasClock A) (hB : HasClock B) :
    HasClock (concat A B) := by
  obtain ⟨C,d,h⟩ := hA
  obtain ⟨D,e,k⟩ := hB
  refine ⟨10+C*(1+2*A.machine.pushBound)+D*(1+2*B.machine.pushBound),d+e+1,?_⟩
  intro L hL
  let p := (2^L+1)^(d+e+1)
  have hbase : 1≤2^L+1 := Nat.succ_le_succ (Nat.zero_le _)
  have hp : 1≤p := Nat.one_le_pow _ _ hbase
  have hpa : (2^L+1)^d≤p := Nat.pow_le_pow_right hbase (by omega)
  have hpb : (2^L+1)^e≤p := Nat.pow_le_pow_right hbase (by omega)
  have hpx : 2^L+1≤p := by
    simpa only [pow_one] using Nat.pow_le_pow_right hbase (show 1≤d+e+1 by omega)
  have hLx := level_le_power L
  have ha := h L hL
  have hb := k L hL
  have hla := BitMachine.output_length_bound A.machine (A.outputs (List.replicate L true))
  have hlb := BitMachine.output_length_bound B.machine (B.outputs (List.replicate L true))
  simp only [List.length_replicate] at hla hlb
  have hla' : (A.result (List.replicate L true)).length≤L+C*(2^L+1)^d*A.machine.pushBound :=
    hla.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ ha) L)
  have hlb' : (B.result (List.replicate L true)).length≤L+D*(2^L+1)^e*B.machine.pushBound :=
    hlb.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hb) L)
  have hma := Nat.mul_le_mul_left (C*(1+2*A.machine.pushBound)) hpa
  have hmb := Nat.mul_le_mul_left (D*(1+2*B.machine.pushBound)) hpb
  change 2*(List.replicate L true).length+2+1+A.clock (List.replicate L true)+1+
    B.clock (List.replicate L true)+2*(B.result (List.replicate L true)).length+2+
    2*(A.result (List.replicate L true)).length+2+1≤_
  simp only [List.length_replicate]
  change _≤(10+C*(1+2*A.machine.pushBound)+D*(1+2*B.machine.pushBound))*p
  nlinarith

theorem seed_clock_polynomial : ∃ C d : Nat, ∀ L, 2≤L →
    V40SeedCells.clock L≤C*(2^L+1)^d := by
  refine ⟨SeedT45.SeedClock.seedC+20,1536,?_⟩
  intro L hL
  have hn : 4≤2^L := by
    simpa using Nat.pow_le_pow_right (by omega : 1≤(2:Nat)) hL
  have hs := SeedT45.SeedClock.clock_poly (2^L) hn
  have hp : 2^L+1≤(2^L+1)^1536 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤2^L+1)
      (show 1≤1536 by omega)
  change 16*2^L+2*2^L+2+SeedT45.SeedClock.clockExpr (2^L)≤_
  exact add_seed_bound _ _ _ _ hs hp

theorem cells_hasClock : HasClock cells := by
  obtain ⟨C,d,h⟩ := seed_clock_polynomial
  exact ⟨C,d,by intro L hL;simpa only [cells,List.length_replicate] using h L hL⟩

theorem law_clock_polynomial (port : V40SeedCells.Port) (count : Nat → Nat)
    (hr : ∀ L, V40SeedCells.result port L=List.replicate (count L) true)
    (hp : ∀ L, 0<count L) :
    ∃ C d : Nat, ∀ L, 2≤L →
      V40SeedCells.clock L+2*count L+2+V40UniformLaw.clock (count L)≤C*(2^L+1)^d := by
  obtain ⟨A,a,ha⟩ := seed_clock_polynomial
  obtain ⟨B,b,hb⟩ := V40UniformLaw.clock_polynomial
  refine ⟨A+2*(A*(V40SeedCells.machine port).pushBound+1)+
    B*(A*(V40SeedCells.machine port).pushBound+1)^b,(a+1)*(b+1),?_⟩
  intro L hL
  have hs := ha L hL
  have hu := hb (count L) (hp L)
  have hruns := V40SeedCells.outputs port (List.replicate L true)
  simp only [List.length_replicate,hr] at hruns
  have ho := BitMachine.output_length_bound (V40SeedCells.machine port) hruns
  simp only [List.length_replicate] at ho
  have hl : count L≤2^L+A*(2^L+1)^a*(V40SeedCells.machine port).pushBound :=
    ho.trans (Nat.add_le_add (level_le_power L) (Nat.mul_le_mul_right _ hs))
  have hc := BitMachineCompositionArithmetic.composition_time_bound (2^L) A a B b
    (V40SeedCells.machine port).pushBound (count L) hl
  exact (Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add_right hs (2*count L)) 2) hu).trans hc

theorem rowLaw_hasClock : HasClock rowLaw := by
  obtain ⟨C,d,h⟩ := law_clock_polynomial .rows rows V40SeedCells.result_rows rows_pos
  exact ⟨C,d,by intro L hL;simpa only [rowLaw,List.length_replicate] using h L hL⟩

theorem columnLaw_hasClock : HasClock columnLaw := by
  obtain ⟨C,d,h⟩ := law_clock_polynomial .columns columns V40SeedCells.result_columns columns_pos
  exact ⟨C,d,by intro L hL;simpa only [columnLaw,List.length_replicate] using h L hL⟩

theorem clock_polynomial : ∃ C d : Nat, ∀ L, 2≤L → clock L≤C*(2^L+1)^d :=
  concat_hasClock _ _ (field_hasClock _ cells_hasClock)
    (concat_hasClock _ _ (field_hasClock _ rowLaw_hasClock) (field_hasClock _ columnLaw_hasClock))
end
end CurrentAdditive.V40WeightedSeedData

namespace CurrentAdditive.V40WeightedSeed
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper

private theorem context_bound (p C d L h a : Nat) (hL : L≤2^L)
    (ha : a≤C*(2^L+1)^d) :
    7*(2*(h+L)+2+2)+(1+4*p)*a≤
      (28+(1+4*p)*C)*(h+2^L+1)^(d+1) := by
  let q := h+2^L+1
  have hq : 1≤q := by dsimp [q];omega
  have hp : q≤q^(d+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hq (show 1≤d+1 by omega)
  have hd : (2^L+1)^d≤q^(d+1) :=
    (Nat.pow_le_pow_left (by dsimp [q];omega) d).trans (Nat.pow_le_pow_right hq (by omega))
  have ht := ha.trans (Nat.mul_le_mul_left C hd)
  have hm := Nat.mul_le_mul_left (1+4*p) ht
  dsimp only [q] at hp hm
  nlinarith

theorem clock_polynomial : ∃ C d : Nat, ∀ context : List Bool, ∀ L, 2≤L →
    clock context L≤C*(context.length+2^L+1)^d := by
  obtain ⟨C,d,h⟩ := V40WeightedSeedData.clock_polynomial
  refine ⟨28+(1+4*V40WeightedSeedData.machine.pushBound)*C,d+1,?_⟩
  intro context L hL
  have hb := context_bound V40WeightedSeedData.machine.pushBound C d L context.length
    (V40WeightedSeedData.clock L) (V40WeightedSeedData.level_le_power L) (h L hL)
  simpa only [clock,packet,V40LawPacket.packet_length,List.length_replicate] using hb

theorem outputs_polynomial : ∃ C d : Nat, ∀ context : List Bool, ∀ L, 2≤L →
    machine.OutputsWithin (packet context (List.replicate L true))
      (packet context (StoredWeightedState.encode (V39GeneratedConstruction.storedLookupSeed L)))
      (C*(context.length+2^L+1)^d) := by
  obtain ⟨C,d,h⟩ := clock_polynomial
  exact ⟨C,d,fun context L hL => BitMachine.outputsWithin_mono _ (outputs context L) (h context L hL)⟩

#print axioms outputs_polynomial
end
end CurrentAdditive.V40WeightedSeed
