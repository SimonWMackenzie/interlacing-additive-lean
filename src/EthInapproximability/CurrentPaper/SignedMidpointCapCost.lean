import EthInapproximability.CurrentPaper.SignedMidpointCapOR

/-!
# Aggregate midpoint-callback cost without exponentiating the branch count

The source-list mapper must charge the sum of actual callback bounds. A
uniform per-packet size bound turns that sum into branch count times one
fixed quadratic; there is no polynomial applied to the total branch count.
-/

namespace EthInapproximability.CurrentPaper.SignedMidpointCapCost

open EncodedETHTail

theorem branchPacket_length (answer : List Bool → ℤ) (k : ℕ)
    (b : Branch) :
    (SignedMidpointCapPacket.branchPacket answer k b).length =
      2 * ((encodeInteger (answer b.table)).length + b.threshold + k) + 5 := by
  simp only [SignedMidpointCapPacket.branchPacket,
    SignedMidpointCapCompare.inputPacket, BitMachineBankCodec.encode_length]
  simp [SignedMidpointCapCompare.inputBank, Fin.sum_univ_five]

theorem branchPacket_length_le (answer : List Bool → ℤ) (k A Y : ℕ)
    (b : Branch)
    (hanswer : (encodeInteger (answer b.table)).length ≤ A)
    (hthreshold : b.threshold ≤ Y) :
    (SignedMidpointCapPacket.branchPacket answer k b).length ≤
      2 * (A + Y + k) + 5 := by
  rw [branchPacket_length]
  omega

theorem branchPacket_length_from_approximation
    (M : BitMachine.Machine) (answer : List Bool → ℤ) (c d k : ℕ)
    (happrox : ∀ table,
      M.OutputsWithin table (encodeInteger (answer table))
        (c*(table.length+1)^d)) (b : Branch) :
    (SignedMidpointCapPacket.branchPacket answer k b).length ≤
      2 * (b.table.length +
        c*(b.table.length+1)^d*M.pushBound + b.threshold + k) + 5 := by
  have hout := BitMachine.output_length_bound M (happrox b.table)
  rw [branchPacket_length]
  omega

theorem branchPacket_length_polytime
    (answer : List Bool → ℤ) (k : ℕ)
    (happrox : BitMachine.Polytime
      (fun table => encodeInteger (answer table))) :
    ∃ (M : BitMachine.Machine) (c d : ℕ), ∀ b : Branch,
      (SignedMidpointCapPacket.branchPacket answer k b).length ≤
        2 * (b.table.length +
          c*(b.table.length+1)^d*M.pushBound + b.threshold + k) + 5 := by
  obtain ⟨M,c,d,hM⟩ := happrox
  exact ⟨M,c,d,fun b =>
    branchPacket_length_from_approximation M answer c d k hM b⟩

theorem decisionTimeBound_mono {n m : ℕ} (h : n ≤ m) :
    SignedMidpointCapPacket.decisionTimeBound n ≤
      SignedMidpointCapPacket.decisionTimeBound m := by
  let p := SignedMidpointCapPacket.rawMachine.pushBound
  have hlin : n+1 ≤ m+1 := by omega
  have hsquare : (n+1)^2 ≤ (m+1)^2 := Nat.pow_le_pow_left hlin 2
  have hbase : 64*(n+1)^2+5 ≤ 64*(m+1)^2+5 := by omega
  have htimes :
      (64*(n+1)^2+5)*(1+20*p) ≤
        (64*(m+1)^2+5)*(1+20*p) :=
    Nat.mul_le_mul_right _ hbase
  have htail :
      160*(64*(n+1)^2+5)*p ≤
        160*(64*(m+1)^2+5)*p := by
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 160 hbase)
  change ((64*(n+1)^2+5)*(1+20*p)+15*(n+1))+
      16*(n+1)+160*(64*(n+1)^2+5)*p ≤
    ((64*(m+1)^2+5)*(1+20*p)+15*(m+1))+
      16*(m+1)+160*(64*(m+1)^2+5)*p
  omega

theorem itemWork_le_count (answer : List Bool → ℤ) (k L : ℕ)
    (branches : List Branch)
    (hpacket : ∀ b ∈ branches,
      (SignedMidpointCapPacket.branchPacket answer k b).length ≤ L) :
    SignedMidpointCapOR.itemWork answer k branches ≤
      branches.length * SignedMidpointCapPacket.decisionTimeBound L := by
  induction branches with
  | nil => simp [SignedMidpointCapOR.itemWork]
  | cons b rest ih =>
      have hb : (SignedMidpointCapPacket.branchPacket answer k b).length ≤ L :=
        hpacket b (by simp)
      have hr : ∀ x ∈ rest,
          (SignedMidpointCapPacket.branchPacket answer k x).length ≤ L := by
        intro x hx
        exact hpacket x (by simp [hx])
      have ht := decisionTimeBound_mono hb
      have hs := ih hr
      simp only [SignedMidpointCapOR.itemWork, List.map_cons, List.sum_cons,
        List.length_cons] at *
      rw [Nat.succ_mul]
      omega

theorem itemWork_le_approximation_bound
    (M : BitMachine.Machine) (answer : List Bool → ℤ)
    (c d k T Y : ℕ) (branches : List Branch)
    (happrox : ∀ table,
      M.OutputsWithin table (encodeInteger (answer table))
        (c*(table.length+1)^d))
    (htable : ∀ b ∈ branches, b.table.length ≤ T)
    (hthreshold : ∀ b ∈ branches, b.threshold ≤ Y) :
    SignedMidpointCapOR.itemWork answer k branches ≤
      branches.length * SignedMidpointCapPacket.decisionTimeBound
        (2*(T+c*(T+1)^d*M.pushBound+Y+k)+5) := by
  apply itemWork_le_count answer k _ branches
  intro b hb
  have hbase := branchPacket_length_from_approximation M answer c d k happrox b
  have hT := htable b hb
  have hY := hthreshold b hb
  have hpow : (b.table.length+1)^d ≤ (T+1)^d :=
    Nat.pow_le_pow_left (by omega) d
  have hwork := Nat.mul_le_mul_right M.pushBound
    (Nat.mul_le_mul_left c hpow)
  omega

theorem packetInputs_length (answer : List Bool → ℤ) (k L : ℕ)
    (branches : List Branch)
    (hpacket : ∀ b ∈ branches,
      (SignedMidpointCapPacket.branchPacket answer k b).length ≤ L) :
    (SignedMidpointCapOR.packetInputs answer k branches).length ≤
      3 * branches.length * (L+1) + 1 := by
  exact SourceListEncoding.encode_map_length_le branches
    (SignedMidpointCapPacket.branchPacket answer k) L hpacket

end EthInapproximability.CurrentPaper.SignedMidpointCapCost
