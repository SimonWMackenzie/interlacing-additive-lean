import CurrentAdditive.V39EntryPublicClock
import CurrentAdditive.V22RepeatArithmetic
import CurrentAdditive.V42RuntimeSchedule

/-! Literal full-schedule envelopes for the already checked current entry
evaluator. Encoded graph bytes remain an explicit polynomial factor. -/
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V42FullTableClock
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open GeneratorCode GeneratorSerialization GeneratorSource RecursiveLabelCodecScratch RecursiveEntries
open CurrentAdditive V42RuntimeSchedule

def T (L k : ℕ) := (k+1)*L
def fullRepeat (L m : ℕ) := V22RepeatArithmetic.repetitions (fullQ₂ L) (fullS L) m
def graphSize (g : EncodedGraph.Graph) := (EncodedGraph.encode g).length+1

theorem full_edge_repeat_le (c δv ζ : ℚ) (L m : ℕ)
    (ht : FullTests c L m δv ζ) : m ≤ fullQ₂ L ∧ fullRepeat L m ≤ fullQ₂ L := by
  have hs : 1 ≤ fullS L := by have h := fullS_ge_256 L; omega
  have hm : m ≤ 4*fullS L*m := by nlinarith
  have hq : V38Schedule.pow2Ceil (4*fullS L*m) ≤ fullQ₂ L := by
    simpa only [fullQ₂_eq_old] using ht.1.1.2.2.1
  exact ⟨(hm.trans (Nat.le_pow_clog (by decide) _)).trans hq,Nat.div_le_self _ _⟩

theorem syntax_cap_full (n L k : ℕ) (hL : CurrentAdditive.V42PublicCutoff.fullLengthCutoff 0 ≤ L) (hn : n ≤ 2^L) :
    V39RLoop.syntaxCap n (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
      (fullW L) (fullQ L) k ≤ 2^(512*T L k) := by
  have hL16 : 16 ≤ L := (CurrentAdditive.V42PublicCutoff.full_cutoff_bounds 0 L hL).2.1
  let M := 2^fullWidthExponent L
  obtain ⟨hnM,hp,hq1,hq2,hs,hw,hQ⟩ := full_widths_le_pow n L hn hL
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hscale : GeneratorSize.scale n (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
      (fullW L) (fullQ L) ≤ 2^(fullWidthExponent L+10) := by
    have hsum : GeneratorSize.scale n (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
        (fullW L) (fullQ L) ≤ 1024*M := by unfold GeneratorSize.scale; change n ≤ M at hnM; omega
    calc
      _ ≤ 1024*M := hsum
      _=2^(fullWidthExponent L+10) := by dsimp [M]; rw [pow_add]; norm_num; ring
  calc
    _ ≤ (2^(fullWidthExponent L+10))^(9*(k+2)) := Nat.pow_le_pow_left hscale _
    _=2^((fullWidthExponent L+10)*(9*(k+2))) := by rw [←pow_mul]
    _ ≤ 2^(512*T L k) := Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent T; nlinarith)

theorem label_base_full (n L : ℕ) (hL : CurrentAdditive.V42PublicCutoff.fullLengthCutoff 0 ≤ L) (hn : n ≤ 2^L) :
    V39RLoop.labelBase n (seedWidth L) (fullS L) ≤ 2^(17*L) := by
  have hL16 : 16 ≤ L := (CurrentAdditive.V42PublicCutoff.full_cutoff_bounds 0 L hL).2.1
  let M := 2^fullWidthExponent L
  obtain ⟨hnM,hp,_,_,hs,_,_⟩ := full_widths_le_pow n L hn hL
  have hM : 1 ≤ M := Nat.one_le_two_pow
  have hb : V39RLoop.labelBase n (seedWidth L) (fullS L) ≤ 8*M := by
    unfold V39RLoop.labelBase
    simp only [piCodec_maxLen,boolCodec,Nat.mul_one,default_item_maxLen]
    change max 1 (max (seedWidth L) (max (seedWidth L) (4*fullS L+(1+max n (fullS L-3))))) ≤ _
    change n ≤ M at hnM
    omega
  calc
    _ ≤ 8*M := hb
    _=2^(fullWidthExponent L+3) := by dsimp [M]; rw [pow_add]; norm_num; ring
    _ ≤ 2^(17*L) := Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)

theorem label_cap_full (n L k : ℕ) (hL : CurrentAdditive.V42PublicCutoff.fullLengthCutoff 0 ≤ L) (hn : n ≤ 2^L) :
    V39RLoop.labelCap n (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
      (fullW L) (fullQ L) k ≤ 2^(128*T L k) := by
  have hL16 : 16 ≤ L := (CurrentAdditive.V42PublicCutoff.full_cutoff_bounds 0 L hL).2.1
  let M := 2^fullWidthExponent L
  obtain ⟨_,_,hq1,hq2,hs,hw,hQ⟩ := full_widths_le_pow n L hn hL
  have hb := label_base_full n L hL hn
  have ht := labelStepCap_le_cube (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L)
    M Nat.one_le_two_pow hs hq1 hq2 hw hQ
  have ht' : labelStepCap (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L) ≤ 2^(49*L) := by
    calc
      _ ≤ 32*M^3 := ht
      _=2^(3*fullWidthExponent L+5) := by dsimp [M]; rw [←pow_mul,pow_add]; norm_num; ring
      _ ≤ 2^(49*L) := Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent; omega)
  calc
    _ ≤ 2^(17*L)*(2^(49*L))^(k+1) := Nat.mul_le_mul hb (Nat.pow_le_pow_left ht' _)
    _=2^(17*L+49*L*(k+1)) := by rw [←pow_mul,←pow_add]
    _ ≤ 2^(128*T L k) := Nat.pow_le_pow_right (by decide) (by unfold T; nlinarith)

def scheduledScale (g : EncodedGraph.Graph) (L k : ℕ) :=
  V39RLoop.publicScale g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
    (fullW L) (fullQ L) (fullRepeat L g.edges.length) k

theorem public_scale_full (g : EncodedGraph.Graph) (c δv ζ : ℚ) (L k : ℕ)
    (hn : g.vertices ≤ 2^L) (ht : FullTests c L g.edges.length δv ζ) :
    scheduledScale g L k ≤ graphSize g*2^(1024*T L k) := by
  let M := 2^fullWidthExponent L
  let Z := 2^(512*T L k)
  have hL : 16 ≤ L := ht.1.2.2.1
  have hT : 16 ≤ T L k := by unfold T; nlinarith
  obtain ⟨hnM,hp,hq1,hq2,hs,hw,hQ⟩ := full_widths_le_pow g.vertices L hn ht.2
  obtain ⟨he,hr⟩ := full_edge_repeat_le c δv ζ L g.edges.length ht
  have heM : g.edges.length ≤ M := he.trans hq2
  have hrM : fullRepeat L g.edges.length ≤ M := hr.trans hq2
  have hMZ : M ≤ Z := Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent T; nlinarith)
  have hM2Z : M^2 ≤ Z := by
    calc
      M^2=2^(2*fullWidthExponent L) := by dsimp [M]; rw [←pow_mul]; congr 1; ring
      _ ≤ Z := Nat.pow_le_pow_right (by decide) (by unfold fullWidthExponent T; nlinarith)
  have hkT : k ≤ T L k := by unfold T; nlinarith
  have hkZ : k ≤ Z := (hkT.trans Nat.lt_two_pow_self.le).trans
    (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have hZ : 1 ≤ Z := Nat.one_le_two_pow
  have hconstant : 1048576 ≤ Z := by
    change 2^20 ≤ Z
    exact Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hsyn := syntax_cap_full g.vertices L k ht.2 hn
  have hlab := (label_cap_full g.vertices L k ht.2 hn).trans
    (Nat.pow_le_pow_right (by decide) (show 128*T L k ≤ 512*T L k by omega))
  have hscalar : V39RLoop.scalarSum g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
      (fullW L) (fullQ L) (fullRepeat L g.edges.length) k ≤ 29*Z := by
    unfold V39RLoop.scalarSum
    change g.vertices ≤ M at hnM
    omega
  have hedge : g.edges.length*g.vertices ≤ Z :=
    (Nat.mul_le_mul heM hnM).trans (by simpa [pow_two] using hM2Z)
  have hedge2 : 2*g.edges.length*g.vertices ≤ 2*Z := by nlinarith
  have hG : 1 ≤ graphSize g := by unfold graphSize; omega
  have hGZ : Z ≤ graphSize g*Z := Nat.le_mul_of_pos_left _ (by omega)
  have hGG : graphSize g ≤ graphSize g*Z := Nat.le_mul_of_pos_right _ (by omega)
  have hbound : scheduledScale g L k ≤ 128*(graphSize g*Z) := by
    unfold scheduledScale V39RLoop.publicScale
    change _+3*graphSize g+_+_+_ ≤ _
    omega
  apply hbound.trans
  calc
    128*(graphSize g*Z)=graphSize g*2^(512*T L k+7) := by dsimp [Z]; rw [pow_add]; norm_num; ring
    _ ≤ graphSize g*2^(1024*T L k) := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by decide) (by nlinarith))

def coreExponent : ℕ := V39RLoop.bodyCoefficient+10000+11264

theorem public_core_full (g : EncodedGraph.Graph) (c δv ζ : ℚ) (L k : ℕ)
    (hn : g.vertices ≤ 2^L) (ht : FullTests c L g.edges.length δv ζ) :
    V39RLoop.publicCoreClock g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
      (fullW L) (fullQ L) (fullRepeat L g.edges.length) k ≤
      (graphSize g)^11*2^(coreExponent*T L k) := by
  let C := V39RLoop.bodyCoefficient+10000
  have hT : 1 ≤ T L k := by have hL := ht.1.2.2.1; unfold T; nlinarith
  have hC : C ≤ 2^(C*T L k) := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by nlinarith))
  have hs := public_scale_full g c δv ζ L k hn ht
  unfold V39RLoop.publicCoreClock
  calc
    _ ≤ 2^(C*T L k)*(graphSize g*2^(1024*T L k))^11 :=
      Nat.mul_le_mul hC (Nat.pow_le_pow_left hs 11)
    _=(graphSize g)^11*2^(coreExponent*T L k) := by
      rw [mul_pow,←pow_mul]
      dsimp [coreExponent,C]
      rw [←mul_assoc]
      conv_lhs => rw [Nat.mul_comm (2^((V39RLoop.bodyCoefficient+10000)*T L k)) ((graphSize g)^11)]
      rw [Nat.mul_assoc,←pow_add]
      congr 2
      ring

#print axioms full_edge_repeat_le
#print axioms syntax_cap_full
#print axioms label_cap_full
#print axioms public_scale_full
#print axioms public_core_full
end
end V42FullTableClock


