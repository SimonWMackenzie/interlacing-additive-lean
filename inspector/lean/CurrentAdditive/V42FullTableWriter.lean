import CurrentAdditive.V42FullTableScale
import CurrentAdditive.V39WTablePublicClock

set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 16384
namespace V42FullTableClock
noncomputable section
open Paper2 EthInapproximability.CurrentPaper
open CurrentAdditive V42RuntimeSchedule
open V39WTablePublicClock
attribute [local irreducible] V39RLoop.bodyCoefficient UnaryBinaryEncoding.coefficient

/- Arithmetic values and their identities only. No clock or execution
proposition is hidden in this datum. -/
private opaque fixedArithmeticData :
    {v : ℕ × ℕ // v.1=V39WTablePrepare.N ∧ v.2=UnaryBinaryEncoding.coefficient} :=
  ⟨(V39WTablePrepare.N,UnaryBinaryEncoding.coefficient),rfl,rfl⟩
def prepCount : ℕ := fixedArithmeticData.val.1
def headerCoefficient : ℕ := 12*fixedArithmeticData.val.2+100
theorem prepCount_eq : prepCount=V39WTablePrepare.N := fixedArithmeticData.property.1
theorem headerCoefficient_eq : headerCoefficient=12*UnaryBinaryEncoding.coefficient+100 := by
  rw [headerCoefficient,fixedArithmeticData.property.2]
def tableCoefficient : ℕ := 10000*(prepCount+1)*(headerCoefficient+1)
def tableExponent : ℕ := tableCoefficient+5*coreExponent

/-- A fixed polynomial bound for the literal writer clock. All hypotheses
bound public arithmetic formulas, not execution times or maxima over runs. -/
theorem whole_polynomial (g : EncodedGraph.Graph) (p s q₁ q₂ w Q r k m thr Z : ℕ)
    (hZ : 1 ≤ Z)
    (hscale : V39RLoop.publicScale g p s q₁ q₂ w Q r k ≤ graphSize g*Z)
    (hsyn : V39RLoop.syntaxCap g.vertices p s q₁ q₂ w Q k ≤ Z)
    (hlab : V39RLoop.labelCap g.vertices p s q₁ q₂ w Q k ≤ Z)
    (hm : m ≤ Z) (hthr : thr ≤ Z)
    (hcore : V39RLoop.publicCoreClock g p s q₁ q₂ w Q r k ≤ (graphSize g)^11*Z) :
    wholeClock g p s q₁ q₂ w Q r k m thr ≤ tableCoefficient*(graphSize g)^11*Z^5 := by
  let V := (graphSize g)^11
  let A := V*Z^5
  have hG : 1 ≤ graphSize g := by unfold graphSize; omega
  have hV : 1 ≤ V := one_le_pow₀ hG
  have hGV : graphSize g ≤ V := by
    simpa [V] using (Nat.pow_le_pow_right hG (show 1 ≤ 11 by decide))
  have hZZ2 : Z ≤ Z^2 := by simpa using (Nat.pow_le_pow_right hZ (show 1 ≤ 2 by decide))
  have hZZ3 : Z ≤ Z^3 := by simpa using (Nat.pow_le_pow_right hZ (show 1 ≤ 3 by decide))
  have hZZ5 : Z ≤ Z^5 := by simpa using (Nat.pow_le_pow_right hZ (show 1 ≤ 5 by decide))
  have hZ25 : Z^2 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have hZA : Z^5 ≤ A := Nat.le_mul_of_pos_left _ (by omega)
  have hA : 1 ≤ A := (hZ.trans hZZ5).trans hZA
  have hZ3V : Z^3 ≤ V*Z^3 := Nat.le_mul_of_pos_left _ (by omega)
  have hfetch : fetchSize m (V39RLoop.labelCap g.vertices p s q₁ q₂ w Q k) ≤ 6*Z^2 := by
    have hprod := Nat.mul_le_mul hm hlab
    unfold fetchSize
    nlinarith only [hprod,hm,hZZ2,hZ]
  have hsf : V39RLoop.syntaxCap g.vertices p s q₁ q₂ w Q k *
      fetchSize m (V39RLoop.labelCap g.vertices p s q₁ q₂ w Q k) ≤ 6*Z^3 := by
    have h := Nat.mul_le_mul hsyn hfetch
    convert h using 1 <;> ring
  have hcore3 : V39RLoop.publicCoreClock g p s q₁ q₂ w Q r k ≤ V*Z^3 :=
    hcore.trans (Nat.mul_le_mul_left V hZZ3)
  have hentry : entryClock g p s q₁ q₂ w Q r k m ≤ 1024*(V*Z^3) := by
    have h140 := Nat.mul_le_mul_left 140 hsf
    have hZ3 : Z ≤ V*Z^3 := hZZ3.trans hZ3V
    unfold entryClock
    omega
  have hm2 : m^2 ≤ Z^2 := Nat.pow_le_pow_left hm 2
  have hprod : m^2*entryClock g p s q₁ q₂ w Q r k m ≤ 1024*A := by
    have h := Nat.mul_le_mul hm2 hentry
    convert h using 1 <;> dsimp [A] <;> ring
  have hmA : m ≤ A := hm.trans (hZZ5.trans hZA)
  have hm2A : m^2 ≤ A := hm2.trans (hZ25.trans hZA)
  have hwriter : MatrixTableWriter.writerBound m m (entryClock g p s q₁ q₂ w Q r k m) ≤ 2048*A := by
    have he : MatrixTableWriter.writerBound m m (entryClock g p s q₁ q₂ w Q r k m)=
        m^2*entryClock g p s q₁ q₂ w Q r k m+6*m^2+8*m+5 := by
      unfold MatrixTableWriter.writerBound; ring
    rw [he]
    omega
  have hsource : sourceLength g p s q₁ q₂ w Q r k m ≤ 4*A := by
    have hprod := Nat.mul_le_mul hm hlab
    have hGZ : graphSize g*Z ≤ A := Nat.mul_le_mul hGV hZZ5
    have hZ2A := hZ25.trans hZA
    have hscaleA := hscale.trans hGZ
    have hprodA : m*V39RLoop.labelCap g.vertices p s q₁ q₂ w Q k ≤ A :=
      hprod.trans (by simpa only [pow_two] using hZ2A)
    unfold sourceLength
    nlinarith only [hscaleA,hmA,hprodA]
  have hprep : V39WTablePrepare.N*(2*sourceLength g p s q₁ q₂ w Q r k m+3)+3 ≤
      (11*V39WTablePrepare.N+3)*A := by
    have hinner : 2*sourceLength g p s q₁ q₂ w Q r k m+3 ≤ 11*A := by omega
    have h := Nat.mul_le_mul_left V39WTablePrepare.N hinner
    nlinarith only [h,hA]
  have hhead : headerClock m thr ≤ 9*headerCoefficient*A := by
    have hmthr : m+thr+1 ≤ 3*Z := by omega
    have hsq := Nat.pow_le_pow_left hmthr 2
    have hp := Nat.mul_le_mul_left headerCoefficient hsq
    have hZ2A := hZ25.trans hZA
    have hp' := Nat.mul_le_mul_left (9*headerCoefficient) hZ2A
    unfold headerClock
    rw [←headerCoefficient_eq]
    nlinarith only [hp,hp']
  have hC : 11*V39WTablePrepare.N+9*headerCoefficient+2053 ≤ tableCoefficient := by
    rw [←prepCount_eq]
    unfold tableCoefficient
    nlinarith [Nat.zero_le (prepCount*headerCoefficient)]
  have hmul := Nat.mul_le_mul_right A hC
  change _ ≤ tableCoefficient*V*Z^5
  rw [Nat.mul_assoc]
  change _ ≤ tableCoefficient*A
  unfold wholeClock
  nlinarith only [hprep,hwriter,hhead,hA,hmul]



theorem whole_full (g : EncodedGraph.Graph) (c δv ζ : ℚ) (L k : ℕ)
    (hn : g.vertices ≤ 2^L) (ht : FullTests c L g.edges.length δv ζ) :
    wholeClock g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L) (fullW L) (fullQ L)
      (fullRepeat L g.edges.length) k (sampleSide L k) (V42RuntimeSchedule.B L k) ≤
      (graphSize g)^11*2^(tableExponent*T L k) := by
  let Z := 2^(coreExponent*T L k)
  have hT : 1 ≤ T L k := by have hL := ht.1.2.2.1; unfold T; nlinarith
  have hC : 11264 ≤ coreExponent := by unfold coreExponent; omega
  have hscale := (public_scale_full g c δv ζ L k hn ht).trans
    (Nat.mul_le_mul_left (graphSize g) (Nat.pow_le_pow_right (by decide)
      (show 1024*T L k ≤ coreExponent*T L k by nlinarith)))
  have hsyn := (syntax_cap_full g.vertices L k ht.2 hn).trans
    (Nat.pow_le_pow_right (by decide) (show 512*T L k ≤ coreExponent*T L k by nlinarith))
  have hlab := (label_cap_full g.vertices L k ht.2 hn).trans
    (Nat.pow_le_pow_right (by decide) (show 128*T L k ≤ coreExponent*T L k by nlinarith))
  have hm := (full_sampleSide_le_pow L k ht.2).trans
    (Nat.pow_le_pow_right (by decide) (show fullSampleExponent L k ≤ coreExponent*T L k by
      simpa only [fullSampleExponent,T,Nat.mul_assoc] using
        (Nat.mul_le_mul_right (T L k) (show 40 ≤ coreExponent by omega))))
  have hb0 := CurrentAdditive.V42PublicSize.budget_linear L k (CurrentAdditive.V42PublicCutoff.full_cutoff_bounds 0 L ht.2).2.2.1 (CurrentAdditive.V42PublicCutoff.full_cutoff_bounds 0 L ht.2).2.2.2.1
  have hb : V42RuntimeSchedule.B L k ≤ Z := hb0.trans
    (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by unfold T at *; nlinarith)))
  have hwhole := whole_polynomial g (seedWidth L) (fullS L) (fullQ₁ L) (fullQ₂ L)
    (fullW L) (fullQ L) (fullRepeat L g.edges.length) k (sampleSide L k) (V42RuntimeSchedule.B L k)
    Z Nat.one_le_two_pow hscale hsyn hlab hm hb (public_core_full g c δv ζ L k hn ht)
  have hcoef : tableCoefficient ≤ 2^(tableCoefficient*T L k) := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by nlinarith))
  apply hwhole.trans
  calc
    tableCoefficient*(graphSize g)^11*Z^5 ≤ 2^(tableCoefficient*T L k)*(graphSize g)^11*Z^5 := by gcongr
    _=(graphSize g)^11*2^(tableExponent*T L k) := by
      dsimp [Z,tableExponent]
      rw [←pow_mul]
      rw [Nat.mul_comm (2^(tableCoefficient*T L k)) ((graphSize g)^11),Nat.mul_assoc,←pow_add]
      congr 2
      ring

#print axioms whole_polynomial
#print axioms whole_full
end
end V42FullTableClock



