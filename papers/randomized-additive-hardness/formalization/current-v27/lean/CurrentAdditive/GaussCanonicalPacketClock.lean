import CurrentAdditive.GaussCanonicalFieldClock

namespace CurrentAdditive.GaussCanonicalFieldClock
noncomputable section
open EthInapproximability.CurrentPaper
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

/-- The next packet is an actually charged term of the pivot byte bound. -/
theorem nextPacket_pivot_linear {m k : Nat} (s : GaussControlTrace.State m k)
    (hr : s.r < m) (hc : s.c < k) (pivot : Fin m)
    (hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩ = some pivot)
    (hcount : s.r = s.pivots.length) :
    (GaussControlTrace.statePacket (GaussControlTrace.step s)).length ≤
      200*((GaussControlTrace.statePacket s).length+
        (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B).length+1) := by
  let ps' := s.pivots ++ [(⟨s.r,hr⟩,⟨s.c,hc⟩)]
  let successor : GaussControlTrace.State m k :=
    ⟨(GaussControlTrace.step s).B,ps'.length,s.c+1,ps'⟩
  have hs : successor = GaussControlTrace.step s := by
    have hlen : ps'.length = s.r+1 := by simp [ps',hcount]
    dsimp only [successor]
    rw [hlen]
    simp [ps',GaussControlTrace.step,hr,hc,hp]
  have hterm : (GaussControlTrace.statePacket successor).length ≤
      GaussPivotByteSize32.byteCharge s
        (foreign [true] (GaussPhysical.encodeTypedMatrix (GaussControlTrace.step s).B)) hr hc := by
    dsimp only [GaussPivotByteSize32.byteCharge,successor,ps']
    omega
  rw [hs] at hterm
  exact hterm.trans (byteCharge_canonical_linear s hr hc hcount)

end
#print axioms nextPacket_pivot_linear
end CurrentAdditive.GaussCanonicalFieldClock
