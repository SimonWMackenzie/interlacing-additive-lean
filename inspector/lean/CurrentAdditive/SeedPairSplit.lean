import EthInapproximability.CurrentPaper.SamplerMachineFactorSplit

/-! Physical splitting of one fixed-width pair counter. The low `d` bits
encode the inner y label, while the high `d` bits encode the outer x label.
The old factor-split controller copies both halves and restores the counter;
its nonconstant flags are incidental here. -/

namespace CurrentAdditive.FiniteFieldMachine.SeedPairSplit

open EthInapproximability.CurrentPaper.SamplerMachineFactorSplit

theorem split_counter_pair (d : ℕ) (q : List Bool)
    (hq : q.length = 2 * d) :
    let y := q.take d
    let x := q.drop d
    run (4 * d + 4)
      (cfg (some .scanU) (flags false false)
        (List.replicate d true) q [] [] [] []) =
      cfg none (flags (y.tail.any id) (x.tail.any id))
        (List.replicate d true) q y x [] [] := by
  intro y x
  have hy : y.length = d := by
    simp [y, List.length_take, hq]
    omega
  have hx : x.length = d := by
    simp [x, List.length_drop, hq]
    omega
  have hq' : q = y ++ x := (List.take_append_drop d q).symm
  have hcy : (List.replicate d true).length = y.length := by simpa using hy.symm
  have hcx : (List.replicate d true).length = x.length := by simpa using hx.symm
  simpa only [hq', List.length_replicate, hy, hx] using
    split_run (List.replicate d true) y x hcy hcx

#print axioms split_counter_pair

end CurrentAdditive.FiniteFieldMachine.SeedPairSplit
