import EthInapproximability.CurrentPaper.BitMachineBroadcast
import EthInapproximability.CurrentPaper.BitMachineBankCodec

/-! A literal destructive transfer between two fixed Boolean stacks. -/

namespace CurrentAdditive.CodeDBankTransferV2

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding

variable {K L V : Type*} [DecidableEq K]

def transferred (source target : K) (S : K → List Bool) : K → List Bool :=
  Function.update (Function.update S source []) target
    ((S source).reverse ++ S target)

theorem transfer_run
    (P : L → TM2.Stmt (fun _ : K => Bool) L (V × Option Bool))
    (source target : K) (h : source ≠ target) (scan next : L)
    (hp : P scan = BitMachineBroadcast.scanStep source target scan next)
    (v : V) (popped : Option Bool) (S : K → List Bool) :
    ((advance P)^[(S source).length+1])
      (⟨some scan, (v,popped), S⟩ : TM2.Cfg (fun _ : K => Bool) L (V × Option Bool)) =
      ⟨some next, (v,none), transferred source target S⟩ := by
  have hs := BitMachineBroadcast.scan_run P source target h scan next hp
    v popped (S source) (S target) S
  have hi : BitMachineBroadcast.contents source target S (S source) (S target) = S := by
    simp [BitMachineBroadcast.contents]
  rw [hi] at hs
  simpa only [BitMachineBroadcast.run, transferred, BitMachineBroadcast.contents] using hs

#print axioms transfer_run

end CurrentAdditive.CodeDBankTransferV2
