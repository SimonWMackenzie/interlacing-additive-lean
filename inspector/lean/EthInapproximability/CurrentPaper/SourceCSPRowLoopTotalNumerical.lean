import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalUniformOne
import EthInapproximability.CurrentPaper.SourceCSPRowCodecParser

/-!
# Input-derived numerical bounds for the total source-row loop

Successful parsing consumes a prefix, so its unread suffix never exceeds
the current raw suffix. All per-row transition bounds are monotone in the
two physical input lengths and can be charged against the original packet.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalNumerical

theorem parsed_suffix_le {q H : Nat} (input : List Bool)
    (bank : SourceCSPRowController.Bank q) (rest : List Bool)
    (hparse : SourceCSPRowController.readQueriesFrom (q := q) 0 input
        (fun _ => []) = some (bank, rest)) :
    (rest.drop H).length ≤ input.length := by
  have hs := SourceCSPRowCodecParser.parse_zero_sound input bank rest hparse
  have hlen := congrArg List.length hs.1
  simp only [List.length_append] at hlen
  simp only [List.length_drop]
  omega

theorem oneBound_mono (q H : Nat) (input input' cap cap' : List Bool)
    (hinput : input.length ≤ input'.length)
    (hcap : cap.length ≤ cap'.length) :
    SourceCSPRowLoopTotalUniformOne.oneBound q H input cap ≤
      SourceCSPRowLoopTotalUniformOne.oneBound q H input' cap' := by
  unfold SourceCSPRowLoopTotalUniformOne.oneBound
    SourceCSPRowLoopTotalUniformOne.resetBound
    SourceCSPRowLoopTotalUniformOne.pushConstant
    SourceCSPRowLoopTotalCombinedAll.totalBound
    SourceCSPRowLoopTotalCombinedAll.wordBound
    SourceCSPRowLoopTotalCombinedAll.parserBound
  gcongr

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalNumerical
