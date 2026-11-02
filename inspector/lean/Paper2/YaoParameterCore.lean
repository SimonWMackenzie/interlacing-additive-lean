import EthInapproximability.CurrentPaper.MatrixTemplateAddressSetup
import EthInapproximability.CurrentPaper.MatrixUnaryPower

/-! A checked physical arithmetic core for the exact Yao flat-tape
coordinates. This deliberately exposes the remaining scalar producer
boundary: the independent power runs and the multiply-add sequence have not
yet been wired into one controller. -/

namespace Paper2.YaoEntryParameters

set_option maxHeartbeats 1000000

open Turing
open EthInapproximability.CurrentPaper

def relativePayload (ell H K p : ℕ) : ℕ := ell * (H * K) + p

/-- This is an actual three-phase, twelve-stack finite-controller run,
specialized to Yao. Its inputs are the basic unary labels `l,z,g,p`, plus
the public unary scalars `Q=2^(t-1)`, `b`, and `W=H*(K+1)`. The `p` suffix
is a basic label, not a supplied desired relative address. The machine
physically produces both the relative payload offset and exact selector
offset, preserving all inputs and clearing the two scratch banks. -/
def physical_relative_and_selector (ell z g p Q H K b : ℕ) :=
  MatrixTemplateAddressSetup.setup_run
    ell (H * K) z Q g b false (List.replicate p true) []

theorem relative_payload_bank (ell H K p : ℕ) :
    List.replicate (ell * (H * K)) true ++ List.replicate p true =
      List.replicate (relativePayload ell H K p) true := by
  simp only [relativePayload, List.replicate_append_replicate]

theorem physical_relative_and_selector_polynomial (ell z g Q H K b : ℕ) :
    MatrixTemplateAddressSetup.bound
      ell (H * K) z Q g b ≤
      24 * (ell + H * K + z + Q + g + b + 1) ^ 3 :=
  MatrixTemplateAddressSetup.bound_polynomial _ _ _ _ _ _

/-- A separate four-stack fixed program physically expands the actual unary
width `b` to the exact payload count `H=2^b`; its exponent bank survives. -/
theorem physical_payload_count (b : ℕ) :
    ∃ steps ≤ 4 * 2 ^ b + 5 * b + 7,
      MatrixUnaryPower.run steps
        (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none)
          [] [] [] (List.replicate b true)) =
        MatrixUnaryPower.cfg none ((false,false),none)
          (List.replicate (2 ^ b) true) [] []
          (List.replicate b true) := MatrixUnaryPower.unary_power_run b

/-- The same independent power program generates the selector-coordinate
count `Q=2^(t-1)` from its unary exponent. A physical `t ↦ t-1` preprocessing
and wiring this output into the arithmetic controller remain outstanding. -/
theorem physical_selector_coordinate_count (t : ℕ) :
    ∃ steps ≤ 4 * 2 ^ (t - 1) + 5 * (t - 1) + 7,
      MatrixUnaryPower.run steps
        (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none)
          [] [] [] (List.replicate (t - 1) true)) =
        MatrixUnaryPower.cfg none ((false,false),none)
          (List.replicate (2 ^ (t - 1)) true) [] []
          (List.replicate (t - 1) true) := MatrixUnaryPower.unary_power_run _

/-- A second independent power run produces the actual `2^t` factor of
the payload stride from unary `t`, preserving that exponent. -/
theorem physical_t_power (t : ℕ) :
    ∃ steps ≤ 4 * 2 ^ t + 5 * t + 7,
      MatrixUnaryPower.run steps
        (MatrixUnaryPower.cfg (some (.inr false)) ((false,false),none)
          [] [] [] (List.replicate t true)) =
        MatrixUnaryPower.cfg none ((false,false),none)
          (List.replicate (2 ^ t) true) [] []
          (List.replicate t true) := MatrixUnaryPower.unary_power_run _

/-- Given two separately materialized unary copies of `2^t`, the existing
six-stack multiply-add controller physically writes `2^t·2^t+1`. The copies
and unary one survive; work banks are empty at halt. -/
theorem physical_stride (t : ℕ) :
    MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime (2 ^ t) (2 ^ t) 1)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate (2 ^ t) true) (List.replicate (2 ^ t) true)
        [true] [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate (2 ^ t) true) (List.replicate (2 ^ t) true)
        [true] [] []
        (List.replicate (2 ^ t * 2 ^ t + 1) true) := by
  simpa only [List.replicate_one, List.append_nil] using
    MatrixAddressMachine.address_run (2 ^ t) (2 ^ t) 1 false []

theorem physical_stride_polynomial (t : ℕ) :
    MatrixAddressMachine.exactTime (2 ^ t) (2 ^ t) 1 ≤
      12 * (2 ^ t + 1) ^ 2 := by
  unfold MatrixAddressMachine.exactTime
  have hp : 0 ≤ 2 ^ t := Nat.zero_le _
  nlinarith

/-- The product width `W=H*K` is physically written from unary `H,K`;
it is the width consumed by the three-phase relative/selector run. -/
theorem physical_payload_width (H K : ℕ) :
    MatrixAddressMachine.run (MatrixAddressMachine.exactTime H K 0)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate H true) (List.replicate K true) [] [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate H true) (List.replicate K true) [] [] []
        (List.replicate (H * K) true) := by
  simpa only [Nat.add_zero, List.append_nil] using
    MatrixAddressMachine.address_run H K 0 false []

/-- The selector-block width `Q*b`, needed for the public selector-prefix
length, is likewise physically computed, not multiplied in finite control. -/
theorem physical_selector_block_width (Q b : ℕ) :
    MatrixAddressMachine.run (MatrixAddressMachine.exactTime Q b 0)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate Q true) (List.replicate b true) [] [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate Q true) (List.replicate b true) [] [] []
        (List.replicate (Q * b) true) := by
  simpa only [Nat.add_zero, List.append_nil] using
    MatrixAddressMachine.address_run Q b 0 false []

/-- Given the independently produced unary block width `Q*b`, public
selector count `S`, and produced relative payload offset `R`, one physical
multiply-add run produces the full payload base `S*Q*b+R`. This theorem
does not claim that those input banks have yet been wired together. -/
theorem physical_prefix_plus_relative (S Q b R : ℕ) :
    MatrixAddressMachine.run
      (MatrixAddressMachine.exactTime S (Q * b) R)
      (MatrixAddressMachine.cfg (some .outer) false
        (List.replicate S true) (List.replicate (Q * b) true)
        (List.replicate R true) [] [] []) =
      MatrixAddressMachine.cfg none false
        (List.replicate S true) (List.replicate (Q * b) true)
        (List.replicate R true) [] []
        (List.replicate (S * Q * b + R) true) := by
  simpa only [Nat.mul_assoc, List.append_nil] using
    MatrixAddressMachine.address_run S (Q * b) R false []

#print axioms physical_relative_and_selector
#print axioms physical_payload_count
#print axioms physical_stride
#print axioms physical_prefix_plus_relative

end Paper2.YaoEntryParameters
