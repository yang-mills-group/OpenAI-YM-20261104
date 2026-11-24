import YM.Integration.WilsonNeutralTwoPrintPathPageRead
import YM.Integration.WilsonOriginalCopiedContraction
import YM.Integration.WilsonOriginalRawQReversion

/-! On the original physical auxiliary period, the measured held direction
uses the same coordinates as the base link at its projected site. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardAxis
open Lattice RG Wilson Function Stationary
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset AllOrder.Ker
open WilsonOriginalRawQReversion (coordinates)
open WilsonNeutralTwoPrintPathPageRead (lower)
variable {G:Gauge}{n X:Side}

theorem original (h:n.val∣X.val)(A:Stationary.Link G n):
    coordinates G X (convey (coverWin h) A)=coordinates G n A ∘ lower h:=rfl

end YM.Integration.WilsonNeutralTwoPrintPathBoardAxis
end
