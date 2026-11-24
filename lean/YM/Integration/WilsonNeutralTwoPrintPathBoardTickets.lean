import YM.Integration.WilsonNeutralTwoPrintPathBoardSeats
/-! Use the coarse seat that actually lies over the original parent.
No additional choice or common relative placement is required. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardTickets
open Lattice RG Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalConnectedPeriodPage
variable {n X:Side}
def ticket (h:n.val∣X.val)(y:Site n)(x:Site X)(inside:splitter h x=y):Fin (Pages n X):=
  (page h y).symm ⟨x,(posted (splitter h) y x).mpr inside⟩
theorem used (h:n.val∣X.val)(y:Site n)(x:Site X)(inside:splitter h x=y):
    (page h y (ticket h y x inside)).val=x:=by
  unfold ticket
  rw [Equiv.apply_symm_apply]
def central (X:Side){n:Side}(y:Site n):Site X:=wrap X (lift y)
theorem parcel (h:n.val∣X.val)(y:Site n):splitter h (central X y)=y:=
  (branch h (lift y)).trans (wrap_lift y)
end YM.Integration.WilsonNeutralTwoPrintPathBoardTickets
end
