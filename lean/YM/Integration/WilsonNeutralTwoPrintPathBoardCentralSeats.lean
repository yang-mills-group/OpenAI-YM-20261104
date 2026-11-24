import YM.Integration.WilsonNeutralTwoPrintPathBoardTickets
import YM.Integration.WilsonIndependentCollarOrbitalReception

/-! Any physical lifts of the registered parents agree with the paid single
sheet at each occupied site, even across a boundary of the torus. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonNeutralTwoPrintPathBoardCentralSeats
open Lattice RG Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open WilsonOriginalConnectedPeriodPage WilsonNeutralTwoPrintPathFineFiber
open WilsonNeutralTwoPrintPathBoxInk WilsonIndependentCollarOrbitalReception
open scoped Classical BigOperators
variable {I:Type}[DecidableEq I]{n f:Side}

theorem on_sheet (z:Site f)(t:Fin (Pages f f)):
    (page dvd_rfl z t).val=z:=by
  let x:=(page dvd_rfl z t).val
  have fixed:splitter (dvd_refl f.val) x=x:=by
    have lam:=branch (dvd_refl f.val) (lift x)
    simpa only [wrap_lift] using lam
  exact fixed.symm.trans ((posted (splitter (dvd_refl f.val)) z x).mp (page dvd_rfl z t).prop)

theorem original (P:Patch)(geometry:f.val=n.val*P.L.val)(S:Finset I)(anchor:S)
    (address:I→Site f)(sheet:S→Fin (Pages f f))(place:I → Lattice.Cover)
    (located:∀l∈S,wrap n (place l)=(Ratio.mk P.L geometry:Ratio n f).parent (address l)):
    ∀l∈S,wrap n (seats P geometry dvd_rfl dvd_rfl S address sheet anchor l)=
      wrap n (ink S anchor.val (place anchor.val) (relative S anchor.val place) l):=by
  intro l hl
  rw [at_front S anchor.val place l hl,located l hl]
  have here:=rooted P geometry dvd_rfl dvd_rfl S address sheet anchor ⟨l,hl⟩
  change _=(Ratio.mk P.L geometry:Ratio n f).parent (page dvd_rfl (address l) (sheet ⟨l,hl⟩)).val at here
  simpa only [on_sheet] using here

end YM.Integration.WilsonNeutralTwoPrintPathBoardCentralSeats
end
