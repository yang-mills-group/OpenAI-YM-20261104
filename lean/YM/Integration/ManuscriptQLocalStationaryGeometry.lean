import YM.Integration.ActualRunSpring
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Station

/-! The two actual adjacent beds, their original path and transfer kernels,
and the purchased stationary laws, on the very same Run and interior stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalStationaryGeometry
open Lattice Wilson RG Precision Pressure Pressure.Testing Pressure.Tube
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Progress.DirectedRecipe AnalyticNext.ConnectedActivity.Aff
variable {G : Gauge} (R : Run G) (N m p : ℕ) (hm : m<N)
include hm

theorem funds : (query R.metals.p R.metals.K (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m)).Funds (R.alloy.B.a.clock.op m p) (ships R.alloy.B N m p) :=
  Pressure.Testing.proceeds (R.alloy.B) N m p hm

/-- This attachment includes the upper endpoint m+1=N and uses the same
physical high and low paths and the same transfer on every forest draw. -/
theorem alongside : Alongside (R.alloy.B.M.H N (m+1)) (R.alloy.B.M.H N m) (ships R.alloy.B N m p) where
  inbound := R.alloy.B.support.links N (m+1) hm
  outbound := R.alloy.B.support.links N m hm.le
  together := R.alloy.B.plan.crossings N m p hm
  sails := R.alloy.B.plan.stack N m p hm
  budgets := ⟨_,_,_,_,R.alloy.B.plan.all N (m+1) hm _,R.alloy.B.plan.all N m hm.le _⟩
  old := R.kit.pledging.conducts.full N (m+1) _ hm
  new := R.kit.pledging.conducts.full N m _ hm.le

theorem larger : Bid.Larger (G:=G) (R.alloy.B.a.clock.op m p) :=
  let P := ActualRunSpring.selected R N p m hm
  (P.spring.H.houses P.point).laws.data.room.larger
end YM.Integration.ManuscriptQLocalStationaryGeometry
end
