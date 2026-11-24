import YM.Integration.WilsonVacuumPreResetPrunedBirthCell
import YM.RG01Estimate.Society

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedBirthCover
open Function Set Filter Lattice RG RG.Shoot Pressure Wilson WilsonStartup
open PhysicalNext PhysicalNext.Repeat Legato RG01Estimate Further.PhysicalPeriodLimitF933
open Further.PhysicalPeriodLimitF933.Macrame
open WilsonVacuumPreResetPrunedBirthSites WilsonVacuumPreResetPrunedBirth
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G)(archive:Extension.UV.Archive R.alloy.B)(m:ℕ)
    {c f C F:Side}(H:f.val=c.val*(R.alloy.B.a.S.block m).val)
    (H':F.val=C.val*(R.alloy.B.a.S.block m).val)(β:ℝ)(hb:β∈band R.alloy.B.a (m+1))
    (d:ℕ)(hd:3≤d)

theorem reports {M:ℕ}(hC:C.val=c.val*M)(hc:2≤c.val):
    Board.reports H H' β (paid R archive m H β hb d hd)
      (paid R archive m H' β hb d hd) hC hc:=by
  let X:=Lace.project (P:=(R.alloy.B.a.clock.op m 0).patch) (h:=H) (H:=H') hC hc
  let W:=R.alloy.B.kin.path (m+1) (m+1)
  let clip:=(R.alloy.B.a.params (m+1)).clip
  let P:=R.alloy.B.a.budget (m+1)
  constructor
  · intro i
    change ((filed f W clip P β).activities.reg (roster G f (X.high.cut i.1,i.2))).support=
      ((filed F W clip P β).activities.reg (roster G F i)).support.image X.high.cut
    rw [address,address]
    exact WilsonVacuumPreResetPrunedBirthCell.footprint X.high i
  · intro i A
    exact WilsonVacuumPreResetPrunedBirthCell.measured X.high W clip P β i A

theorem original (hc:2≤c.val)(hC:2≤C.val):
    Board.Clockset H H' β (paid R archive m H β hb d hd)
      (paid R archive m H' β hb d hd):=by
  let b:=R.alloy.B.a.S.block m
  let n:=c*C
  let B:(n*b).val=n.val*b.val:=rfl
  exact ⟨paid R archive m B β hb d hd,hc,hC,
    reports R archive m H B β hb d hd rfl hc,
    reports R archive m H' B β hb d hd (mul_comm ..) hC⟩

end YM.Integration.WilsonVacuumPreResetPrunedBirthCover
