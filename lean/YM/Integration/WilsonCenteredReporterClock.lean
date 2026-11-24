import YM.Integration.WilsonCenteredDividedRoom
import YM.Integration.WilsonReportLampForecast
import YM.Integration.WilsonRootedKioskPostRadius
import YM.Integration.WilsonCapturedPrimarySection

/-! The original divided hard allowance, field reader and directional radius
have simultaneous prices before both Wilson regulators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredReporterClock
open Filter Lattice Wilson RG PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.Local Push.PriceCompiler Next.Foundations Extra.Histories Pert.Asymptotics RG16
open scoped Classical Topology
theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (slow : ∀ m, ((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels) :
    ∀ᶠ i : ℕ in atTop, ∀ N per, i<N →
      let g:=regulatorRun R.family N per (i+1)
      let p:=R.family.path.levels.budget i
      let κ:=LocalComparison.forcedDivisor R.family i
      let η:=R.alloy.B.a.clock.forcedAllowance i
      1≤g⁻¹ ∧ R.alloy.B.a.clock.hatBeta (i+1)≤2*(g⁻¹)^2 ∧
      WilsonReportRetainedAnchor.reprice p p.B≤2*(g⁻¹)^2 ∧
      (R.family.path.levels.params i).columns≤4*(g⁻¹)^2 ∧
      0<κ ∧ κ≤1 ∧ 0≤η ∧ hitWidth p*η≤1 ∧ hitWidth p*η/κ≤1 := by
  let A:=R.alloy.B.a
  have rise : Tendsto A.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  filter_upwards [rise.eventually_ge_atTop (2:ℝ),WilsonRootedKioskPostRadius.original R simple,ready 0,
    WilsonCapturedPrimarySection.priced R simple slow,WilsonCenteredCaptureClock.original R simple,
    WilsonCenteredDividedRoom.original R simple] with i late window radius income first second N per live
  let β:=(R.family.path.rep N per (i+1)).beta
  let g:=regulatorRun R.family N per (i+1)
  have xp : 0<β := Overlay.beta_positive R.makes.wilson live
  have x : g⁻¹=Real.sqrt β:=inv_inv _
  have square : (g⁻¹)^2=β := x ▸ Real.sq_sqrt xp.le
  let H:=A.clock.hatBeta (i+1)
  have lower : H/2≤β := (R.makes.wilson.represents N per (i+1) live).band.1
  have price : H≤2*(g⁻¹)^2 := by rw [square];linarith only [lower]
  have floor : 1≤g⁻¹ := by
    rw [x,←Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    linarith only [late,window.2.1,lower]
  have lamp : WilsonReportRetainedAnchor.reprice (A.budget i) (A.budget i).B ≤ A.clock.hatBeta i := by
    simp only [WilsonReportLampForecast.part,Nat.cast_zero,zero_add,div_one,Real.rpow_one] at radius
    exact radius
  exact ⟨floor,price,lamp.trans (window.2.1.trans price),by simpa only [div_eq_mul_inv,inv_pow] using income N per live,
    first.1,second.1,first.2.1,first.2.2,second.2⟩

end YM.Integration.WilsonCenteredReporterClock
