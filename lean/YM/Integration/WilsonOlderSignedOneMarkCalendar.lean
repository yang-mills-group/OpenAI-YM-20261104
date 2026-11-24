import YM.Integration.WilsonOlderSignedOneMarkFiled
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! A common date for the complete signed one-source edge. The number of
seats and the school precede the cutoff, period, physical post, and
neighboring edges. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkCalendar
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder
open QuadraticLocal.Mentor Org Pert.Asymptotics Further.PhysicalPeriodLimitF933
open WilsonLimitConstruction RG16
open WilsonOlderSignedOneMarkFiled
open scoped Topology

universe u
variable {G : Gauge} (R : Run G) (simple : G.Simple)
  (slow : ∀ n, ((R.family.S.block n).val:ℝ) ≤ Real.log (Lambda R.family.path.levels n))
  (prepared : WilsonReportLampForecast.Ready R.family.path.levels)
  {k : ℕ} (U : Syl.School k) (q d : ℕ)
  (deep : 2*(q+4+1)+8 ≤ U.order) (aged : q+4+4 ≤ 3*k+2) {ε : ℝ} (ep : 0 < ε)

structure Date (i : ℕ) : Prop where
  support : (R.family.path.levels.budget i).supportExponent ≤ 100
  depth : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J i
  shelf : U.horizon ≤ R.alloy.B.a.clock.J i
  scalar : R.t 0 ≤ i
  capture : WilsonCenteredCaptureClock.first R simple ≤ i
  gross : WilsonReceivedSourceGross.opening R simple ≤ i
  fields : WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared ≤ i
  space : Sycamore.Boot.need d U ≤ R.alloy.B.a.clock.J (i+1)
  hard : q+1+6 ≤ R.alloy.B.a.clock.J i
  regular : WilsonFirstReceivedEarnedFee.opening R simple U.pieces (q+4) U.order k deep aged
    (tolerance_pos R q ep) ≤ i
  reversion : WilsonCoherentMayerMutationIntake.firstDate R simple U.order
    (show (0:ℝ) < 1 by norm_num) le_rfl (tolerance_pos R q ep) ≤ i
  masks : WilsonOlderSignedOneMarkBooked.opening R simple (U.order+U.horizon+2) q 102
    (show 0 < ε/6 by positivity) ≤ i
  currency : WilsonOlderSignedOneMarkCurrency.opening R simple q ep ≤ i

theorem cofinal (support : ∀ i, (R.family.path.levels.budget i).supportExponent ≤ 100) :
    ∀ᶠ m : ℕ in atTop, ∀ i, m ≤ i → Date R simple slow prepared U q d deep aged ep i := by
  let target:=Burn.horizon k+2+U.horizon+(q+1+6)+Sycamore.Boot.need d U
  have tall:=R.alloy.B.a.fits.deep.eventually_ge_atTop target
  obtain ⟨n,beginning⟩:=eventually_atTop.mp tall
  let earn:=WilsonFirstReceivedEarnedFee.opening R simple U.pieces (q+4) U.order k deep aged
    (tolerance_pos R q ep)
  let shift:=WilsonCoherentMayerMutationIntake.firstDate R simple U.order
    (show (0:ℝ) < 1 by norm_num) le_rfl (tolerance_pos R q ep)
  let cover:=WilsonOlderSignedOneMarkBooked.opening R simple (U.order+U.horizon+2) q 102
    (show 0 < ε/6 by positivity)
  let cash:=WilsonOlderSignedOneMarkCurrency.opening R simple q ep
  filter_upwards [eventually_ge_atTop n,eventually_ge_atTop (R.t 0),
    eventually_ge_atTop (WilsonCenteredCaptureClock.first R simple),
    eventually_ge_atTop (WilsonReceivedSourceGross.opening R simple),
    eventually_ge_atTop (WilsonOlderSignedOneMarkPhysicalFare.opening R simple slow prepared),
    eventually_ge_atTop earn,eventually_ge_atTop shift,eventually_ge_atTop cover,eventually_ge_atTop cash]
    with m nm born capture gross price regular reversion mask soft
  intro i hi
  have booked:=beginning i (nm.trans hi)
  have upper:=beginning (i+1) ((nm.trans hi).trans (Nat.le_succ i))
  dsimp only [target] at booked upper
  exact ⟨support i,by omega,by omega,born.trans hi,capture.trans hi,gross.trans hi,price.trans hi,
    by omega,by omega,regular.trans hi,reversion.trans hi,mask.trans hi,soft.trans hi⟩

theorem original {T : Campaign R} {W : Campaign.Pillars R T} {slack : ℝ}
    (fund : FundedOriginalProperties.{u} simple slack W) :
    ∀ᶠ m : ℕ in atTop, ∀ i, m ≤ i → Date R simple slow prepared U q d deep aged ep i :=
  cofinal R simple slow prepared U q d deep aged ep (fun i=>(fund.2.1.paid.fixed i).le)

end YM.Integration.WilsonOlderSignedOneMarkCalendar
