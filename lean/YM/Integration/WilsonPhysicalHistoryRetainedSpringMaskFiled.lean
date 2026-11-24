import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskEarned
import YM.Integration.WilsonRegisteredSpringPriorCourse

/-! File the physical mask estimate on the original pre-period spring list and
the guide that furnished the enrolled conditional numerator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open OriginalMarkedRunAction
open IterationFour IterationFour.Vacuum Comparison.RG02
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Fk
open scoped BigOperators Classical ENNReal
variable {G : Gauge} (R : Run G)

theorem cofinal_filed_mask (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (held : WilsonFundedWindowCompany.PhysicalInputs R.kit) (heat : OPE.Therm.Poetry R.family.path.levels)
    (mark : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (checkoutPrice : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay)
    (cov : Mallow.RG12.Earned (WilsonCoherentMayerCovarianceCalendar.decal G) R.kit.shape R.alloy.delay)
    (d : ℕ) (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit)
    (paths : FundedOriginalVacuumPaths.prices R.kit) (e K load q : ℕ) {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    ∃ credit : Credit, ∀ᶠ m : ℕ in atTop,
      let V:=R.family.path.levels
      ∃ σ : ℝ, 0<σ ∧ σ⁻¹≤zz V (m+1) ∧ ∀ N : ℕ, (later : m+1<N) →
      let C:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      let old:=R.alloy.B.kin.path N (m+1)
      let clip:=(V.params (m+1)).clip
      ∃ Z : SeriesA G, (∀ a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧ Z.length ≤ meterPre (3+e) ∧
        Draw Z σ C ∧ RunFundedPeriodAction.PeriodData Z (2+e) σ C ∧
        (∀ k<3+e,∀ n : Side,∀ l,Blue.mix (pace (pitch V R.metals.O N (m+1)))
          (front old clip n+sands Z n) k (l+1)=lagoon (freshet V R.metals.O N (m+1) k (l+1)) n) ∧
        RootedSpringBounds R m N Z (2+e) (3+e) load K ε η ∧
        WilsonRegisteredFiledInvoice.Invoice R m N (2+e) Z C ∧
        SpringMaskEstimate R m N Z σ C (2+e) q ε ∧
        ∀ per, ∃ H : Guide R.alloy.B R.kit.shape N m per (R.family.path.rep N per (m+1)),
          WilsonRegisteredSpringPriorCourse.Paid R per later d Z (2+e) K ε η (WilsonRegisteredSpringPriorCourse.physicalCash R per H) := by
  obtain ⟨credit,offer⟩:=WilsonRegisteredSpringPriorCourse.original R simple slow held mark checkoutPrice cov d v rows paths e K load ep hp
  refine ⟨credit,?_⟩
  filter_upwards [offer,cofinal_spring_mask_return R simple slow heat v rows credit (3+e) (meterPre (3+e)) (2+e) q ep]
    with m previous mask
  obtain ⟨σ,hs,width,allN⟩:=previous
  refine ⟨σ,hs,width,?_⟩
  intro N later C old clip
  obtain ⟨Z,lower,birth,length,draw,period,correct,root,invoice,guide⟩:=allN N later
  have occupied (a:PrismA G) (ha:a∈Z):0<a.grade:=by have:=lower a ha;omega
  exact ⟨Z,lower,birth,length,draw,period,correct,root,invoice,
    mask N later σ hs width Z draw length occupied (fun a ha=>(birth a ha).le),guide⟩

end YM.Integration.OriginalMarkedRunAction
