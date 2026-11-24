import YM.Integration.WilsonMeasuredPointTopCoin
import YM.Integration.WilsonThermometerSectionStretch

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointApertureWage
open Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 WilsonLimitConstruction PhysicalNext.Repeat Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot
open Next.UVStress Next.Rank Next.Rank.East MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "S" => R.family.S
local notation "B" n:max => R.family.path.levels.clock.hatBeta n

open Next.Foundations WilsonNeutralCopiedProgram WilsonNeutralCopiedField
local notation "F₁" => R.family.labels.level 4
local notation "named" => WilsonNeutralOffsetCutoff.named R

/-- One literal nominated grade-four leg, priced at its station before the
UV cutoff, period, leg, complex phase or physical reference is chosen. -/
theorem original (simple:G.Simple) (δ:ℝ)(dp:0<δ):
    ∀ᶠ k:ℕ in atTop,∀ A:Group C 6,A.station.k=k → A.station.checked f H A.horizon → close R A →
    ∀ N per:ℕ,k<N → ∀leg:Fin 2,∀phase:ℂ→ₗ[ℝ]ℝ,
      let x:=named A N per leg.succ
      let cap:=((S).a k/(S).a N)^5*((B k)^δ*mass R)
      (F₁).coeffSize (Price.awake C 4 N N per x)≤cap ∧
      (∑v:(F₁).Index,|fee R N per x phase (ConnectedActivityE6.Coat.gStep (R.family.beta N per)) v|)≤
        2*‖phase.toContinuousLinearMap‖*cap:=by
  filter_upwards [WilsonOriginalThermometerPalette.station R (f:=f) (H:=H) simple δ dp,
    eventually_ge_atTop (R.family.ref 4)] with k registered ref
  intro A atK checked near N per cut leg phase
  let x:=named A N per leg.succ
  have stationFee:(F₁).coeffSize (Price.awake C 4 k N per x)≤(B k)^δ*mass R:=by
    have paid:=(registered A atK checked N per cut leg.succ).trans
      (mul_le_mul_of_nonneg_left (WilsonOriginalThermometerReportedGrading.station_mass R A near)
        (Real.rpow_nonneg (zero_le_one.trans ((C).path.levels.fits.delayed k).le) _))
    exact paid
  have hop:=WilsonThermometerSectionStretch.sectionAt R 4 k N per ref x cut.le le_rfl
  have full:=(hop.trans (mul_le_mul_of_nonneg_left stationFee
    (pow_nonneg (div_nonneg ((S).a_pos _).le ((S).a_pos _).le) _)))
  exact ⟨full,(WilsonMeasuredPointTopCoin.funded R N per simple (ref.trans cut.le) x phase).trans
    (mul_le_mul_of_nonneg_left full (by positivity))⟩

end YM.Integration.WilsonMeasuredPointApertureWage
end
