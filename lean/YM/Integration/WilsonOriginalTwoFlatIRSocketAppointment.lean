import YM.Integration.WilsonOriginalTwoFlatIRCapturedCross
import YM.Integration.WilsonOriginalTwoFlatIRSocketHome
/-! Choose the infrared ear on the actual physical compact-cell capture,
before either original cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRSocketAppointment
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Multi Gauge
open Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Poetry
open Planned.GuardedAtom Extra.Histories Next.Foundations RG16 RG16.Literal Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonPositionProgramReporterBand WilsonIndependentCapturedPages
open WilsonOlderFreshGraphSlate WilsonRegisteredPairUnaryWallet WilsonOriginalMixedBlockRows
open WilsonRootedKioskOccupiedSlip WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatIRHalo WilsonOriginalTwoFlatTelescope WilsonOriginalTwoFlatGridScaling
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family
local notation "Tchr" => R.family.path.levels
local notation "Sec" => R.family.localSection 0
local notation "par" => R.family.params


open WilsonOriginalTwoFlatIRCapturedCross (Quote)
open StressFlux.Matching Cells
open WilsonReceivedChronologicalFixedCellFee (factor capture)
open Analysis Table Spec Extraction Next.UVStress

theorem original (simple:G.Simple)(slow:∀m,((C).S.block m).val ≤ Real.log (Lambda (Tchr) m))
    (ready:WilsonReportLampForecast.Ready (Tchr))(D₀:XSpace.Run){stage u d:ℕ}
    (band:Band R D₀ stage)(v:WilsonIndependentCapturedPages.Stop R D₀ band u d)(cu:(C).ref 0 ≤ u)(P:ℕ)
    {n:ℕ}(φ:Test n)(floor:ℕ):
    ∃radius:ℝ,0<radius ∧ ∀r:ℝ,0<r → r≤radius →
    let c:=capture R φ r
    ∃h:ℕ,∃_same:c=band.reporter+h,∃uc:u≤c,∃vc:v.date h≤c,
      floor+1≤c ∧ factor R φ*r≤R.family.S.a 0 ∧
      ∀N per:ℕ,c<N → Quote R N per u (v.date h) c P d uc vc:=by
  obtain ⟨k,head⟩:=eventually_atTop.mp (WilsonOriginalTwoFlatIRCapturedCross.original R simple slow ready D₀ band v cu P)
  let cap₀:=max (max u (floor+1)) (band.reporter+k)
  have hp:=WilsonReceivedChronologicalFixedCellFee.positive R φ
  refine ⟨(C).S.a cap₀/factor R φ,div_pos ((C).S.a_pos cap₀) hp,?_⟩
  intro r rp small c
  have fit:factor R φ*r≤(C).S.a cap₀:=by simpa only [mul_comm] using (le_div_iff₀ hp).mp small
  have opening:=fit.trans ((C).S.strictAnti.antitone (Nat.zero_le cap₀))
  have level:cap₀≤c:=by
    by_contra! tooSmall
    have later: (C).S.a cap₀≤(C).S.a (c+1):=(C).S.strictAnti.antitone (by omega)
    exact (not_lt_of_ge (fit.trans later)) (WilsonCloseCaptureDate.bracket (C).S (mul_pos hp rp) opening).1
  have a:u≤c:=(le_max_left _ _).trans ((le_max_left _ _).trans level)
  have b:floor+1≤c:=(le_max_right _ _).trans ((le_max_left _ _).trans level)
  have position:band.reporter+k≤c:=(le_max_right _ _).trans level
  let h:=c-band.reporter
  have e:c=band.reporter+h:=by dsimp only [h];omega
  have lower:k≤h:=by dsimp only [h];omega
  have endpoint:v.date h≤c:=e.symm ▸ v.upper h
  refine ⟨h,e,a,endpoint,b,opening,?_⟩
  intro N per nc
  have earned:Quote R N per u (v.date h) (band.reporter+h) P d (e ▸ a) (v.upper h):=head h lower N per (show band.reporter+h<N from e ▸ nc)
    (show u≤band.reporter+h from e ▸ a)
  have cast (date:ℕ)(same:band.reporter+h=date)(uDate:u≤date)(vDate:v.date h≤date):
      Quote R N per u (v.date h) date P d uDate vDate:=by
    cases same
    exact @earned
  exact @cast c e.symm a endpoint

end YM.Integration.WilsonOriginalTwoFlatIRSocketAppointment
end
