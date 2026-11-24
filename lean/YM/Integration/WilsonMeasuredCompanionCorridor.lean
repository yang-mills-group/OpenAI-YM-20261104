import YM.Integration.WilsonMeasuredCompanionTransport

/-! A genuine occupied table on its native course, integrated back from a common receiving halo. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionCorridor
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonGeometricSignedCapture
local notation "J" => Stock.census (Fin 3)

variable {G:Gauge}(R:Run G)(simple:G.Simple){N per m i u k t f:ℕ}
  (way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (bank:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D bank)
  (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
local notation "S" => R.family.localSection 0
local notation "F" => R.family.labels.level 0
local notation "Y" => R.family.params
local notation "μ" => (R.family.path.levels.params i).columns
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "g" => Pert.Asymptotics.regulatorRun R.family N per (i+1)
local notation "It" => R.family.side i per
local notation "read" => WilsonThermometerUnitFilingCoarse.reading R (N:=N)

open MergeProof.Accent WilsonThermometerMixedCorridor WilsonThermometerMixedCollarSubpower
local notation "gt" => Pert.Asymptotics.regulatorRun R.family N per (f+1)
local notation "zf" => scale (R.alloy.B.a.clock.hatBeta (f+1))

open WilsonMeasuredCompanionTransport

def charge (α:ℝ):ℝ:=(2:ℝ)^87*abs (testPrice (F)*
  (WilsonFullFaceSignedPower.inter*((Fintype.card (Multi.parts (J)).Mode:ℝ)*27))
  +15*abs (WilsonFullFaceSignedPower.constants (S) (Y) α 4))

private theorem member (s:(J).Mode)(A:Poly (J)):take (key s) A=A.part s:=
  (identified s (fun _=>1) A).1

include way D bank ticket π Γ course in
theorem one (floor:m ≤ u)(ui:u ≤ i)(it:i≤t)(tf:t≤f)(cut:f+1≤N)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
    (sec:R.t 0 ≤ i)(slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (C:ℝ)(cp:0≤C)(d:ℕ)
    (onset:(eventually_atTop.mp (WilsonThermometerMixedCorridorWallet.original R simple C cp d)).choose ≤ f)
    (length:(t-i:ℕ) ≤ C*zf^d)(stage₀:∀(j:ℕ),i≤j→3≤R.alloy.B.a.clock.J j)
    {X K:Type}[Countable K]{o:Fin 3→Site (R.family.side t per)}(A:Gallery X K o (Ψ t) (J))(fired:X)
    (w:Fin 3→ℝ)(positive:∀j,0<w j)(s:(J).Mode)(occupied:s≠(J).quiet)
    (α:ℝ)(strength:(Ψ i).p.supportExponent ≤ α)
    (y:Site (It))(Z:Support (It))(center:y∈Z)(resident:∀j,sites R o it j∈Z)(box:Z⊆halo (Ψ i).p.B {y})
    (rad:ℕ)(near:∀j,separation (sites R o it j) y ≤ rad)(radius:rad ≤ (Ψ i).p.B)
    (complete:A.E.Paid w (Ψ t).p.B ((Ψ t).p.supportExponent+2) 1)
    (forced:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (LocalComparison.forcedDivisor R.family t)):

    MeasureTheory.Integrable (A.density fired) (prior G _) ∧
      ∀j,u ≤ j→∀ji:j ≤ i,gt^88*‖read (fun U=>((A.density fired) U).part s) j (ji.trans it)‖ ≤
        (1/Poly.toll w s)*charge R α:=by
  have law:=(course.1.walk t ((floor.trans ui).trans it) (tf.trans_lt cut).le).truep.valid
  have before:=QuadraticLocal.Tariff.integrable (J) o w positive A fired
    (show A.Pays w (Ψ t).p.supportExponent 1 (LocalComparison.forcedDivisor R.family t) from
      ⟨WilsonPrecontactSeparatedLamps.lower A.E (by linarith) positive complete,forced⟩)
    (Ψ t).p.exponent_pos.le law
  have income:gt^0*weightBill (key s) w ≤ 1/Poly.toll w s:=by
    rw [pow_zero,one_mul,(identified s w 0).2]
  have field:=WilsonThermometerMixedCorridorReading.original R simple way D bank ticket π Γ Ψ course
    floor ui it tf cut gate sec slow ready early C cp d onset length stage₀ A fired w positive
    (key s) 0 (1/Poly.toll w s) income α strength y Z center resident box rad near radius complete forced
  refine ⟨before,fun j uj ji=>?_⟩
  rw [←through R (A.density fired) before s it ji]
  simpa only [member,Next.Rank.Exponential.pass_zero,Poly.one_part,if_neg occupied,mul_zero,
    sub_zero,charge,mul_assoc] using field.2 j uj ji

end YM.Integration.WilsonMeasuredCompanionCorridor
