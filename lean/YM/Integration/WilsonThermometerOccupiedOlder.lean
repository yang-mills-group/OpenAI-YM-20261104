import YM.Integration.WilsonMeasuredCompanionCorridor
import YM.Integration.WilsonThermometerOccupiedLinear
import YM.Integration.WilsonThermometerReceivedHardNodes

/-! Erase all occupied hard entries of the original finite three-mark source in a fixed older reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerOccupiedOlder
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

open WilsonMeasuredCompanionCorridor WilsonThermometerOccupiedInterpolation
open WilsonThermometerOccupiedGallery

include way D bank ticket π Γ course in
theorem original (floor:m ≤ u)(ui:u ≤ i)(it:i≤t)(tf:t≤f)(cut:f+1≤N)
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
    (T:ℝ)(large:1≤T)
    (forced:∀z:ℂ,‖z‖≤3*T→(gallery z A).K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent
      (LocalComparison.forcedDivisor R.family t)):
    let real:=fun U=>(A.density fired U).part s
    let regular:=fun U=>(((Ψ t).eval U:ℂ) • Poly.pass (A.E.log fired U)).part s
    ∀ (j : ℕ), u ≤ j → ∀ (ji : j ≤ i), gt^88*‖read real j (ji.trans it)-read regular j (ji.trans it)‖≤
       10*((1/Poly.toll w s)*WilsonMeasuredCompanionCorridor.charge R α)/T:=by
  intro real regular
  have tp:0<T:=zero_lt_one.trans_le large
  let z (v:Fin 4):ℂ:=if v=0 then 0 else if v=1 then T else if v=2 then 2*(T:ℂ) else 3*(T:ℂ)
  have within (v:Fin 4):‖z v‖≤3*T:=by
    fin_cases v <;> simp [z,abs_of_nonneg tp.le] <;> linarith
  let field (v:Fin 4):Config G (R.family.side t per)→ℂ:=
    fun U=>((gallery (z v) A).density fired U).part s
  have points (v:Fin 4):MeasureTheory.Integrable (field v) (prior G _) ∧
      ∀ (j : ℕ), u ≤ j → ∀ (ji : j ≤ i), gt^88*‖read (field v) j (ji.trans it)‖≤
        (1/Poly.toll w s)*WilsonMeasuredCompanionCorridor.charge R α:=by
    have p:=WilsonMeasuredCompanionCorridor.one R simple way D bank ticket π Γ Ψ course
      floor ui it tf cut gate sec slow ready early C cp d onset length stage₀ (gallery (z v) A)
      fired w positive s occupied α strength y Z center resident box rad near radius complete (forced _ (within v))
    exact ⟨(Poly.get s).integrable_comp p.1,p.2⟩
  have fund (a:ℂ)(ha:a∈({0,(T:ℂ),2*(T:ℂ),3*(T:ℂ)}:Finset ℂ)):
      (gallery a A).K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (LocalComparison.forcedDivisor R.family t):=by
    apply forced
    simp only [mem_insert,mem_singleton] at ha
    rcases ha with rfl|rfl|rfl|rfl <;> simp [abs_of_nonneg tp.le] <;> linarith
  have same U:real U=fitted T⁻¹ (field 0 U) (field 1 U) (field 2 U) (field 3 U):=by
    have held:=congrArg (fun p:Poly (J)=>p.part s)
      (WilsonThermometerOccupiedGallery.field A fired U w positive T⁻¹ T _ (inv_mul_cancel₀ tp.ne') fund)
    have part (a b c d:Poly (J)):
        (fitted T⁻¹ a b c d).part s=fitted T⁻¹ (a.part s) (b.part s) (c.part s) (d.part s):=rfl
    rw [part] at held
    simpa [real,field,z] using held
  have zero:field 0=regular:=by
    funext U
    exact congrArg (fun p:Poly (J)=>p.part s) (WilsonThermometerOccupiedGallery.origin A fired U
      w positive (fund 0 (by simp)))
  intro j uj ji
  have gp:=ActualRunKernelPackets.regulator_pos R N per (f+1) cut
  have gross:0<gt^88:=pow_pos gp _
  let upper:=(1/Poly.toll w s)*WilsonMeasuredCompanionCorridor.charge R α
  let v (k:Fin 4):ℂ:=read (field k) j (ji.trans it)
  have prices(k:Fin 4):‖v k‖≤upper/gt^88:=(le_div_iff₀ gross).2
    ((mul_comm _ _).le.trans ((points k).2 j uj ji))
  have paid:=WilsonThermometerOccupiedInterpolation.bill T⁻¹ (inv_nonneg.mpr tp.le)
    (inv_le_one_of_one_le₀ large) (v 0) (v 1) (v 2) (v 3) (upper/gt^88)
    (prices 0) (prices 1) (prices 2) (prices 3)
  have combined:=WilsonThermometerOccupiedLinear.earlier R (N:=N) T⁻¹ real field (fun k=>(points k).1) same (ji.trans it)
  rw [combined,←zero]
  apply (mul_le_mul_of_nonneg_left paid gross.le).trans
  change gt^88*(10*(upper/gt^88)*T⁻¹)≤10*upper/T
  exact le_of_eq (by field_simp)

end YM.Integration.WilsonThermometerOccupiedOlder
