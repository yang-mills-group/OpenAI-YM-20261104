import YM.Integration.WilsonThermometerUnpaintedCapture
import YM.Integration.WilsonThermometerMixedEndpoint

/-! A complete original Gallery, regular and forced budgets intact, on each fixed older Wilson reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnpaintedOlder
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

variable {G:Gauge}(R:Run G)(simple:G.Simple){N per m i u k:ℕ}
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

include way D bank ticket π Γ course in
theorem original (cut:i<N)(floor:m ≤ u)(ui:u ≤ i)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
    (sec:R.t 0 ≤ i)(slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    {X I:Type}[Countable I]{o:Fin 3→Site (It)}(A:Gallery X I o (Ψ i) (J))(fired:X)
    (w:Fin 3→ℝ)(positive:∀j,0<w j)(c:(J).Mode→ℂ)(α:ℝ)(strength:(Ψ i).p.supportExponent ≤ α)
    (y:Site (It))(Z:Support (It))(center:y∈Z)(resident:∀j,o j∈Z)(box:Z⊆halo (Ψ i).p.B {y})
    (rad:ℕ)(near:∀j,separation (o j) y ≤ rad)(radius:rad ≤ (Ψ i).p.B)
    {C:ℝ}(complete:A.E.Paid w (Ψ i).p.B ((Ψ i).p.supportExponent+2) C)
    (forced:A.K.Paid w (Ψ i).p.B (Ψ i).p.supportExponent κ):
    let w':=Stoop.radius w (max 1 C)
    let bill:=weightBill c w'
    let k₀:=WilsonFullFaceSignedPower.inter*((Fintype.card (Multi.parts (J)).Mode:ℝ)*27)
    let K:=|WilsonFullFaceSignedPower.constants (S) (Y) α 4|
    let f:=fun U=>take c (A.density fired U)-((Ψ i).eval U:ℂ)*take c (Poly.pass (0:Poly (J)))
    MeasureTheory.Integrable f (prior G _) ∧ ∀j,u ≤ j→∀ji:j ≤ i, ‖read f j ji‖ ≤ bill*(g⁻¹)^87*(testPrice (F)*k₀+15*K):=by
  intro w' bill k₀ K f
  have mi:=floor.trans ui
  have walk:=course.1.walk i mi cut.le
  obtain ⟨keeper⟩:=WilsonCenteredCourseKeeper.original R course i mi cut
  have shape:(Ψ i).p=R.family.path.levels.budget i:=walk.truep.point
  have rdr:=(WilsonCapturedPrimarySection.original R sec (Ψ i) shape).1
  obtain ⟨temp,_,motion,columns,div,upper,hv,room,froom⟩:=
    (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose_spec i early N per cut
  have gt:0 < max 1 C:=zero_lt_one.trans_le (le_max_left ..)
  have shrink:1 ≤ max 1 C:=le_max_left .. 
  have hp:∀j,0<w' j:=fun j=>div_pos (positive j) gt
  have amt:(max 1 C)⁻¹*C ≤ 1:=(inv_mul_le_iff₀ gt).2 (by simpa only [mul_one] using (le_max_right 1 C))
  have newsoft:=Lamps.loan_monotone _ (Stoop.tighten w A.E positive shrink complete) amt
  have newhard:=Stoop.leaves w A.K positive shrink forced
  obtain ⟨h,fmt,rem,out,prim⟩:=WilsonThermometerUnpaintedCapture.original A fired w' hp c keeper walk.truep.valid div hv
    (shape ▸ room) (shape ▸ froom) (S) (Y) rdr y Z center resident box rad near radius strength temp (shape ▸ motion)
    (zero_le_one.trans (R.family.path.levels.params i).columns_ge) columns div.le upper le_rfl newsoft newhard
  have bpos:0 ≤ bill:=sum_nonneg fun s _=>div_nonneg (norm_nonneg _) (Poly.worth hp s).le
  have zp:0 ≤ g⁻¹:=zero_le_one.trans temp
  have M0:0 ≤ bill*(K*(g⁻¹)^87*3):=by dsimp only [K];positivity
  have whole:=WilsonThermometerUnitFilingWhole.original R simple way D bank ticket π Γ Ψ course cut.le floor ui gate
    y h fmt rem M0
  have same:h.density y (S) (Ψ i)=f:=funext out
  rw [←same]
  refine ⟨(WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course mi cut.le (S) (Y) y h fmt rem).2,?_⟩
  have unit:‖h.x 0‖ ≤ testPrice (F)*(bill*k₀):=
    (single_le_sum (fun q _=>norm_nonneg (h.x q)) (mem_univ 0)).trans prim
  have tp:0 ≤ testPrice (F):=zero_le_one.trans (probe_budget (F)).choose_spec.choose_spec.1
  have kpos:0 ≤ k₀:=by dsimp only [k₀];have h0:=WilsonFullFaceSignedPower.bounded.choose_spec.1;unfold WilsonFullFaceSignedPower.inter;positivity
  have initial:1 ≤ (g⁻¹)^87:=one_le_pow₀ temp
  have boost:testPrice (F)*(bill*k₀) ≤ testPrice (F)*(bill*k₀)*(g⁻¹)^87:=
    le_mul_of_one_le_right (by positivity) initial
  intro j uj ji
  calc _  ≤  ‖h.x 0‖+5*(bill*(K*(g⁻¹)^87*3)):=whole.1 j uj ji
       _  ≤  testPrice (F)*(bill*k₀)*(g⁻¹)^87+5*(bill*(K*(g⁻¹)^87*3)):=add_le_add (unit.trans boost) le_rfl
       _ = _ :=by ring
end YM.Integration.WilsonThermometerUnpaintedOlder
end
