import YM.Integration.WilsonThermometerMixedCorridorWallet
import YM.Integration.WilsonThermometerUnpaintedOlder
import YM.Integration.WilsonThermometerMixedFlatPrice
import YM.Integration.WilsonLocalCompactRichPortUnits
import YM.Integration.WilsonThermometerUnpaintedCapture
import YM.Integration.WilsonThermometerMixedEndpoint

/-! A complete original Gallery, regular and forced budgets intact, on each fixed older Wilson reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerMixedCorridorReading
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
    (w:Fin 3→ℝ)(positive:∀j,0<w j)(c:(J).Mode→ℂ)(l:ℕ)(B:ℝ)(income:gt^l*weightBill c w ≤ B)
    (α:ℝ)(strength:(Ψ i).p.supportExponent ≤ α)
    (y:Site (It))(Z:Support (It))(center:y∈Z)(resident:∀j,sites R o it j∈Z)(box:Z⊆halo (Ψ i).p.B {y})
    (rad:ℕ)(near:∀j,separation (sites R o it j) y ≤ rad)(radius:rad ≤ (Ψ i).p.B)
    (complete:A.E.Paid w (Ψ t).p.B ((Ψ t).p.supportExponent+2) 1)
    (forced:A.K.Paid w (Ψ t).p.B (Ψ t).p.supportExponent (LocalComparison.forcedDivisor R.family t)):
    let filed:=gust R.family.path N per t (A.density fired) i it
    let field:=fun U=>take c (filed U)-((Ψ i).eval U:ℂ)*take c (Poly.pass (0:Poly (J)))
    let αfee:=testPrice (F)*(WilsonFullFaceSignedPower.inter*((Fintype.card (Multi.parts (J)).Mode:ℝ)*27))
      +15*|WilsonFullFaceSignedPower.constants (S) (Y) α 4|
    MeasureTheory.Integrable field (prior G _) ∧
      ∀j,u ≤ j→∀ji:j ≤ i,gt^(l+1+87)*‖read field j ji‖ ≤ B*(2:ℝ)^87*|αfee|:=by
  intro filed field αfee
  letI:Nonempty X:=⟨fired⟩
  have cap (j:ℕ)(ij:i≤j):LocalComparison.forcedDivisor R.family j ≤ 1:=
    (WilsonSingleHardRadius.cash R simple 0 zero_lt_one (gate.trans (ui.trans ij))).1.trans (by norm_num)
  obtain ⟨J',L,hJ,regular,hard,heard⟩:=WilsonThermometerMixedCorridor.original R way D bank π Γ Ψ course ticket o A w positive
    (floor.trans ui) (tf.trans ((Nat.le_succ f).trans cut)) it stage₀ cap complete forced
  letI:Countable J':=hJ
  have wp:=WilsonThermometerMixedCorridor.positive R w positive it
  have receipt:=WilsonThermometerUnpaintedOlder.original R simple way D bank ticket π Γ Ψ course (by omega)
    floor ui gate sec slow ready early (I:=J') L fired (wallet R w it) wp c α strength y Z center resident box rad near radius regular hard
  have trimmed : Stoop.radius (wallet R w it) (max 1 (1:ℝ))=wallet R w it:=by ext v;simp [Stoop.radius]
  dsimp only at receipt
  rw [trimmed,heard fired] at receipt
  obtain ⟨support,pay⟩:=receipt
  refine ⟨support,?_⟩
  intro j uj ji
  have tariff:=(eventually_atTop.mp (WilsonThermometerMixedCorridorWallet.original R simple C cp d)).choose_spec f onset
    N cut per i t it (tf.trans (Nat.le_succ f)) length c w positive
  have gp:=ActualRunKernelPackets.regulator_pos R N per (f+1) cut
  have gi:=ActualRunKernelPackets.regulator_pos R N per (i+1) (by omega)
  have coarse:=WilsonLocalCompactRichPortUnits.compared R simple (i:=i+1) (m:=f+1) (by omega) cut per
  have credits:gt^(l+1)*weightBill c (wallet R w it) ≤ B:=by
    rw [pow_succ,mul_assoc]
    exact (mul_le_mul_of_nonneg_left tariff (pow_nonneg gp.le _)).trans income
  apply WilsonThermometerMixedFlatPrice.paid gp gi coarse _ (l+1) credits (pay j uj ji)
  unfold weightBill
  exact sum_nonneg fun s _=>div_nonneg (norm_nonneg _) (Poly.worth wp s).le
end YM.Integration.WilsonThermometerMixedCorridorReading
end
