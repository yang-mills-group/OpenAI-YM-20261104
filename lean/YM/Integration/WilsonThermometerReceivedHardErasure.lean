import YM.Integration.WilsonThermometerOccupiedOlder
import YM.Integration.WilsonThermometerOccupiedHardOrder
import YM.Integration.WilsonMeasuredCompanionCorridor
import YM.Integration.WilsonThermometerOccupiedLinear
import YM.Integration.WilsonThermometerReceivedHardNodes

/-! Erase all occupied hard entries of the original finite three-mark source in a fixed older reading. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerReceivedHardErasure
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
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:(j:ℕ) → RG.Rep G (R.family.side j per))
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

variable (hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls bank φ)(ahead:Mentor.Forecast D R.rolls bank φ books)
  {X:Fin 3 → Type}[∀v,AddCommGroup (X v)][∀v,Module ℝ (X v)]
  (actors:∀v,Set (X v))(pieces:∀v,Submodule ℝ (X v))(grades:Fin 3 → ℕ)(order shelf seats:ℕ)(hf:m≤f)
  (physical:Affinity.Wallet actors → Config G (R.family.side (f+1) per) → Poly (J))
  (P:WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead actors pieces grades order shelf seats f hf physical)
local notation "Ω" => Oak.expenseReal R hk D bank π Γ books hf P.op P.lesson ahead order shelf
local notation "weights" => Stoop.radius P.w (Ω^6)
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hf P.op P.lesson ahead actors P.model order P.voter
local notation "posted" => Tint.Patrol.report student P.output (Coat.gStep (Ψ (f+1)).beta)
local notation "homes" => (P.passport.coarser (R.family.path.levels.clock.op f per).ratio).origin
local notation "heat" => R.alloy.B.a.clock.hatBeta (f+1)

include way D bank ticket π Γ course in
theorem original (floor:m ≤ u)(ui:u ≤ i)(it:i≤f)(cut:f+1≤N)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
    (sec:R.t 0 ≤ i)(slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (C:ℝ)(cp:0≤C)(d:ℕ)
    (onset:(eventually_atTop.mp (WilsonThermometerMixedCorridorWallet.original R simple C cp d)).choose ≤ f)
    (length:(f-i:ℕ) ≤ C*zf^d)(stage₀:∀(j:ℕ),i≤j → 3≤R.alloy.B.a.clock.J j)
    (fired:Affinity.Wallet actors)(s:(J).Mode)(occupied:s≠(J).quiet)
    (α:ℝ)(strength:(Ψ i).p.supportExponent≤α)
    (y:Site (It))(Z:Support (It))(center:y∈Z)(resident:∀v,sites R homes it v∈Z)(box:Z⊆halo (Ψ i).p.B {y})
    (rad:ℕ)(near:∀v,separation (sites R homes it v) y≤rad)(radius:rad≤(Ψ i).p.B)
    (p l:ℕ)(B:ℝ)(wallet:gt^l*(1/Poly.toll weights s)≤B)(warm:3≤heat)
    (stage:p+l+88+6*seats≤R.alloy.B.a.clock.J f):
    let real:=fun U=>(LocalComparison.actualPush R.family N per f (physical fired) U).part s
    let regular:=fun U=>(((Ψ f).eval U:ℂ) • Poly.pass ((posted).E.log fired U)).part s
    ∀ (j : ℕ), u ≤ j  →  ∀ (ji : j ≤ i),
      ‖read real j (ji.trans it)-read regular j (ji.trans it)‖≤
        30*(B*WilsonMeasuredCompanionCorridor.charge R α)*gt^p:=by
  intro real regular
  let q:=p+l+88
  let T:=heat^q/3
  obtain ⟨large,nodes,convert⟩:=WilsonThermometerOccupiedHardOrder.original R (per:=per) cut warm p l
  obtain ⟨soft,positive,raised,source⟩:=WilsonThermometerReceivedHardNodes.original R hk D bank π Γ Ψ course
    books hf cut ahead actors pieces grades order shelf seats physical P way q stage
  letI : Countable P.modelIndex:=P.modelCount
  letI : Countable P.outputIndex:=P.outputCount
  let Rows : Type := Scene.Texts P.model (Pane.panel R.alloy f ((R.alloy.B.a.S.oneStep f per).exact_size)).ratio (Cruise.publish D R.rolls bank R.alloy φ books P.op (Oak.era R hk D bank π Γ hf P.op P.lesson) ((R.alloy.B.a.S.oneStep f per).exact_size) P.model order P.voter P.lesson.entry)
  letI snapshots : Countable Rows :=
    Scene.crewC P.model _ (Cruise.publish D R.rolls bank R.alloy φ books P.op (Oak.era R hk D bank π Γ hf P.op P.lesson) ((R.alloy.B.a.S.oneStep f per).exact_size) P.model order P.voter P.lesson.entry) (Cruise.funded D R.rolls bank R.alloy φ books P.op (Oak.era R hk D bank π Γ hf P.op P.lesson) ((R.alloy.B.a.S.oneStep f per).exact_size) P.model order P.voter P.lesson.entry P.lesson.studied ahead)
  letI : Countable (Rows ⊕ P.outputIndex):=inferInstance
  have issued:=WilsonThermometerOccupiedOlder.original (K:=Rows ⊕ P.outputIndex) R simple way D bank ticket π Γ Ψ course
    floor ui it le_rfl cut gate sec slow ready early C cp d onset length stage₀ (posted) fired
    weights positive s occupied α strength y Z center resident box rad near radius soft T large
    (fun z hz=>raised z (hz.trans nodes))
  have ready:real=(fun U=>((posted).density fired U).part s):=congrArg
    (fun f0 : Config G (R.family.side f per) → Poly (J) => fun U=>(f0 U).part s) (source fired)
  intro j uj ji
  rw [ready]
  have nonneg:0≤WilsonMeasuredCompanionCorridor.charge R α:=mul_nonneg (pow_nonneg (by norm_num) _) (abs_nonneg _)
  exact convert (1/Poly.toll weights s) B (WilsonMeasuredCompanionCorridor.charge R α) _
    (one_div_nonneg.mpr (Poly.worth positive s).le) nonneg wallet (issued j uj ji)

end YM.Integration.WilsonThermometerReceivedHardErasure
