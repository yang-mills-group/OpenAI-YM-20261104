import YM.Integration.WilsonMeasuredCompanionCorridor

/-! The first genuine original step accepts the regular budget at the incoming support exponent. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionEntry
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


open WilsonMeasuredCompanionCorridor
local notation "senior" => ((R.family.path.levels.clock.op t per).ratio.parent)
local notation "clock" => R.alloy.B.a.clock
local notation "W" => (Ψ (t+1))
local notation "Kcap" => LocalComparison.forcedDivisor R.family (t+1)

include way D bank ticket π Γ course in
theorem first (upper:m ≤ t)(live:t<N)(stage:3≤(clock).J t)
    {X K:Type}[Countable K][Nonempty X]{o:Fin 3→Site (R.family.side (t+1) per)}
    (A:Gallery X K o (W) (J))(w:Fin 3→ℝ)(pos:∀v,0<w v)
    (income:A.Pays w (W).p.supportExponent 1 1):
    ∃(I':Type)(L:Gallery X I' ((senior) ∘ o) (Ψ t) (J)),Countable I' ∧
      L.E.Paid (Stoop.radius w (factor R t)) (Ψ t).p.B ((Ψ t).p.supportExponent+2) 1 ∧
      L.K.Paid (Stoop.radius w (factor R t)) (Ψ t).p.B (Ψ t).p.supportExponent
        (LocalComparison.forcedDivisor R.family t) ∧
      ∀x,L.density x=gust R.family.path N per (t+1) (A.density x) t (Nat.le_succ t):=by
  obtain ⟨I',L,hI,wide,tap,seen⟩:=WilsonReceivedGalleryEnlarged.original R way D bank π Γ Ψ course ticket
    upper live w pos A income stage (fun s=>by simpa using card_le_univ s.val)
  have dpos:0<factor R t:=zero_lt_one.trans_le (le_max_left ..)
  have reprice:(factor R t)⁻¹*rent R t≤1:=(inv_mul_le_one₀ dpos).2 (le_max_right ..)
  have budget:=Stoop.tighten w L.E pos (le_max_left 1 (rent R t)) wide
  have output:=Advent.force_bill R way π Γ Ψ course upper live (Nat.zero_le ((clock).J t))
  rw [Nat.cast_zero,neg_zero,Real.rpow_zero,one_mul] at output
  refine ⟨I',L,hI,?_,Stoop.leaves w L.K pos (le_max_left ..) (Hard.mono _ tap output),?_⟩
  · have soft:=Lamps.loan_monotone _ budget reprice
    rwa [show (Ψ t).p.supportExponent+1+1=(Ψ t).p.supportExponent+2 by ring] at soft
  · intro x
    rw [seen x,gust_step R.family.path N per (t+1) (A.density x) (Nat.lt_succ_self t),gust_base]
    rfl

include way D bank ticket π Γ course in
theorem one (floor:m ≤ u)(ui:u ≤ i)(it:i≤t)(tf:t+1≤f)(cut:f+1≤N)
    (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
    (sec:R.t 0 ≤ i)(slow:∀j,((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready:WilsonReportLampForecast.Ready R.family.path.levels)
    (early:(eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (C:ℝ)(cp:0≤C)(d:ℕ)
    (onset:(eventually_atTop.mp (WilsonThermometerMixedCorridorWallet.original R simple C cp d)).choose ≤ f)
    (length:(t-i:ℕ) ≤ C*zf^d)(stage₀:∀(j:ℕ),i≤j→3≤R.alloy.B.a.clock.J j)

    {X K:Type}[Countable K]{o:Fin 3→Site (R.family.side (t+1) per)}(A:Gallery X K o (W) (J))(x:X)
    (w:Fin 3→ℝ)(pos:∀v,0<w v)(s:(J).Mode)(occupied:s≠(J).quiet)
    (α:ℝ)(strength:(Ψ i).p.supportExponent ≤ α)
    (y:Site (It))(Z:Support (It))(center:y∈Z)(resident:∀j,sites R ((senior) ∘ o) it j∈Z)
    (box:Z⊆halo (Ψ i).p.B {y})(rad:ℕ)(near:∀j,separation (sites R ((senior) ∘ o) it j) y ≤ rad)
    (radius:rad ≤ (Ψ i).p.B)(income:A.Pays w (W).p.supportExponent 1 1):
    MeasureTheory.Integrable (A.density x) (prior G _) ∧
    ∀j,u ≤ j→∀ji:j ≤ i,gt^88*‖read (fun U=>(A.density x U).part s) j ((ji.trans it).trans (Nat.le_succ t))‖ ≤
      (1/Poly.toll (Stoop.radius w (factor R t)) s)*charge R α:=by
  letI:Nonempty X:=⟨x⟩
  have mt: m≤t:=floor.trans (ui.trans it)
  have live:t<N:=by omega
  obtain ⟨I',L,co,reg,hard,seen⟩:=first R way D bank ticket π Γ Ψ course mt live (stage₀ t it) A w pos income
  letI:Countable I':=co
  have wp (v:Fin 3):0<Stoop.radius w (factor R t) v:=
    div_pos (pos v) (zero_lt_one.trans_le (le_max_left ..))
  have got:=WilsonMeasuredCompanionCorridor.one R simple way D bank ticket π Γ Ψ course
    floor ui it ((Nat.le_succ t).trans tf) cut gate sec slow ready early C cp d onset length stage₀ L x
    (Stoop.radius w (factor R t)) wp s occupied α strength y Z center resident box rad near radius reg hard
  have law:=(course.1.walk (t+1) (mt.trans (Nat.le_succ t)) live).truep.valid
  have pay:=QuadraticLocal.Tariff.integrable (J) o w pos A x income (W).p.exponent_pos.le law
  refine ⟨pay,fun j uj ji=>?_⟩
  rw [←WilsonMeasuredCompanionTransport.through R (A.density x) pay s (Nat.le_succ t) (ji.trans it),←seen x]
  exact got.2 j uj ji

end YM.Integration.WilsonMeasuredCompanionEntry
