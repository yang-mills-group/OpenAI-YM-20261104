import YM.Integration.WilsonThermometerPlantedScalar
import YM.Integration.WilsonThermometerUnitFilingSpan

/-! Two older scalar readings of the complete designated three-field ordinary
program, on the original positive Wilson history at its purchased fee. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingPupil
open FVA1 Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Planned.GuardedAtom Push.Local Source Labels Extra.Histories Next.Foundations
open scoped Classical BigOperators Topology

open Push.AbsoluteSums WilsonFiniteOrdinaryInverse Primitives.GCC.Anchor

open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
local notation "J" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m i N per k : ℕ}
  (cut : i<N) (o : Positions (Fin 3) (R.family.side N per))
  (hk : Burn.horizon k+2    ≤    R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m   ≤   i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
local notation "ages" => (fun j:Fin 3=>(WilsonPositionThermometerGradedSource.grade j).val)
local notation "actual" => offered R A simple cut o
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead disks sectors ages
  order shelf seats i hi (offered R A simple cut o))
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead disks
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "fig" => Oak.figureReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "gauge" => (Tint.Patrol.report student P.output oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "width" => ((Ψ i).p.supportExponent+1+1)
local notation "modelFee" => Invoice.price (Ψ i).p (fig).mist (order+shelf+1) P.op.count width (fig).limitC G
local notation "homes" => (P.passport.coarser (sheet).ratio).origin
local notation "configuration" => Config G (R.family.side i per)
local notation "value" => LocalComparison.actualPush R.family N per i


local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "μ" => (R.family.path.levels.params i).columns
local notation "rep" => R.family.path.rep N per i
local notation "cash" => modelFee*((fig).produce (sheet).ratio.count*P.cost)
local notation "raw" => (((2:ℝ)^(order+shelf+1)/(oldG)^15)*cash)
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "rel" => R.alloy.B.a.clock.forcedAllowance i
open private rem_nonneg from YM.Integration.WilsonThermometerUnitFilingStops

/-- The same v on every upper cutoff and period. -/
def first (slow:∀j,((C).S.block j).val ≤ Real.log (RG16.Lambda (C).path.levels j)) (u d q:ℕ):ℕ:=
  (eventually_atTop.mp (WilsonThermometerUnitFilingSpan.original R simple slow u d q)).choose

def earlier (slow:∀j,((C).S.block j).val ≤ Real.log (RG16.Lambda (C).path.levels j))
    (u d q i:ℕ) (aged:first R simple slow u d q ≤ i) : ℕ:=
  ((eventually_atTop.mp (WilsonThermometerUnitFilingSpan.original R simple slow u d q)).choose_spec i aged).choose

include course cut in
theorem original (ref : (C).ref 0  ≤  i) (sec : R.t 0 ≤ i) (station : WilsonCenteredCaptureClock.first R simple  ≤  i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ)  ≤  Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose  ≤  i)
    (pass : Pass D bank R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf   ≤   R.alloy.B.a.clock.J i) (load : P.op.count   ≤   Burn.horizon k+2)
    (Z : Support ((C).side i per)) (center : (0:Site ((C).side i per))∈Z)
    (anchors : ∀j, (homes) j∈Z) (rad : ℕ) (near : ∀ j,separation ((homes) j) 0 ≤ rad)
    (radius : rad ≤ (rep).p.B) (box : Z⊆halo (rep).p.B {0}) (α : ℝ) (strength : (rep).p.supportExponent ≤ α)
    (Q : Poly (J)) (loss : ℕ) (fullPrice : g^loss ≤ Poly.toll P.w full)
    (inverse : Poly.price (fun v=>g*P.w v) (inverseMass Q) ≤ fee J)
    (u q:ℕ) (cu:(C).ref 0≤u) (deployed:first R simple slow u (3+loss+61) q ≤ i)
    (ou:Trace.Physical.GermGraph.Opened C 0 u per)
    (ov:Trace.Physical.GermGraph.Opened C 0 (earlier R simple slow u (3+loss+61) q i deployed) per) :
    let v:=earlier R simple slow u (3+loss+61) q i deployed
    let M:=WilsonPlantedOrdinaryHalo.master (S) (Y) α ((2:ℝ)^(order+shelf+2))
    let A₀ : Config G ((C).side i per)→ℂ := fun U=>((rep).eval U:ℂ)*
        (total (Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)) Q).part full
    ∃ (uv:u≤v) (vi:v ≤ i),
      ‖WilsonThermometerUnitFilingCoarse.reading R (N:=N) A₀ u (uv.trans vi)-
        WilsonThermometerUnitFilingCoarse.reading R (N:=N) A₀ v vi‖ ≤ 40*(2*(fee (J)*M)+1)*g^q := by
  intro v M A₀
  have chosen:=((eventually_atTop.mp
      (WilsonThermometerUnitFilingSpan.original R simple slow u (3+loss+61) q)).choose_spec i deployed).choose_spec
  change u≤v ∧ v < i ∧ _ at chosen
  obtain ⟨uv,vi,_,rates⟩:=chosen
  obtain ⟨_,cashRate⟩:=rates N per cut
  have gpos:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson (Nat.succ_le_of_lt cut)))
  have loan:=WilsonThermometerPlantedScalar.original R A simple cut o hk D bank π Γ Ψ course books hi ahead order
    shelf seats P ref sec station slow ready early late pass hospital narrow load 0 Z center anchors rad
    near radius box α strength Q loss fullPrice inverse
  have rp:0≤fee (J)*M/g^(3+loss+61):=rem_nonneg loan
  have amp:0≤fee (J)*M:=by
    have zz:=mul_nonneg rp (pow_nonneg gpos.le (3+loss+61))
    rwa [div_mul_cancel₀ _ (pow_pos gpos _).ne'] at zz
  have stable:=WilsonThermometerUnitFilingStops.two_stops R simple cu uv vi.le cut.le ou ov loan
  refine ⟨uv,vi.le,stable.trans ?_⟩
  let E:=fee (J)*M
  let d:=3+loss+61
  let Δ:=(C).S.scale i-(C).S.scale v
  change 2*WilsonMacroscopicRichCaptureFilingBudget.capital C i (E/g^d) 1*Real.exp (-Δ/8)
      ≤ 40*(2*E+1)*g^q
  calc
    _ = 8*(1+((C).path.levels.params i).columns)*(2*(E/g^d)+1)*Real.exp (-Δ/8) := by
        unfold WilsonMacroscopicRichCaptureFilingBudget.capital
        ring
    _ ≤ _ := cashRate E amp

end YM.Integration.WilsonThermometerUnitFilingPupil
