import YM.Integration.WilsonReceivedEarnedFaceSum
import YM.Integration.WilsonGeometricSignedOrder
import YM.Integration.WilsonGeometricSignedPrimary

/-! Buy the complete signed three-face numerator minus its own unmasked pupil on the
actual captured field using the previously sold close-window radii. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedGeometricFieldPrice
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
variable {G : Gauge} (R : Run G) (simple : G.Simple) {m i N per k : ℕ}
  (cut : i<N)
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m ≤ i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
variable {X : Fin 3 → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀v, Set (X v)) (pieces : ∀v, Submodule ℝ (X v)) (ages : Fin 3 → ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly J)
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead actors pieces ages
    order shelf seats i hi physical)
  (fired : Wallet actors)
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "Ω" => Oak.expenseReal R hk D bank π Γ books hi P.op P.lesson ahead order shelf
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "g" => Coat.gStep (R.family.path.rep N per (i+1)).beta

local notation "homes" => (P.passport.coarser (sheet).ratio).origin

local notation "C" => R.family
local notation "F" => R.family.labels.level 0
local notation "S" => R.family.localSection 0
local notation "Y" => R.family.params
local notation "incomingAt" => LocalComparison.actualPush R.family N per i (physical fired)

local notation "debt" => (fun (ε:ℝ) (p:ℕ)=>(8*Ω^P.op.count)*P.rent+ε*g^p)
local notation "B" => ((2:ℝ)^(order+shelf+2)+4)
local notation "M" => (fun (α:ℝ)=>WilsonFullFaceSignedPower.constants (S) (Y) α B)

include course cut in
theorem original (gradeCap : (∑j,ages j) ≤ 14) (way : WayStation R.kit) (station : WilsonCenteredCaptureClock.first R simple ≤ i)
    (sec : R.t 0 ≤ i)
    (slow : ∀ j, ((R.family.S.block j).val:ℝ) ≤ Real.log (RG16.Lambda R.family.path.levels j))
    (ready : WilsonReportLampForecast.Ready R.family.path.levels)
    (early : (eventually_atTop.mp (WilsonCenteredReporterClock.original R simple slow ready)).choose ≤ i)
    (late : (eventually_atTop.mp (WilsonRootedKioskPostRadius.original R simple)).choose ≤ i)
    (pass : Pass D bank R.alloy R.kit) (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf≤R.alloy.B.a.clock.J i) (load : P.op.count≤Burn.horizon k+2)
    (q : ℕ) (force : q≤R.alloy.B.a.clock.J i) (deep : 2*(q+1)+8≤order) (aged : q+4≤3*k+2)
    {ε : ℝ} (positive : 0<ε) (opened : WilsonFirstReceivedEarnedFee.opening R simple P.op.count q order k deep aged positive ≤ i)
    (half : ε≤1/2) (retained : 8*Ω^P.op.count*P.rent≤(1/2)*g^q) (c : (J).Mode → ℂ) (y : Site ((C).side i per)) (Z : Support ((C).side i per)) (center : y∈Z)
    (homes_in : ∀j:Fin 3,homes j∈Z) (rad : ℕ) (near : ∀j:Fin 3,separation (homes j) y≤rad)
    (radius : rad≤(Ψ i).p.B) (box : Z⊆halo (Ψ i).p.B {y}) (α : ℝ) (strength : (Ψ i).p.supportExponent≤α)
    (sourcePower d₀ : ℕ) (wallet : ℝ) (sold : ∀ s:(J).Mode,g^(d₀*s.val.card+1) ≤ Poly.toll P.w s)
    (coefficients : g^sourcePower * (∑s,‖c s‖) ≤ wallet) (target : ℕ)
    (surplus : target+(sourcePower+(d₀*3+1)+87) ≤ q)
    (saved : (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i) :
    let nominal := fun U=>Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U)
    ∃ h : Coefficient (F) ((C).side i per), h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ (|M α| * wallet * (2+4^q) * g^target) ∧
      (∀U,h.density y (S) (Ψ i) U=take c (incomingAt U)-
          ((Ψ i).eval U:ℂ)*take c (nominal U)) ∧
      ‖h.x 0‖ ≤ testPrice (F) *
        (|WilsonFullFaceSignedPower.inter * (Fintype.card (Multi.parts (J)).Mode:ℝ)*125| * wallet * g^target) := by
  intro nominal
  have actual := course.1.walk (i+1) (Nat.le_succ_of_le hi) cut
  have good : 0<g := (congrArg Coat.gStep actual.beta) ▸ P.issued.Waffle.soon.1
  have low : g≤1 := (congrArg Coat.gStep actual.beta) ▸ P.issued.Waffle.soon.2.1
  have qp : 0≤g^q:=pow_nonneg good.le q
  have fund : debt ε q≤1*g^q := by
    dsimp only
    have e:=mul_le_mul_of_nonneg_right half qp
    linarith
  have small : debt ε q≤1 := by
    simpa only [one_mul] using fund.trans (mul_le_one₀ le_rfl (pow_nonneg good.le q) (pow_le_one₀ good.le low))
  have char (s:(J).Mode) (_ : s∈(Finset.univ:Finset (J).Mode)) : s.val.card ≤ 3 :=by
    simpa using Finset.card_le_univ s.val
  have bill : g^(sourcePower+(d₀*3+1)) * weightBill c P.w ≤ wallet :=
    (WilsonReceivedEarnedFaceSum.original P.w good low d₀ 3 sourcePower sold Finset.univ c char).trans coefficients
  obtain ⟨h,fmt,fee,rep,scalar,size⟩ := WilsonGeometricSignedOrder.original (d:=0) R simple cut hk D bank π Γ Ψ
    course books hi ahead order shelf seats actors pieces ages physical P fired gradeCap way station sec slow ready early late
    pass hospital narrow load q q force deep aged positive opened small c y Z center homes_in rad near radius box α strength
    (sourcePower+(d₀*3+1)) wallet 1 bill target surplus fund saved
  refine ⟨h,fmt,?_,rep,?_⟩
  · simpa only [show (1:ℝ)+4^q+1=2+4^q by ring] using fee
  · have main := WilsonGeometricSignedPrimary.unit h _ scalar size
    have entry : ‖h.x 0‖≤(F).coeffSize h.x :=
      Finset.single_le_sum (fun j _=>norm_nonneg (h.x j)) (Finset.mem_univ 0)
    simpa only [mul_one] using entry.trans main

end YM.Integration.WilsonReceivedGeometricFieldPrice
