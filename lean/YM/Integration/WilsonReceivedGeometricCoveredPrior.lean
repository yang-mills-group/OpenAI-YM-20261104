import YM.Integration.WilsonReceivedGeometricFieldPrice
import YM.Integration.WilsonReceivedCloseCoveredWalletDates
import YM.Integration.WilsonMeasuredPostedComparison

/-! The true captured numerator and the independently named covered scalar on each
earlier original Wilson law, with its complete compulsory account kept on the same vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedGeometricCoveredPrior
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
open MeasureTheory WilsonLimitConstruction OPE.Therm WilsonJointAxialRoster WilsonReportingForestAngularFare
open WilsonMeasuredCoefficientTransport ConnectedActivityE6.SliceRows
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

local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "writer" => Air.craft student (fun s=>(student s).paint fired) ages (π i) tape₀
local notation "names" => (order+shelf+2)
/-- The actual compensated scalar tested on every older physical Wilson measure. -/
def Heard (singer : MSbar.Heath.Voice G) (axes : Lattice.Order) (q target sourcePower d₀ : ℕ)
    (ε wallet : ℝ) (c : (J).Mode → ℂ) (y : Site ((C).side i per))
    (K : Wallet actors → Stationary.Link G (R.family.side i per) → ℕ → Poly (J)) : Prop :=
    let H := WilsonRegisteredAffineHalo.radius R (WilsonJointAxialRoster.invoice 3 (q+2*names)) 1 i
    let r := WilsonRegisteredAxialRates.amplitude R singer H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let height := (WilsonDegreeFourInheritedRange.height R (q+2*names) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let cold := House.chilly (G:=G) (WilsonJointAxialRoster.plaquettes homes H) τ
    let A := fun U => WilsonCapturedPrimaryPotential.potential g
      (r • WilsonJointAxialWindow.direction homes height singer axes r U)
    let forecast := fun U=>∑s:(J).Mode,c s*WilsonCoveredOrdinaryPolynomial.evaluated order (K fired (A U)) (g:ℂ) s
    let withdrawn := fun U => take c (incomingAt U)
    let declared := cold.indicator forecast
    let filed := fun U=>take c (Poly.pass (WilsonRootedKioskOccupiedSlip.bare lamps fired U))
    let loss := sourcePower+(d₀*3+1)
    let fee₀ := WilsonReceivedCloseOrdinaryGrade.invoice (J) 3 0 (target+loss) 1+
      (4:ℝ)^(target+loss+1+2*names*3)*(Fintype.card (Multi.parts (J)).Mode)*((2:ℝ)^names)^3
    let principal := testPrice (F) * (|WilsonFullFaceSignedPower.inter * (Fintype.card (Multi.parts (J)).Mode:ℝ)*125| * wallet)
    let regular := |M 100| * wallet * (2+4^q)
    ∃ h:Coefficient (F) ((C).side i per), h.Format y (Y) (Ψ i) ∧
      h.remBound y (Ψ i) κ (regular*g^(target+1)) ∧ ‖h.x 0‖ ≤ principal*g^(target+1) ∧
      (∀U,h.density y (S) (Ψ i) U=withdrawn U - ((Ψ i).eval U:ℂ)*filed U) ∧
      let error := fun U=>withdrawn U/((Ψ i).eval U:ℂ) - declared U - account h (Ψ i) U/((Ψ i).eval U:ℂ)
      RG.Envelope error ∧ ∀ (j : ℕ) (age : j ≤ i),
        (∫U,‖actualTransport R.family (N:=N) error age U‖ ∂scene R.family.path N per j) ≤
          (wallet*fee₀+ε+principal+regular)*g^(target+1)

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
    (radius : rad≤(Ψ i).p.B) (box : Z⊆halo (Ψ i).p.B {y}) 
    (sourcePower d₀ : ℕ) (wallet : ℝ) (sold : ∀ s:(J).Mode,g^(d₀*s.val.card+1) ≤ Poly.toll P.w s)
    (coefficients : g^sourcePower * (∑s,‖c s‖) ≤ wallet) (target : ℕ)
    (surplus : target+1+(sourcePower+(d₀*3+1)+87) ≤ q)
    (saved : (eventually_atTop.mp (WilsonFullFaceSignedReserved.original R simple q)).choose ≤ i)
    {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T} (funded:FundedOriginalProperties.{u} simple η W)
    (singer:MSbar.Heath.Voice G) (clear:MSbar.Heath.Clear G singer) (axes:Lattice.Order)
    (strip:∀a j:ℕ,j≤a→∀b:ℝ,R.alloy.delay.betaEntry a≤b→Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon j) a)⁻¹^2)≤b)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D bank books)
    (fund:Volume.Fund D R.rolls bank φ books R.alloy.delay) (gate:WilsonReportingForestAngularReflection.posted R)
    (fit:k≤R.alloy.B.a.clock.J i) (accurate:ε*((3:ℝ)^q+2)≤1)
    (dates:WilsonReceivedCloseCoveredWalletDates.Ready R simple funded slow singer clear D strip ages
      order shelf seats k gate q target (sourcePower+(d₀*3+1)) wallet positive i)
    (K:Wallet actors → Stationary.Link G (R.family.side i per) → ℕ → Poly (J))
    (named:∀x A l,l≤order→K x A l = Air.discharge
      (Air.craft student (fun s=>(student s).paint x) ages (π i) tape₀) l (Stationary.arm G (R.family.side i per) 1 A)) :
    Heard R hk D bank π Γ Ψ books hi ahead order shelf seats actors pieces ages physical P fired
      singer axes q target sourcePower d₀ ε wallet c y K := by
  unfold Heard
  intro H r τ height cold A forecast withdrawn declared filed loss fee₀ principal regular
  have walk := course.1.walk i hi cut.le
  have strength : (Ψ i).p.supportExponent ≤ 100 :=
    ((congrArg BudgetPoint.supportExponent walk.truep.point).trans (funded.2.1.paid.fixed i)).le
  obtain ⟨h,fmt,paid,rep,head⟩ := WilsonReceivedGeometricFieldPrice.original R simple cut hk D bank π Γ Ψ course
    books hi ahead order shelf seats actors pieces ages physical P fired gradeCap way station sec slow ready early late
    pass hospital narrow load q force deep aged positive opened half retained c y Z center homes_in rad near radius box
    100 strength sourcePower d₀ wallet sold coefficients (target+1) surplus saved
  have money : ‖h.x 0‖ ≤ principal*g^(target+1) := by simpa only [principal,mul_assoc] using head
  refine ⟨h,fmt,paid,money,rep,?_⟩
  obtain ⟨reach,finiteReach,clock,rare,winding⟩ := dates i le_rfl
  have reserve : target+loss+1+Fintype.card (Fin 3) ≤ q := by dsimp only [loss]; change target+(sourcePower+(d₀*3+1))+1+3 ≤ q;omega
  have room : q ≤ order:=by omega
  have arity (s : (J).Mode) (_ : s∈(Finset.univ:Finset (J).Mode)) : s.val.card ≤ 3 :=by
    simpa using Finset.card_le_univ s.val
  have quote := WilsonReceivedCoveredSignedWallet.original R hk D bank π Γ Ψ course books hi cut ahead actors pieces ages
    order shelf seats physical P simple funded slow singer clear axes q positive strip law enrolled fund reach finiteReach
    pass hospital narrow load fit gate target sourcePower d₀ 3 reserve room accurate clock rare wallet winding K named
    sold fired Finset.univ c arity coefficients
  have env : RG.Envelope (fun U=>filed U-declared U) := quote.1
  have base : (∫U,‖filed U-declared U‖ ∂scene R.family.path N per i) ≤ (wallet*fee₀+ε)*g^(target+1) := by
    simpa only [actualTransport_base R.family R.makes cut.le,fee₀,loss,filed,declared,forecast,A,cold,height,τ,r,H,take,Fintype.card_fin] using quote.2 i le_rfl
  have seen := WilsonMeasuredPostedComparison.earlier R simple π Γ Ψ course hi cut.le y h fmt paid
    withdrawn filed declared rep env base
  exact ⟨seen.1,fun j age=>(seen.2 j age).trans (by dsimp only [regular] at *; nlinarith only [money])⟩

end YM.Integration.WilsonReceivedGeometricCoveredPrior
