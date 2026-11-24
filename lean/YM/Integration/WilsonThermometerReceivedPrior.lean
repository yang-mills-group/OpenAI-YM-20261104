import YM.Integration.WilsonMeasuredPostedComparison
import YM.Integration.WilsonReceivedCoveredWallet
import YM.Integration.WilsonThermometerCenteredWeight
import YM.Integration.WilsonThermometerCourseIntake

/-! The eight actual cutoff faces share one compensating ordinary table and one original lower hard account.
The landed paper polynomial is evaluated on the measured local Wilson field, with its own signed total-degree truncation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerReceivedPrior
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare
open scoped Classical BigOperators Topology

open MeasureTheory Exterior ConnectedActivityE6.SliceRows

open RG16.Literal Next.Rank Next.UVStress MergeProof.East OriginalForcedAddresses Exterior
open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open Primitives.GCC.Anchor WilsonFiniteOrdinaryInverse WilsonMeasuredCoefficientTransport
open FVA1 Function MeasureTheory Planned.GuardedAtom Extra.Histories Next.Foundations
local notation "J₃" => Stock.census (Fin 3)
variable {G : Gauge} (R : Run G) (A : Group R.family 6) (simple : G.Simple) {m i N per k : ℕ}
  (cut : i<N) (o : Positions (Fin 3) (R.family.side N per))
  (hk : Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (bank : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls bank φ) (hi : m ≤ i)
  (ahead : Mentor.Forecast D R.rolls bank φ books) (order shelf seats : ℕ)
local notation "ages" => (fun j:Fin 3=>(WilsonPositionThermometerGradedSource.grade j).val)
local notation "actual" => offered R A simple cut o
variable (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D bank π Γ Ψ books ahead disks sectors ages
  order shelf seats i hi (offered R A simple cut o))
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "student" => Oak.student (n:=per) R hk D bank π Γ books hi P.op P.lesson ahead disks
  P.model order P.voter
local notation "I" => (R.family.path.levels.clock.op i per)
local notation "placed" => P.passport.coarser (I).ratio
local notation "n" => (order+shelf+2)
local notation "gs" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "W₀" => (Ψ i)
local notation "κ" => LocalComparison.forcedDivisor R.family i
local notation "roster" => Air.craft student (fun v=>(student v).paint fired) ages (π i)
  (AllOrder.Floe.Step.tape (Burn.horizon k+2))
local notation "lamps" => rendered student (Ψ i).p (Coat.gStep (Ψ (i+1)).beta)
open WilsonJointAxialRoster WilsonJointAxialHearing WilsonReceivedWholeFieldHot

include course cut in
theorem original {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (width : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D bank books)
    (fund : Volume.Fund D R.rolls bank φ books R.alloy.delay)
    (late : max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) n q ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width order shelf (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate : max (WilsonReceivedAxialFinite.opening R simple q ep)
      (WilsonReceivedAxialFinite.massOpening R D ages order shelf seats (k:=k) simple width) ≤ i)
    (pass : Pass D bank R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls bank R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) (fit : k ≤ stage)
    (gate : WilsonReportingForestAngularReflection.posted R) (p l : ℕ)
    (reserve : p+(3+l)+1+Fintype.card (Fin 3) ≤ q) (headroom : q ≤ order)
    (accuracy : ε*((3:ℝ)^q+2) ≤ 1)
    (clockLate : (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (rareLate : WilsonJointAxialScalar.opening (V:=Fin 3) R simple gate q n (p+(3+l)+1+2*n*(Fintype.card (Fin 3))) ≤ i)
    (winding : (eventually_atTop.mp (WilsonCoveredOrdinaryWeightedPost.original R simple D φ ages
      width order shelf k seats 0 (Fintype.card (Fin 3)) (3+l) (p+1) 1 1 (fee (J₃)) zero_le_one ep)).choose ≤ i)
    (aperture : gs^l ≤ Poly.toll P.w full) (Q₀ : Poly (J₃))
    (inverse : Poly.price (fun v=>gs*P.w v) (inverseMass Q₀)≤fee (J₃))
    (y : Site (R.family.side i per)) (h₀ : Coefficient F₀ (R.family.side i per))
    (fmt : h₀.Format y R.family.params W₀) {M:ℝ} (paid : h₀.remBound y W₀ κ M)
    (represented : ∀U,h₀.density y S₀ W₀ U=
      (total (incoming R A simple cut.le o U) Q₀).part full-
      ((W₀).eval U:ℂ)*(total (Poly.pass (bare lamps fired U)) Q₀).part full) :
    let H := radius R (invoice (Fintype.card (Fin 3)) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let k₀ := (WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let cold := House.chilly (G:=G) (plaquettes (placed).origin H) τ
    let angle := WilsonJointAxialHearing.angleOf (placed).origin k₀ J axes r gs
    let published := fun (s : (J₃).Mode) U=>WilsonCoveredOrdinaryPolynomial.evaluated order
      (fun d=>Air.discharge roster d (angle U)) (gs:ℂ) s
    let original := fun U=>(total (incoming R A simple cut.le o U) Q₀).part full/((W₀).eval U:ℂ)
    let declared := fun U=>∑s:(J₃).Mode,weight Q₀ s*(cold.indicator (published s) U)
    let error := fun U=>original U-declared U-account h₀ W₀ U/((W₀).eval U:ℂ)
    let D₀ := WilsonReceivedCloseOrdinaryGrade.invoice (J₃) (Fintype.card (Fin 3)) 0 (p+(3+l)) 1+
      (4:ℝ)^(p+(3+l)+1+2*n*(Fintype.card (Fin 3)))*(Fintype.card (Multi.parts (J₃)).Mode)*
        ((2:ℝ)^n)^(Fintype.card (Fin 3))
    RG.Envelope error ∧ ∀ (j:ℕ) (age : j ≤ i),
      (∫U,‖actualTransport R.family (N:=N) error age U‖ ∂scene R.family.path N per j)≤
        (fee (J₃)*D₀+ε)*gs^(p+1)+(‖h₀.x 0‖+M) := by
  intro H r τ k₀ cold angle published original declared error D₀
  have clock := (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose_spec i clockLate N per cut
  have weighted := WilsonThermometerCenteredWeight.original Q₀ P.w P.salary.positive clock.1 clock.2.1 l aperture inverse
  have quoted := WilsonReceivedCoveredWallet.original R hk D bank π Γ Ψ course books hi cut ahead disks sectors ages
    order shelf seats (offered R A simple cut o) P simple funded slow J clear axes q ep width law enrolled fund late
    finiteLate pass hospital narrow load fit gate p (3+l) reserve headroom accuracy clockLate rareLate _ winding
    fired univ (weight Q₀) (fee (J₃)) weighted le_rfl
  let filed := fun U=>(total (Poly.pass (bare lamps fired U)) Q₀).part full
  let each := fun U=>∑s:(J₃).Mode,weight Q₀ s*((Poly.pass (bare lamps fired U)).part s-cold.indicator (published s) U)
  have eq : (fun U=>filed U-declared U)=each := by
    funext U
    dsimp only [filed,declared,each]
    simp only [WilsonThermometerCenteredAlgebra.affine,mul_sub,Finset.sum_sub_distrib]
  have env : RG.Envelope (fun U=>filed U-declared U) := eq ▸ quoted.1
  have expense : (∫U,‖filed U-declared U‖ ∂scene R.family.path N per i)≤(fee (J₃)*D₀+ε)*gs^(p+1) := by
    change (∫U,‖(fun V=>filed V-declared V) U‖ ∂scene R.family.path N per i)≤_
    rw [eq]
    simpa only [actualTransport_base R.family R.makes cut.le] using quoted.2 i le_rfl
  exact WilsonMeasuredPostedComparison.earlier R simple π Γ Ψ course hi cut.le y h₀ fmt paid
    (fun U=>(total (incoming R A simple cut.le o U) Q₀).part full) filed declared represented env expense

end YM.Integration.WilsonThermometerReceivedPrior
