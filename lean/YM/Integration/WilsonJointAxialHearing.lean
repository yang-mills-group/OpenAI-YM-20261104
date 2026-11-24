import YM.Integration.WilsonJointAxialOrdinary
import YM.Integration.WilsonThermometerEarlierHearing
import YM.Integration.WilsonFiniteProgramFieldBorel
import YM.Integration.WilsonReceivedWholeFieldHot

/-! The finite ordinary Wick program on the Borel field selected from all
original source positions. Its signed difference from the received Wilson
nominal can be tested against an integrable spectator at any older date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonJointAxialHearing
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

def angleOf {G : Gauge} {nn : Side} {V : Type} [Fintype V]
    (o : V → Site nn) (h : ℕ) (J : Voice G) (axes : Lattice.Order) (r g : ℝ)
    (U : Config G nn) : fieldDir G nn 1 :=
  Stationary.arm G nn 1 (WilsonCapturedPrimaryPotential.potential g
    (r • WilsonJointAxialWindow.direction o h J axes r U))

theorem measuredAngle {G : Gauge} {nn : Side} {V : Type} [Fintype V]
    (o : V → Site nn) (h : ℕ) (J : Voice G) (clear : Clear G J)
    (axes : Lattice.Order) (r g : ℝ) : Measurable (angleOf o h J axes r g) := by
  unfold angleOf WilsonCapturedPrimaryPotential.potential
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  apply measurable_pi_lambda
  intro e
  exact (((measurable_pi_apply ((Work.E03.poleEquiv nn).symm e)).comp
    (WilsonJointAxialWindow.measurable_direction o h J clear axes r)).const_smul r).const_smul g⁻¹

variable {G : Gauge} (R : Run G) {m i N per k : ℕ}
  (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
  (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
  (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ : ℕ → ℕ} (books : Mentor.Offices.Books D R.rolls Q φ) (hi : m ≤ i) (cut : i < N)
  (ahead : Mentor.Forecast D R.rolls Q φ books) {V : Type} [Fintype V] [DecidableEq V]
  {X : V → Type} [∀ v, AddCommGroup (X v)] [∀ v, Module ℝ (X v)]
  (actors : ∀ v, Set (X v)) (pieces : ∀ v, Submodule ℝ (X v)) (grades : V → ℕ)
  (order shelf seats : ℕ)
  (physical : Wallet actors → Config G (R.family.side (i+1) per) → Poly (Stock.census V))
  (P : WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead actors pieces grades
    order shelf seats i hi physical)

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead actors
  P.model order P.voter
local notation "oldG" => Coat.gStep (Ψ (i+1)).beta
local notation "lamps" => (rendered student (Ψ i).p oldG)
local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (order+shelf+2)
local notation "gf" => Coat.gStep (R.family.path.rep N per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i
local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)

open WilsonJointAxialRoster

open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade

open Push.AbsoluteSums

def feeFor {V : Type} [Fintype V] [DecidableEq V] {C : Census V}
    (s : C.Mode) (u : ℕ) (g E : ℝ) := (∑ h∈shards C s,
      (h.val.card:ℝ)*E*(g⁻¹+E)^h.val.card) + g^u*((shards C s).card:ℝ)

theorem fee_nonnegative {V : Type} [Fintype V] [DecidableEq V] {C : Census V}
    (s : C.Mode) (u : ℕ) {g E : ℝ} (hg : 0 ≤ g) (hE : 0 ≤ E) : 0 ≤ feeFor s u g E :=
  add_nonneg (Finset.sum_nonneg fun h _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg h.val.card) hE)
    (pow_nonneg (add_nonneg (inv_nonneg.mpr hg) hE) _))
      (mul_nonneg (pow_nonneg hg _) (Nat.cast_nonneg _))

include course cut in
theorem original (simple : G.Simple) {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (q : ℕ) {ε : ℝ} (ep : 0 < ε)
    (width : ∀ j k : ℕ, k ≤ j → ∀ b : ℝ, R.alloy.delay.betaEntry j ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) j)⁻¹ ^ 2) ≤ b)
    (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late : max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card V) n q ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width order shelf (Fintype.card V) ep) ≤ i)
    (finiteLate : max (WilsonReceivedAxialFinite.opening R simple q ep)
      (WilsonReceivedAxialFinite.massOpening R D grades order shelf seats (k:=k) simple width) ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) (fit : k ≤ stage) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let h := (WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let cold := House.chilly (G:=G) (plaquettes (placed).origin H) τ
    ∀ (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
      (tag : (R.family.path.levels.clock.op i per).Choices)
      (s : (Stock.census V).Mode) (u : ℕ), s.val.card+u ≤ order+1 →
      let issued := Air.craft P.model (fun b => (P.model b).paint x) grades (π (i+1)) tape
      let finite := fun U => (Order.value (gf:ℂ) (Order.ratio (Bulk.Fk
        ((RunFormalChain.fromRun R).step N i per cut) F tag issued
        (angleOf (placed).origin h J axes r gf U) order))).part s
      let E := ε*(regulatorRun R.family N per i)^q + ε*gf^order + ε*gf^q
      let fee := (∑ h∈shards (Stock.census V) s,
        (h.val.card:ℝ)*E*(gf⁻¹+E)^h.val.card) + gf^u*((shards (Stock.census V) s).card:ℝ)
      WilsonThermometerCompulsoryReturn.Heard R (top:=N) (cold.indicator
        (fun U => (Poly.toll P.w s:ℂ)*((Poly.pass (bare lamps x U)).part s - finite U))) fee := by
  intro H r τ h cold x F tag s u fitOrder issued finite E fee
  have Gs := WilsonReceivedSourceGross.landed R hk D Q π Γ Ψ books hi ahead actors pieces grades
    order shelf seats physical P
  letI : Countable P.modelIndex := P.modelCount
  letI students : Countable (Scene.Texts P.model
    (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry)) := Scene.crewC P.model
    (Pane.panel R.alloy i (R.alloy.B.a.S.oneStep i per).exact_size).ratio
    (Cruise.publish D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry)
    (Cruise.funded D R.rolls Q R.alloy φ books P.op (Oak.era R hk D Q π Γ hi P.op P.lesson)
      (R.alloy.B.a.S.oneStep i per).exact_size P.model order P.voter P.lesson.entry P.lesson.studied ahead)
  have left := @WilsonReceivedWholeFieldHot.borel _ _ _ _ _ _ _ _ _ _ lamps _ _ _ P.issued.earning.positive
    (show 0 ≤ (Ψ i).p.supportExponent+1+1 by linarith only [(Ψ i).p.exponent_pos]) Gs students x s
  have right : Measurable finite := (WilsonFiniteProgramFieldBorel.original
    ((RunFormalChain.fromRun R).step N i per cut) F tag issued gf order s).comp
      (measuredAngle (placed).origin h J clear axes r gf)
  have measurable : MeasurableSet cold := House.bath _
  let source : Config G (R.family.side i per) → ℂ := fun U =>
    (Poly.toll P.w s:ℂ) * ((Poly.pass (bare lamps x U)).part s - finite U)
  change WilsonThermometerCompulsoryReturn.Heard R (top:=N) (cold.indicator source) fee
  apply WilsonThermometerEarlierHearing.original R (f:=cold.indicator source) (cap:=fee) cut.le
    (show Measurable (cold.indicator source) from (measurable_const.mul (left.sub right)).indicator measurable)
  intro U
  by_cases onCold : U ∈ cold
  · rw [Set.indicator_of_mem onCold, show source U = _ * ((Poly.pass (bare lamps x U)).part s - finite U) from rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Poly.worth P.issued.earning.positive s).le]
    have rates := WilsonJointAxialOrdinary.selected R hk D Q π Γ Ψ course books hi cut ahead
      actors pieces grades order shelf seats physical P simple funded slow J clear axes q ep width law enrolled
      fund late finiteLate pass hospital narrow load fit U onCold
    exact rates.2.2.2.2.2 x F tag s u fitOrder
  · rw [Set.indicator_of_notMem onCold,norm_zero]
    have gg : 0 ≤ gf := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have gi : 0 ≤ regulatorRun R.family N per i := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have ge : 0 ≤ E := add_nonneg (add_nonneg (mul_nonneg ep.le (pow_nonneg gi _))
      (mul_nonneg ep.le (pow_nonneg gg _))) (mul_nonneg ep.le (pow_nonneg gg _))
    exact fee_nonnegative s u gg ge

end YM.Integration.WilsonJointAxialHearing
