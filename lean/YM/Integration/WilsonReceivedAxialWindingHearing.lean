import YM.Integration.WilsonCoveredOrdinaryMeasured
import YM.Integration.WilsonCoveredOrdinarySpecificPost
import YM.Integration.WilsonJointAxialRefund

/-! A fixed signed collection of ordinary subwords can test the finite-minus-covered
winding on the local axial gauge of each incoming Wilson configuration. The signed
weights stay fixed under all the older conditional integrations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedAxialWindingHearing
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

open WilsonJointAxialHearing WilsonReceivedWholeFieldHot


local notation "head" x:max => Air.craft P.model (fun v=>(P.model v).paint x) grades (π (i+1)) tape
local notation "writer" x:max => Air.craft student (fun v=>(student v).paint x) grades (π i) tape
local notation "strip" => ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
  Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b

include course in
theorem original (simple : G.Simple) {η : ℝ} {T : Campaign R} {W : Campaign.Pillars R T}
    (funded : FundedOriginalProperties.{u} simple η W)
    (slow : ∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J : Voice G) (clear : Clear G J) (axes : Lattice.Order) (hearing : ℕ) {ε : ℝ} (ep : 0 < ε)
    (width : strip) (law : VowsR.LawScroll G φ) (enrolled : VowsR.Chamber law R.kit D Q books)
    (fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late : WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card V) n hearing ep ≤ i)
    (pass : Pass D Q R.alloy R.kit)
    (hospital : MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow : shelf ≤ stage) (load : P.op.count ≤ Burn.horizon k+2) (fit : k ≤ stage)
    (a v w q : ℕ) (C : ℝ)
    (winding : (eventually_atTop.mp (WilsonCoveredOrdinarySpecificPost.original R simple D φ grades
      width order shelf k seats 0 a v w q 1 1 C zero_le_one ep)).choose ≤ i)
    (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
    (tag : (R.family.path.levels.clock.op i per).Choices) (rows : Finset (Stock.census V).Mode)
    (c : (Stock.census V).Mode → ℂ)
    (sizes : ∀s∈rows, s.val.card ≤ a ∧ gf^v ≤ Poly.toll P.w s)
    (paid : gf^w*(∑s∈rows,‖c s‖) ≤ C) :
    let H := radius R (invoice (Fintype.card V) (hearing+2*n)) 1 i
    let r := amplitude R J H N per i
    let h := (WilsonDegreeFourInheritedRange.height R (hearing+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let cold := House.chilly (G:=G) (plaquettes (placed).origin H)
      (angularCut (R.family.path.levels.clock.hatBeta i))
    let angle := WilsonJointAxialHearing.angleOf (placed).origin h J axes r gf
    let source := fun U => ∑s∈rows,c s*(Order.value (gf:ℂ) (Order.ratio
      (Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag (head x) (angle U) order))).part s
    let predicted := fun U => ∑s∈rows,c s*WilsonCoveredOrdinaryPolynomial.evaluated order
      (fun d=>Air.discharge (writer x) d (angle U)) (gf:ℂ) s
    let err := cold.indicator (fun U => source U-predicted U)
    Measurable err ∧ (∀U,‖err U‖≤ε*gf^q) ∧
      WilsonThermometerCompulsoryReturn.Heard R (top:=N) err (ε*gf^q) := by
  intro H r h cold angle source predicted err
  let program := (RunFormalChain.fromRun R).step N i per cut
  have axial : Measurable angle := WilsonJointAxialHearing.measuredAngle (placed).origin h J clear axes r gf
  have borel : Measurable err := (Measurable.sub (Finset.measurable_fun_sum _ (fun s _ =>
    measurable_const.mul ((WilsonFiniteProgramFieldBorel.original program F tag (head x) gf order s).comp axial)))
    (Finset.measurable_fun_sum _ (fun s _ => measurable_const.mul
      ((WilsonCoveredOrdinaryMeasured.original (writer x) order (gf:ℂ) s).measurable.comp axial)))).indicator (House.bath _)
  have restore := (eventually_atTop.mp (WilsonCoveredOrdinarySpecificPost.original R simple D φ grades width
    order shelf k seats 0 a v w q 1 1 C zero_le_one ep)).choose_spec i winding hk fit Q π Γ Ψ course books law
      enrolled fund hi cut ahead actors pieces physical P x
  have bound (U) : ‖err U‖ ≤ ε*gf^q := by
    by_cases on : U∈cold
    · have invoice := WilsonJointAxialRoster.selected R hk D Q π Γ Ψ course books hi cut ahead actors pieces
        grades order shelf seats physical P simple funded slow J clear axes hearing ep late pass hospital narrow load U on
      let ξ := WilsonJointAxialWindow.direction (placed).origin h J axes r U
      obtain ⟨z,zs,admitted⟩ := WilsonReceivedAxialFinite.room R π Γ Ψ course hi cut ξ invoice.2.2.1 invoice.1 invoice.2.1
      have quote := restore (WilsonCapturedPrimaryPotential.potential gf (r • ξ)) z zs admitted F tag
      rw [show err U = source U-predicted U from Set.indicator_of_mem on _]
      exact quote.2 rows c sizes paid
    · rw [show err U=0 from Set.indicator_of_notMem on _]
      rw [norm_zero]
      exact mul_nonneg ep.le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  exact ⟨borel,bound,WilsonThermometerEarlierHearing.original R cut.le borel bound⟩

end YM.Integration.WilsonReceivedAxialWindingHearing
