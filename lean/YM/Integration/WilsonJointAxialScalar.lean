import YM.Integration.WilsonJointAxialHearing
import YM.Integration.WilsonJointAxialAbsolute
import YM.Integration.WilsonJointAxialMeasure

/-! A single pretuned linear combination of the complete ordinary Wilson
face table, on one healthy chart and against the true older marginal. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonJointAxialScalar
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

def opening {G : Gauge} {V : Type} [Fintype V] (R : Run G) (simple : G.Simple)
    (gate : WilsonReportingForestAngularReflection.posted R) (q degree K : ℕ) : ℕ :=
  (eventually_atTop.mp (WilsonJointAxialMeasure.missed (V:=V) R simple gate
    (invoice (Fintype.card V) (q+2*degree)) 1 K)).choose+1

private theorem missed_at {G : Gauge} {V : Type} [Fintype V] (R : Run G) (simple : G.Simple)
    (gate : WilsonReportingForestAngularReflection.posted R) (q degree K : ℕ) {i N per : ℕ}
    (late : WilsonJointAxialScalar.opening (V:=V) R simple gate q degree K ≤ i) (live : i ≤ N)
    (o : V → Site (R.family.side i per)) :
    let H := radius R (invoice (Fintype.card V) (q+2*degree)) 1 i
    (scene R.family.path N per i).real (House.chilly (G:=G) (plaquettes o H)
      (angularCut (R.family.path.levels.clock.hatBeta i)))ᶜ ≤ ((R.family.path.levels.clock.hatBeta i)⁻¹)^K := by
  let e := WilsonJointAxialMeasure.missed (V:=V) R simple gate (invoice (Fintype.card V) (q+2*degree)) 1 K
  have stageBound : (eventually_atTop.mp e).choose+1 ≤ i := late
  cases i with
  | zero => omega
  | succ j => exact (eventually_atTop.mp e).choose_spec j (Nat.le_of_succ_le_succ stageBound) N per live o

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
    (narrow : shelf ≤ R.alloy.B.a.clock.J i) (load : P.op.count ≤ Burn.horizon k+2) (fit : k ≤ stage)
    (gate : WilsonReportingForestAngularReflection.posted R) (K : ℕ)
    (rareLate : WilsonJointAxialScalar.opening (V:=V) R simple gate q n K ≤ i) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let h := (WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let cold := House.chilly (G:=G) (plaquettes (placed).origin H) τ
    ∀ (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
      (tag : (R.family.path.levels.clock.op i per).Choices)
      (faces : Finset (Stock.census V).Mode) (c : (Stock.census V).Mode → ℂ) (u : ℕ),
      (∀ s ∈ faces, s.val.card+u ≤ order+1) →
      let issued := Air.craft P.model (fun b => (P.model b).paint x) grades (π (i+1)) tape
      let expected := fun (s : (Stock.census V).Mode) U => (Order.value (gf:ℂ) (Order.ratio (Bulk.Fk
        ((RunFormalChain.fromRun R).step N i per cut) F tag issued
        (angleOf (placed).origin h J axes r gf U) order))).part s
      let E := ε*(regulatorRun R.family N per i)^q + ε*gf^order + ε*gf^q
      let Drow := (Spill.allOver (Ψ i).p)^(order+shelf+1)*
        (Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf)
      let delta := ∑ s∈faces,‖c s‖*(feeFor s u gf E / Poly.toll P.w s)
      let M := ∑ s∈faces,‖c s‖*(charge s Drow / Poly.toll P.w s)
      let difference := fun U => ∑ s∈faces,c s *
        ((Poly.pass (bare lamps x U)).part s - cold.indicator (expected s) U)
      ∀ j, (age : j ≤ i) →
        ∫ Z, ‖actualTransport R.family (N:=N) difference age Z‖ ∂scene R.family.path N per j ≤
          delta + ((R.family.path.levels.clock.hatBeta i)⁻¹)^K*M := by
  intro H r τ h cold x F tag faces c u fits issued expected E Drow delta M difference j age
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
  let nominal := fun (s : (Stock.census V).Mode) (U : Config G (R.family.side i per)) =>
    (Poly.pass (bare lamps x U)).part s
  have exponent : 0 ≤ (Ψ i).p.supportExponent+1+1 := by linarith only [(Ψ i).p.exponent_pos]
  have left (s) : Measurable (nominal s) := @WilsonReceivedWholeFieldHot.borel _ _ _ _ _ _ _ _ _ _
    lamps _ _ _ P.issued.earning.positive exponent Gs students x s
  have right (s) : Measurable (expected s) := (WilsonFiniteProgramFieldBorel.original
    ((RunFormalChain.fromRun R).step N i per cut) F tag issued gf order s).comp
      (measuredAngle (placed).origin h J clear axes r gf)
  have measurable : MeasurableSet cold := House.bath _
  have gg : 0 ≤ gf := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have gi : 0 ≤ regulatorRun R.family N per i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have ge : 0 ≤ E := add_nonneg (add_nonneg (mul_nonneg ep.le (pow_nonneg gi _))
    (mul_nonneg ep.le (pow_nonneg gg _))) (mul_nonneg ep.le (pow_nonneg gg _))
  have fundedRows (U : Config G (R.family.side i per)) (hc : U ∈ cold) (s) (hs : s∈faces) :
      ‖nominal s U - expected s U‖ ≤ feeFor s u gf E / Poly.toll P.w s := by
    have rates := WilsonJointAxialOrdinary.selected R hk D Q π Γ Ψ course books hi cut ahead
      actors pieces grades order shelf seats physical P simple funded slow J clear axes q ep width law enrolled
      fund late finiteLate pass hospital narrow load fit U hc
    apply (le_div_iff₀ (Poly.worth P.issued.earning.positive s)).mpr
    rw [mul_comm]
    exact rates.2.2.2.2.2 x F tag s u (fits s hs)
  have full (U : Config G (R.family.side i per)) (s) : ‖nominal s U‖ ≤ charge s Drow / Poly.toll P.w s := by
    apply (le_div_iff₀ (Poly.worth P.issued.earning.positive s)).mpr
    rw [mul_comm]
    exact WilsonReceivedWholeFieldHot.ordinary lamps P.issued.earning.positive exponent Gs x U s
  have hd (s : (Stock.census V).Mode) : 0 ≤ feeFor s u gf E / Poly.toll P.w s :=
    div_nonneg (fee_nonnegative s u gg ge) (Poly.worth P.issued.earning.positive s).le
  have hm (s : (Stock.census V).Mode) : 0 ≤ charge s Drow / Poly.toll P.w s := (norm_nonneg _).trans (full 1 s)
  have total := WilsonJointAxialAbsolute.older R cut.le faces c cold measurable nominal expected
    (fun s _ => left s) (fun s _ => right s) _ _ (fun s _ => hd s) (fun s _ => hm s)
    fundedRows (fun U s _ => full U s) j age
  have missed := missed_at R simple gate q n K rareLate cut.le (placed).origin
  have nonneg : 0 ≤ M := Finset.sum_nonneg fun s _ => mul_nonneg (norm_nonneg _) (hm s)
  exact total.trans (add_le_add (le_refl delta) (mul_le_mul_of_nonneg_right missed nonneg))

end YM.Integration.WilsonJointAxialScalar
