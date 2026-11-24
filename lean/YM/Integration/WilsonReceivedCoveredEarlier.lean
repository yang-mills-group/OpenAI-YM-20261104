import YM.Integration.WilsonReceivedAxialWindingHearing
import YM.Integration.WilsonReceivedFiniteOrdinaryEnvelope

/-! The independent covered ordinary polynomial and the physical unmasked pupil are
compared on every previous normalized Wilson law, on the same measured post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCoveredEarlier
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

private theorem joined {G : Gauge} (R : Run G) {i N per : ℕ} (live : i ≤ N)
    (X Y : Config G (R.family.side i per) → ℂ) (hx : RG.Envelope X) (hy : Measurable Y)
    (B K : ℝ) (cost : (∫U, ‖X U‖ ∂scene R.family.path N per i) ≤ B) (price : ∀U, ‖Y U‖ ≤ K) :
    RG.Envelope (fun U=>X U+Y U) ∧ ∀j, (age:j ≤ i) →
      (∫U, ‖actualTransport R.family (N:=N) (fun V=>X V+Y V) age U‖ ∂scene R.family.path N per j) ≤ B+K := by
  let μ := scene R.family.path N per i
  haveI : IsProbabilityMeasure μ := OPE.Therm.probability (H:=R.family.path) (p:=per) R.makes.wilson live
  obtain ⟨mx,M,hM⟩ := hx
  have both : RG.Envelope (fun U=>X U+Y U) := ⟨mx.add hy,M+K,fun U=>(norm_add_le ..).trans (add_le_add (hM U) (price U))⟩
  refine ⟨both,fun j age => ?_⟩
  have ix : Integrable X μ := Integrable.of_bound mx.aestronglyMeasurable M (ae_of_all _ hM)
  have iy : Integrable Y μ := Integrable.of_bound hy.aestronglyMeasurable K (ae_of_all _ price)
  calc
    _ ≤ ∫U,‖X U+Y U‖ ∂μ := ActualWilsonAbsoluteTransport.first R.family R.makes live
      (ActualWilsonAbsoluteTransport.weighted R.family R.makes live both) age
    _ ≤ ∫U, ‖X U‖+K ∂μ := integral_mono (ix.add iy).norm (ix.norm.add (integrable_const _))
      (fun U=>(norm_add_le ..).trans (add_le_add le_rfl (price U)))
    _ ≤ B+K := by simpa only [integral_add ix.norm (integrable_const _),integral_const,probReal_univ,one_smul] using add_le_add cost (le_refl K)

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
    (gate : WilsonReportingForestAngularReflection.posted R) (p loss : ℕ)
    (reserve : p+loss+1+Fintype.card V ≤ q) (headroom : q ≤ order)
    (accuracy : ε*((3:ℝ)^q+2) ≤ 1)
    (clockLate : (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose ≤ i)
    (rareLate : WilsonJointAxialScalar.opening (V:=V) R simple gate q n (p+loss+1+2*n*(Fintype.card V)) ≤ i)
    (v w : ℕ) (C : ℝ)
    (winding : (eventually_atTop.mp (WilsonCoveredOrdinarySpecificPost.original R simple D φ grades
      width order shelf k seats 0 (Fintype.card V) v w (p+1) 1 1 C zero_le_one ep)).choose ≤ i) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let h := (WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let cold := House.chilly (G:=G) (plaquettes (placed).origin H) τ
    ∀ (x : Wallet actors)
      (faces : Finset (Stock.census V).Mode) (c : (Stock.census V).Mode → ℂ) (M : ℝ),
      (gf^loss*(∑ s∈faces,‖c s‖/Poly.toll P.w s) ≤ M) →
      (∀s∈faces, gf^v ≤ Poly.toll P.w s) → gf^w*(∑s∈faces,‖c s‖) ≤ C →
      let angle := WilsonJointAxialHearing.angleOf (placed).origin h J axes r gf
      let expected := fun (s : (Stock.census V).Mode) U => WilsonCoveredOrdinaryPolynomial.evaluated order
        (fun d=>Air.discharge (writer x) d (angle U)) (gf:ℂ) s
      let difference := fun U => ∑s∈faces,c s*((Poly.pass (bare lamps x U)).part s-cold.indicator (expected s) U)
      let D₀ := WilsonReceivedCloseOrdinaryGrade.invoice (Stock.census V) (Fintype.card V) 0 (p+loss) 1+
        (4:ℝ)^(p+loss+1+2*n*(Fintype.card V))*(Fintype.card (Multi.parts (Stock.census V)).Mode)*((2:ℝ)^n)^(Fintype.card V)
      RG.Envelope difference ∧ ∀ j, (age : j ≤ i) →
        ∫ U, ‖actualTransport R.family (N:=N) difference age U‖ ∂scene R.family.path N per j ≤
          (M*D₀+ε)*gf^(p+1) := by
  intro H r τ h cold x faces c M weighted salaries costs angle expected difference D₀
  let F := WilsonCoeffUV.repeatF (R.family.path.levels.clock.op i per)
  let tag := PhysicalWilsonPeriodizedProgram.branch (R.family.path.levels.clock.op i per)
  let I := head x
  let finite := fun (s : (Stock.census V).Mode) U => (Order.value (gf:ℂ) (Order.ratio
    (Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) F tag I (angle U) order))).part s
  let nominal := fun (s : (Stock.census V).Mode) U => (Poly.pass (bare lamps x U)).part s
  let X := fun U => ∑s∈faces,c s*(nominal s U-cold.indicator (finite s) U)
  let Y := cold.indicator fun U => (∑s∈faces,c s*finite s U)-(∑s∈faces,c s*expected s U)
  have equality : difference=fun U=>X U+Y U := by
    funext U
    change (∑s∈faces,c s*(nominal s U-cold.indicator (expected s) U)) =
        (∑s∈faces,c s*(nominal s U-cold.indicator (finite s) U))+
          cold.indicator (fun V=>(∑s∈faces,c s*finite s V)-(∑s∈faces,c s*expected s V)) U
    by_cases on : U∈cold
    · have eq₀ (f : Config G (R.family.side i per) → ℂ) : cold.indicator f U=f U :=
        Set.indicator_of_mem on _
      simp only [eq₀,mul_sub,Finset.sum_sub_distrib]
      abel
    · have eq₀ (f : Config G (R.family.side i per) → ℂ) : cold.indicator f U=0 :=
        Set.indicator_of_notMem on _
      simp only [eq₀,sub_zero,add_zero]
  have fits (s : (Stock.census V).Mode) (_ : s∈faces) : s.val.card+0 ≤ order+1 := by
    have := Finset.card_le_univ s.val
    omega
  have bounds : RG.Envelope X := WilsonReceivedFiniteOrdinaryEnvelope.original R hk D Q π Γ Ψ course books hi cut
    ahead actors pieces grades order shelf seats physical P simple funded slow J clear axes q ep width law enrolled fund
    late finiteLate pass hospital narrow load fit x F tag faces c 0 fits
  have price := WilsonJointAxialRefund.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P simple funded slow J clear axes q ep width law enrolled fund late finiteLate
    pass hospital narrow load fit gate p loss reserve headroom accuracy clockLate rareLate x F tag faces c M weighted i le_rfl
  have current : (∫ U, ‖X U‖ ∂scene R.family.path N per i) ≤ M*D₀*gf^(p+1) := by
    simpa only [actualTransport_base R.family R.makes cut.le] using price
  have close := WilsonReceivedAxialWindingHearing.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P simple funded slow J clear axes q ep width law enrolled fund ((le_max_left ..).trans late)
    pass hospital narrow load fit (Fintype.card V) v w (p+1) C winding x F tag faces c
    (fun s h=>⟨Finset.card_le_univ _,salaries s h⟩) costs
  have measured : Measurable Y := close.1
  have owed : ∀U, ‖Y U‖≤ε*gf^(p+1) := close.2.1
  rw [equality]
  obtain ⟨env,each⟩ := joined R cut.le X Y bounds measured (M*D₀*gf^(p+1)) (ε*gf^(p+1)) current owed
  refine ⟨env,fun j age => (each j age).trans_eq ?_⟩
  ring

end YM.Integration.WilsonReceivedCoveredEarlier
