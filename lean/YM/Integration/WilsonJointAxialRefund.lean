import YM.Integration.WilsonJointAxialCash
import YM.Integration.WilsonJointAxialClock

/-! Restored physical error for a fixed signed table of ordinary Wilson faces,
in the actual older marginal. The order and the aperture deadline precede
the top cutoff, the period, the link configuration, and the spectator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonJointAxialRefund
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
    (rareLate : WilsonJointAxialScalar.opening (V:=V) R simple gate q n (p+loss+1+2*n*(Fintype.card V)) ≤ i) :
    let H := radius R (invoice (Fintype.card V) (q+2*n)) 1 i
    let r := amplitude R J H N per i
    let τ := angularCut (R.family.path.levels.clock.hatBeta i)
    let h := (WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    let cold := House.chilly (G:=G) (plaquettes (placed).origin H) τ
    ∀ (x : Wallet actors) (F : Forest (R.family.path.levels.clock.op i per).ratio)
      (tag : (R.family.path.levels.clock.op i per).Choices)
      (faces : Finset (Stock.census V).Mode) (c : (Stock.census V).Mode → ℂ) (M : ℝ),
      (gf^loss*(∑ s∈faces,‖c s‖/Poly.toll P.w s) ≤ M) →
      let issued := Air.craft P.model (fun b => (P.model b).paint x) grades (π (i+1)) tape
      let expected := fun (s : (Stock.census V).Mode) U => (Order.value (gf:ℂ) (Order.ratio (Bulk.Fk
        ((RunFormalChain.fromRun R).step N i per cut) F tag issued
        (angleOf (placed).origin h J axes r gf U) order))).part s
      let difference := fun U => ∑ s∈faces,c s *
        ((Poly.pass (bare lamps x U)).part s - cold.indicator (expected s) U)
      let C := WilsonReceivedCloseOrdinaryGrade.invoice (Stock.census V) (Fintype.card V) 0 (p+loss) 1+
        (4:ℝ)^(p+loss+1+2*n*(Fintype.card V))*(Fintype.card (Multi.parts (Stock.census V)).Mode)*((2:ℝ)^n)^(Fintype.card V)
      ∀ j, (age : j ≤ i) →
        ∫ Z, ‖actualTransport R.family (N:=N) difference age Z‖ ∂scene R.family.path N per j ≤ M*C*gf^(p+1) := by
  intro H r τ h cold x F tag faces c M income issued expected difference C j age
  let K := p+loss+1+2*n*(Fintype.card V)
  have fits (s : (Stock.census V).Mode) (_ : s∈faces) : s.val.card+(p+loss+1) ≤ order+1 := by
    have := Finset.card_le_univ s.val
    omega
  have paid := WilsonJointAxialScalar.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P simple funded slow J clear axes q ep width law enrolled fund late finiteLate
    pass hospital narrow load fit gate K rareLate x F tag faces c (p+loss+1) fits j age
  refine paid.trans ?_
  let A := ε*(regulatorRun R.family N per i)^q+ε*gf^order+ε*gf^q
  let D₀ := (Spill.allOver (Ψ i).p)^(order+shelf+1)*
    (Oak.expenseReal R hk D Q π Γ books hi P.op P.lesson ahead order shelf)
  have band := (eventually_atTop.mp (WilsonJointAxialClock.original R simple)).choose_spec i clockLate N per cut
  obtain ⟨gp,small,relation,refund⟩ := band
  have lower : 0 ≤ regulatorRun R.family N per i := by
    change 0 ≤ (Real.sqrt _)⁻¹
    positivity
  have ag : 0 ≤ A := by dsimp only [A]; positivity
  have a0 := WilsonJointAxialClock.accuracy gp small lower relation q order headroom ep.le accuracy
  have strong : A ≤ gf^(p+loss+1+Fintype.card V) :=
    a0.trans (pow_le_pow_of_le_one gp.le small reserve)
  have budget : WilsonReceivedSourceGross.opening R simple ≤ i := (le_max_left ..).trans ((le_max_left ..).trans late)
  have gross := (WilsonReceivedSourceGross.original R hk D Q π Γ Ψ course books hi cut ahead actors pieces grades
    order shelf seats physical P simple budget pass hospital narrow load).2
  have nonneg : 0 ≤ D₀ := mul_nonneg (pow_nonneg (zero_le_one.trans (Spill.allOver_ge _)) _) P.issued.Waffle.paysAbove.le
  have bp : 0 < R.family.path.levels.clock.hatBeta i := zero_lt_one.trans (R.family.path.levels.fits.delayed i)
  exact WilsonJointAxialCash.restored (Stock.census V) faces c (Poly.toll P.w) gp small (Fintype.card V)
    (2*n) p loss (fun s _ => Finset.card_le_univ s.val)
    (fun s _ => Finset.prod_pos fun v _ => P.salary.positive v) income ag strong nonneg (one_le_pow₀ (by norm_num)) (by positivity)
    gross (WilsonJointAxialClock.exceptional (inv_pos.mpr bp).le gp.le small refund K)

end YM.Integration.WilsonJointAxialRefund
