import YM.Integration.WilsonJointAxialOrdinary
import YM.Integration.WilsonReceivedOrdinaryPanel
import YM.Integration.WilsonThermometerRegisteredOrdinary

/-! The registered two-field numerator on the axial extension of the measured coarse field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredWindow

open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open Ac OPE.Therm WilsonLimitConstruction RG16 MSbar.Heath Labels Source Pert.Asymptotics
open WilsonRootedKioskOccupiedSlip WilsonRegisteredAffineHalo WilsonRegisteredAxialRates
open WilsonReportingForestAngularFare WilsonJointAxialRoster
open Multi Extra.Trajectories Comparison.RG02.Cumulants WilsonIndependentOrdinaryPairGrade
open FVA1 Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic
open WilsonThermometerCourseHearing WilsonThermometerRegisteredPair WilsonPositionThermometerGradedReading
open WilsonPositionThermometerGradedSource
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (simple:G.Simple) (A:Group R.family 6) {m i per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀ j, RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m (i+2) per k Ψ)
  {φ:ℕ → ℕ} (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (order shelf seats:ℕ) (o:Positions (Fin 3) (R.family.side (i+2) per))
local notation "cut" => (show i < i+2 from by omega)
local notation "faces" => Stock.census (Fin 3)
local notation "source₀" => WilsonThermometerCourseHearing.offered R A simple cut o
variable (P:WilsonOriginalReceivedChain.Post (N:=i+2) R hk D Q π Γ Ψ books ahead WilsonThermometerCourseHearing.disks sectors levels
  order shelf seats i hi (WilsonThermometerCourseHearing.offered R A simple (by omega : i < i+2) o))

local notation "student" => Oak.student (n:=per) R hk D Q π Γ books hi P.op P.lesson ahead WilsonThermometerCourseHearing.disks
  P.model order P.voter
local notation "lamps" => (rendered student (Ψ i).p (Coat.gStep (Ψ (i+1)).beta))
local notation "placed" => P.passport.coarser (R.family.path.levels.clock.op i per).ratio
local notation "n" => (order+shelf+2)
local notation "gf" => Coat.gStep (R.family.path.rep (i+2) per (i+1)).beta
local notation "stage" => R.alloy.B.a.clock.J i

variable (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
  (q:ℕ) (deep:2*(q+1)+8 ≤ order) (aged:q+4 ≤ 3*k+2)

def opening {ε:ℝ} (_ep:0 < ε) : ℕ := (eventually_atTop.mp
  (WilsonReceivedOrdinaryPanel.original R simple D φ width levels q 0 order shelf k seats deep aged 1 1
    zero_le_one _ep)).choose

def bill (s:(faces).Mode) (g E:ℝ) (u:ℕ) : ℝ :=
  (∑ h ∈ shards (faces) s,(h.val.card:ℝ)*E*(g⁻¹+E)^h.val.card)+g^u*(shards (faces) s).card

include course in
/-- For the real registered post, compare the nominal at the original coarse field with
both plantings transported through the actual two steps at its common axial extension.
All companions of those plantings enter the finite Wick comparison before it cancels. -/
theorem original {η:ℝ} {T:Campaign R} {W:Campaign.Pillars R T}
    (funded:FundedOriginalProperties.{u} simple η W)
    (slow:∀ m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda R.family.path.levels m))
    (J:Voice G) (clear:Clear G J) (axes:Lattice.Order) {ε:ℝ} (ep:0 < ε)
    (law:VowsR.LawScroll G φ) (enrolled:VowsR.Chamber law R.kit D Q books)
    (fund:Volume.Fund D R.rolls Q φ books R.alloy.delay)
    (late:max (WilsonJointAxialRoster.opening R simple funded slow J clear (Fintype.card (Fin 3)) n q ep)
        (WilsonReceivedAxialFiling.opening R simple D φ width order shelf (Fintype.card (Fin 3)) ep) ≤ i)
    (finiteLate:max (WilsonReceivedAxialFinite.opening R simple q ep)
        (WilsonReceivedAxialFinite.massOpening R D levels order shelf seats (k:=k) simple width) ≤ i)
    (hearing:opening R simple D order shelf seats width q deep aged ep ≤ i)
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:shelf ≤ stage) (load:P.op.count ≤ Burn.horizon k+2) (fit:k ≤ stage)
    (refs:∀ v,R.family.ref (levels v) ≤ i+2) (held:0 < i) :
    let H:=radius R (invoice (Fintype.card (Fin 3)) (q+2*n)) 1 i
    let r:=amplitude R J H (i+2) per i
    let τ:=angularCut (R.family.path.levels.clock.hatBeta i)
    ∀ U:Config G (R.family.side i per), U ∈ House.chilly (plaquettes (placed).origin H) τ →
      let ξ:=WilsonJointAxialWindow.direction (placed).origin
        ((WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1) J axes r U
      let B:=R.family.path.levels.budget i
      let link:=WilsonCapturedPrimaryPotential.potential gf (r • ξ)
      let angle:=Stationary.arm G (R.family.side i per) 1 link
      let W':=Integral.sample gf angle
      (∃ z:ℝ, |z| ≤ |(1:ℝ)| *(Real.log (R.family.path.levels.clock.hatBeta i))^0*
        ((B.B:ℝ)^2*B.threshold)/gf ∧ ∀ e,‖Exterior.collect G angle e‖ ≤ (1:ℝ)*|z|) ∧
      flags (Ψ i).p.threshold W'=∅ ∧
      ∀ t a b:Fin 3,a ≠ b → a ≠ t → b ≠ t → ∀ u:ℕ, 2+u ≤ order+1 →
        let x:=without t
        let s:(faces).Mode:=⟨{a,b},mem_univ _⟩
        let fields:=fun v:Fin 3 => R.family.O (i+2) per
          (A.station.wheel.atCut (i+2,per) (index A (grade v)) (vector A univ v)) (o.origin v)
        let two:=actualTransport R.family (N:=i+2) (fun Z=>fields a Z*fields b Z) (Nat.le_add_right i 2) W'
        let E:=ε*(regulatorRun R.family (i+2) per i)^q+ε*gf^order+ε*gf^q
        let E':=(8*(budgetR R i)^seats)*P.rent+ε*gf^q
        Poly.toll P.w s*‖(Poly.pass (bare lamps x U)).part s - two‖ ≤ bill s gf E u+bill s gf E' u := by
  intro H r τ U cold ξ B link angle W'
  obtain ⟨sampled,r0,r1,uniform,healthy,folds⟩:=WilsonJointAxialOrdinary.selected R hk D Q π Γ Ψ
    course books hi cut ahead WilsonThermometerCourseHearing.disks sectors levels order shelf seats source₀ P simple funded slow J
    clear axes q ep width law enrolled fund late finiteLate pass hospital narrow load fit U cold
  obtain ⟨z,range,paid⟩:=WilsonReceivedAxialFinite.room R π Γ Ψ course hi cut ξ uniform r0 r1
  have clearW:flags (Ψ i).p.threshold W'=∅:=by
    have all:=healthy r ⟨r0,le_rfl⟩ univ
    change Disjoint univ (flags (Ψ i).p.threshold _) at all
    change flags (Ψ i).p.threshold (Integral.sample gf angle) = ∅
    rw [sampled]
    exact Finset.eq_empty_iff_forall_notMem.mpr fun x hx => (Finset.disjoint_left.mp all (mem_univ x) hx)
  refine ⟨⟨z,range,paid⟩,clearW,?_⟩
  intro t a b ab at' bt' u enough x s fields two E E'
  let block:=R.family.path.levels.clock.op i per
  let F:Forest block.ratio:=Classical.choice (Tree.select block.ratio block.patch.odd_side)
  let tag:block.Choices:=Classical.arbitrary _
  have needed:s.val.card+u ≤ order+1:=by simpa [s,ab] using enough
  have first:=folds x F tag s u needed
  have second:=(eventually_atTop.mp (WilsonReceivedOrdinaryPanel.original R simple D φ width levels q
    0 order shelf k seats deep aged 1 1 zero_le_one ep)).choose_spec i hearing hk fit Q π Γ Ψ course
    books law enrolled fund hi cut ahead WilsonThermometerCourseHearing.disks sectors source₀ P x link z range paid clearW F tag s u needed
  have trueField:
      ((((Ψ i).eval W':ℂ)⁻¹) • LocalComparison.actualPush R.family (i+2) per i (source₀ x) W').part s = two := by
    have physical: (Ψ i).eval W' = (R.family.path.rep (i+2) per i).eval W':=
      (congrFun (course.1.walk i hi (cut).le).view W')
    rw [physical]
    change (WilsonThermometerRegisteredOrdinary.conditional R simple A cut o t W').part s = two
    have no:t∉s.val:=by simpa only [s,mem_insert,mem_singleton,not_or] using And.intro (Ne.symm at') (Ne.symm bt')
    rw [WilsonThermometerRegisteredOrdinary.observed R simple A cut o held refs t W' s,
      if_neg no,WilsonThermometerCourseResidual.observed R A simple (cut).le o refs W' s]
    simp [two,s,fields,prod_insert,ab]
  rw [trueField] at second
  let issued:=Air.craft P.model (fun b => (P.model b).paint x) levels (π (i+1))
    (AllOrder.Floe.Step.tape (Burn.horizon k+2))
  let sheet:=Order.value (gf:ℂ) (Order.ratio (Bulk.Fk
    ((RunFormalChain.fromRun R).step (i+2) i per cut) F tag issued angle order))
  let originalPanel:=(Poly.pass (bare lamps x U)).part s
  have left:Poly.toll P.w s * ‖originalPanel-sheet.part s‖ ≤ bill s gf E u:=first
  have right:Poly.toll P.w s * ‖two-sheet.part s‖ ≤ bill s gf E' u:=second
  rw [norm_sub_rev two (sheet.part s)] at right
  calc
    _ ≤ Poly.toll P.w s * (‖originalPanel - sheet.part s‖ + ‖sheet.part s - two‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le_norm_sub_add_norm_sub originalPanel (sheet.part s) two)
        (Finset.prod_nonneg fun v _ => (P.salary.positive v).le)
    _ = _ := mul_add .. 
    _ ≤ _ := add_le_add left right

end YM.Integration.WilsonThermometerRegisteredWindow
