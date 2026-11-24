import YM.Integration.WilsonThermometerRegisteredWindow
import YM.Integration.WilsonJointAxialOrdinary
import YM.Integration.WilsonReceivedOrdinaryPanel
import YM.Integration.WilsonThermometerRegisteredOrdinary

/-! The registered two-field numerator on the axial extension of the measured coarse field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonThermometerRegisteredAllMaterial

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

local notation "tape" => AllOrder.Floe.Step.tape (Burn.horizon k+2)

include course in
/-- The complete independently filed ordinary polynomial of the actual post has the finite
Wick value at the protected field, to any paid order, with its measured old vacuum. -/
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
    (pass:Pass D Q R.alloy R.kit)
    (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
    (narrow:shelf ≤ stage) (load:P.op.count ≤ Burn.horizon k+2) (fit:k ≤ stage) :
    let H:=radius R (invoice (Fintype.card (Fin 3)) (q+2*n)) 1 i
    let r:=amplitude R J H (i+2) per i
    let τ:=angularCut (R.family.path.levels.clock.hatBeta i)
    let h:=(WilsonDegreeFourInheritedRange.height R (q+2*n) i)*(4*(Ψ i).p.B+2)+2*(Ψ i).p.B+1
    ∀ U:Config G (R.family.side i per), U∈House.chilly (plaquettes (placed).origin H) τ →
      let ξ:=WilsonJointAxialWindow.direction (placed).origin h J axes r U
      let link:=WilsonCapturedPrimaryPotential.potential gf (r • ξ)
      let angle:=Stationary.arm G (R.family.side i per) 1 link
      ∀ (x:Wallet WilsonThermometerCourseHearing.disks) (F:Forest (R.family.path.levels.clock.op i per).ratio)
        (tag:(R.family.path.levels.clock.op i per).Choices),
        let writer:=Air.craft student (fun v=>(student v).paint x) levels (π i) tape
        let folded:=WilsonCoherentMayerWindingGrades.panel order (gf:ℂ) (fun d=>Air.discharge writer d angle)
        let issued:=Air.craft P.model (fun v=>(P.model v).paint x) levels (π (i+1)) tape
        let W:=Bulk.Fk ((RunFormalChain.fromRun R).step (i+2) i per cut) F tag issued angle order
        ∀ (s:(faces).Mode) (u:ℕ), s.val.card+u ≤ order+1 →
          Poly.toll P.w s*‖(Poly.pass folded).part s-(Order.value (gf:ℂ) (Order.ratio W)).part s‖ ≤
            WilsonThermometerRegisteredWindow.bill s gf (ε*gf^q) u := by
  intro H r τ h U hc ξ link angle x F tag writer folded issued W s u hu
  obtain ⟨_,r0,r1,cap,_,_⟩:=WilsonJointAxialFolded.selected R hk D Q π Γ Ψ course books hi cut ahead
    WilsonThermometerCourseHearing.disks sectors levels order shelf seats source₀ P simple funded slow J clear
    axes q ep width late pass hospital narrow load fit U hc
  obtain ⟨cool,finite⟩:=WilsonReceivedAxialFinite.priced R hk D Q π Γ Ψ course books hi cut
    ahead WilsonThermometerCourseHearing.disks sectors levels order shelf seats source₀ P simple width law
    enrolled fund q ep finiteLate fit ξ cap r0 r1
  obtain ⟨wind,mass⟩:=finite x F tag
  have zero:folded.part (faces).quiet=0:=by
    simp only [folded,WilsonCoherentMayerWindingGrades.panel,Poly.part_sum,Poly.part_smul,
      Air.discharge,Multi.part_lit_quiet,mul_zero,Finset.sum_const_zero]
  have unit:=Poly.pass_part folded zero
  have connected:Order.logTo (Fintype.card (Fin 3)) (Poly.pass folded)=folded:=
    (Order.log_to _ unit _ (fun t=>Finset.card_le_univ t.val)).symm.trans (Cumulants.connected_pass zero)
  have gp : 0 < gf := inv_pos.mpr (Real.sqrt_pos.mpr (Overlay.beta_positive R.makes.wilson cut))
  apply WilsonReceivedOrdinaryPanel.measured_on (Poly.pass folded) unit W (Bulk.fk_unit ..) (Bulk.fk_sym ..)
    P.w P.salary.positive gf (ε*gf^q) gp cool (mul_nonneg ep.le (pow_nonneg gp.le _)) s
    (fun d _=>mass d.val) _ u hu
  intro j _
  rw [connected]
  exact (Poly.member P.salary.positive j.val _).trans wind

end YM.Integration.WilsonThermometerRegisteredAllMaterial
