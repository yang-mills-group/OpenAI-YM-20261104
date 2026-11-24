import YM.Integration.WilsonThermometerWardNamedCloseAssay
import YM.Integration.WilsonThermometerWardIndividualCourse

/-! The actual signed return for the named three-source programme through any
finite number of dates. The original microscopic and accumulated card costs
remain visible on every occupied subset. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardIndividualHistory
open RG05Readout RG05Readout.Address PhysicalNext Next.Foundations PhysMS
open WilsonCapturedPrimaryActiveArms WilsonCapturedPrimaryWardGapAperture WilsonThermometerOwnOffsetField
open WilsonThermometerOffsetTrajectory
open WilsonReceivedFirstTrace
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators
open Pert.Asymptotics FVA1Physical.TwoReset WilsonOriginalCopiedHistory MergeProof.Accent Extra.Histories

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m per k b:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (b+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m  ≤  b)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (b+1)) (R.family.path.levels.clock.forcedAllowance (b+1)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (b+1) per))
  {k₀:ℕ} (S:Shelf (N:=b+1) (p:=per) R k₀ levels o.origin) (live:k₀≤b+1)
  (Z:Group R.family 6)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (b+1)) (R.alloy.B.a.clock.J b))
  (lesson:Lesson (N:=b+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=b+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "dim" => WilsonOriginalThermometerPalette.levels
local notation "v" => WilsonThermometerWardNamedProgram.axis R Z (b+1) per
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (b+1))
local notation "M₀" => WilsonThermometerWardBareScene.models R dim (b+1) per o.origin v σ₀ (show ∀i:Fin 3,0<dim i from by intro i;fin_cases i <;> decide)
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (b+1)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerWardBareScene.physical R dim (b+1) per o.origin v

local notation "C" => R.family
local notation "coins" => (fun j=>Next.Rank.Price.awake (C) (dim j) (b+1) (b+1) per (v j))
variable (W:Registration (m:=m) (N:=b+1) (k:=k) R D Q π Γ Ψ books ahead disks school.horizon school.pieces)
local notation "N₀" => (b+1)
local notation "arr" j:max jb:max => WilsonReceivedCloseHistory.history (N:=N₀) R disks (head) j jb
local notation "post" i:max mi:max y:max => WilsonOriginalReceivedChain.Post (N:=N₀) R hk D Q π Γ Ψ books ahead
  disks S₀ dim school.order school.horizon school.pieces i mi y
local notation "teacher" a:max mi:max P:max => Oak.student (i:=a) (n:=per) R hk D Q π Γ books mi
  (P).op (P).lesson ahead disks (P).model school.order (P).voter
local notation "store" L:max c:max cut:max => WilsonReceivedFirstTrace.install R hk D Q π Γ Ψ books ahead
  disks S₀ dim school.order school.horizon school.pieces W L c cut
local notation "g" => regulatorRun (C) N₀ per
local notation "depth" => Burn.horizon k+2
local notation "tape" => AllOrder.Floe.Step.tape depth

local notation "arrFee" atDate:max L:max => Oak.expenseReal R hk D Q π Γ books atDate (L).op (L).lesson ahead school.order school.horizon
include simple history scroll chamber warm top cal hospital in
theorem original (y:(i:Fin 3)→Palette (C) (dim i))
    (actual:WilsonCapturedPrimaryNamedReturn.primary R (p:=per) dim S.route live v y) (one:1 ≤ Ω₀)
    (q r:ℕ) (orders:r=q+2*school.pieces) (shape:op.count=school.pieces) (slots:3 ≤ op.count) (space:∑j,dim j ≤ school.horizon)
    (fit:WilsonOriginalStarSceneWords.maximum R dim ≤ school.order) (room:school.order+1  ≤  op.stage)
    (future:school.order ≤ R.alloy.B.a.clock.J b) (stamp:∀j,dim j ≤ R.alloy.B.a.clock.J b)
    (cover:school.order+school.horizon ≤ Burn.horizon k+2)
    (width:Sycamore.Boot.need 0 school  ≤  R.alloy.B.a.clock.J (b+1))
    (refs:∀j,(C).ref (dim j)  ≤  b+1)
    {ε η:ℝ} {j:ℕ} (jb:j ≤ b) (mj:m ≤ j)
    (path:PlanV.Path D R.alloy Q (Burn.horizon k) N₀ m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:school.order ≤ Burn.horizon k+1)
    (deep:2*(r+5)+8 ≤ school.order) (aged:r+5+3 ≤ 3*k+2) (ep:0<ε) (unit:ε ≤ 1)
    (late:WilsonReceivedMeasuredStampPrice.opening R W.simple (r+5) school.order k deep aged ep ≤ j+1)
    (small:∀l,j ≤ l→l ≤ N₀→0<g l ∧ g l ≤ 1)
    (paid:WilsonThermometerAncestralLongLaunch.Funded R r (η/2^(r+5)) j) (ask:0≤η)
    (funded:(eventually_atTop.mp (WilsonThermometerWardShoulderFunding.original R simple school.pieces q 0 ask)).choose≤j):
    let A:=WilsonThermometerIndividualSourceWallet.aperture R dim coins σ₀ Ω₀
    exposed R dim o.origin S live y=v ∧
    head=WilsonThermometerCourseHearing.offered R Z simple b.lt_succ_self o ∧
    ∃ base:post b hi (head), HEq base.model (primitive R Z N₀ per o.origin σ₀) ∧ base.inputIndex=Empty ∧ base.w=(fun i=>(A i)⁻¹) ∧
      ∃ L:post j mj (arr j jb), L.rent ≤ η*g j^(r+2) ∧
      (∀i,(L.passport.coarser ((C).path.levels.clock.op j per).ratio).origin i=
        ((C).S.toDepth (jb.trans b.le_succ) per).parent (o.origin i)) ∧
      ∃d:ℝ,1 ≤ d ∧ d ≤ ∏l∈Ico j b,(budgetR R l)^2*(budgetR R (l+1))^7 ∧
        (∀i,L.w i=(A i)⁻¹/d) ∧ (∀c:(J₀).Mode→ℂ,WilsonGeometricSignedCapture.weightBill c L.w=∑s,‖c s‖*(∏i∈s.val,A i*d)) ∧
      (8*(arrFee mj L)^L.op.count)*L.rent+(1/4)*(g (j+1))^q≤(g (j+1))^q ∧
      (∀u j₀:ℕ,WilsonThermometerWardShoulderResponse.Paid (j:=j₀) (u:=u)
        R simple (Nat.lt_succ_of_le jb) hk D Q π Γ Ψ books mj ahead school.order school.horizon school.pieces
        disks S₀ dim (arr j jb) L WilsonThermometerCourseHearing.fired q 0
        (fun c=>∑s,‖c s‖*(∏i∈s.val,A i*d)) o.origin v) ∧
      ((arr j jb) WilsonThermometerCourseHearing.fired =
        gust (C).path N₀ per N₀ (WilsonCapturedPrimaryWardAppointment.input R dim o.origin v (J₀)) (j+1)
          (Nat.succ_le_succ jb)) ∧
      ∀x:Wallet disks,
        let upper:=WilsonThermometerRegisteredPupil.bare R Z D π (φ:=φ) school o x
        ∀(grid:Side)(div:((C).side j per).val ∣ grid.val)(d:ℕ),d ≤ school.order → ∀field,
          (WilsonOriginalCoveredEvolution.run R b.lt_succ_self π Γ depth school.order dim upper) j jb grid div d field =
            peek div (teacher j mj L) dim (π (j+1)) tape x d field :=by
  classical
  intro A
  have same:=WilsonThermometerWardNamedProgram.on_shelf R dim o.origin S live y v actual
  have named:=WilsonThermometerWardNamedProgram.original R Z simple o S live y actual refs
  rw [same] at named
  have high:∀i:Fin 3,0<dim i:=WilsonOriginalThermometerGradedPalette.positive
  obtain ⟨basePost,source,blank,initial,L,rent,homes,⟨d,positive,limit,rad,wage⟩,physical,copied⟩:=
    WilsonThermometerWardIndividualCourse.original R simple hk D Q π Γ Ψ history scroll books chamber hi warm top school
      o dim high v op lesson cal ahead hospital W one r shape slots space fit room future stamp cover
      width refs jb mj path pass month fits deep aged ep unit late small paid
  have pay:=((eventually_atTop.mp (WilsonThermometerWardShoulderFunding.original R simple school.pieces q
    0 ask)).choose_spec j funded) (b+1) per (Nat.lt_succ_of_le jb)
  have paidRent:L.rent≤η*(g j)^(q+2*school.pieces+2):=by simpa only [orders] using rent
  have bill:=(pay (arrFee mj L) L.rent 0 0 L.op.count L.issued.Waffle.cool L.issued.Beamwork
    L.capacity.le L.active.le paidRent le_rfl (by simp)).1
  rw [named.2.2 D π φ k school] at copied
  refine ⟨same,named.2.1,basePost,source,blank,initial,L,rent,homes,d,positive,limit,rad,wage,bill,?_,physical,copied⟩
  intro u j₀
  exact WilsonThermometerWardShoulderResponse.original (j:=j₀) (u:=u) R simple (Nat.lt_succ_of_le jb)
    hk D Q π Γ Ψ history books mj ahead school.order school.horizon school.pieces disks S₀ dim
    (arr j jb) L WilsonThermometerCourseHearing.fired q 0 (fun c=>∑s,‖c s‖*(∏i∈s.val,A i*d)) o.origin v
    (fun c=>by rw [wage c,pow_zero,one_mul]) bill physical (small (j+1) j.le_succ (Nat.succ_le_succ jb)).1.le
    (small (j+1) j.le_succ (Nat.succ_le_succ jb)).2

end YM.Integration.WilsonThermometerWardIndividualHistory
