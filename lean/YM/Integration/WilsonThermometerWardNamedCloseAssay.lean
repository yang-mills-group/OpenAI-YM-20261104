import YM.Integration.WilsonThermometerWardNamedFare

/-! The funded, named (6,4,4) Wilson source and its copied numerical course at a fixed before-order source price. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardNamedCloseAssay
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
  (Z:Group R.family 6) (payment:ℝ)
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

local notation "K₀" => ∑i,WilsonThermometerWardSolvedShoulder.coin R (N:=b+1) (p:=per) v i
local notation "salary" => max 1 (WilsonOriginalStarSceneRent.wallet R dim 0)
local notation "earning" c:max => (∑s,‖(c) s‖)*WilsonThermometerWardNamedFare.stageFee R payment univ
local notation "loss" T:max => (21*(T)+19)
local notation "arrFee" atDate:max L:max => Oak.expenseReal R hk D Q π Γ books atDate (L).op (L).lesson ahead school.order school.horizon
include simple history scroll chamber warm top cal hospital in
theorem original (one:1≤Ω₀) (admitted:Ω₀≤budgetR R b)
    (q degree:ℕ) {cap:ℝ} (base:0≤cap) (r:ℕ) (orders:r=q+2*school.pieces) (shape:op.count=school.pieces) (slots:3 ≤ op.count) (space:∑j,dim j ≤ school.horizon)
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
    (paid:WilsonThermometerAncestralLongLaunch.Funded R r (η/2^(r+5)) j) (asking:0≤η)
    (upper:WilsonMovingMentorRootRadius.Income (M:=R.metals) D φ R.alloy.delay)
    (available:Burn.horizon k≤R.alloy.B.a.clock.J (b+1))
    (rootWidth:WilsonOriginalThermometerTollBudget.reach R≤R.alloy.B.a.clock.J (b+1)+1)
    (close:PaceR.Close R degree cap j b) (within:j≤k₀)
    (slow:∀n,((C).S.block n).val≤Real.log (RG16.Lambda (C).path.levels n))
    (geometry:(eventually_atTop.mp
      (WilsonThermometerWardCloseSpan.original R simple slow degree base (zero_lt_one:0<(1:ℝ)))).choose≤b)
    (prepared:(eventually_atTop.mp (WilsonThermometerWardSolvedShoulder.original R simple degree base)).choose≤k₀)
    (arrived:(eventually_atTop.mp ((eventually_atTop.mp
      (WilsonThermometerWardSolvedShoulder.original R simple degree base)).choose_spec k₀ prepared)).choose≤b)
    (funded:(eventually_atTop.mp (WilsonThermometerWardShoulderFunding.original R simple school.pieces q
      40 asking)).choose≤j)
    (fiscal:(eventually_atTop.mp (WilsonThermometerWardNamedFare.original R simple degree cap)).choose≤b)
    (near:Z.station.k≤b)
    (honest:WilsonThermometerNominatedSourceSalary.owns Z k₀ N₀ per live univ S.route
      (payment*(R.alloy.B.a.clock.hatBeta Z.station.k)^((1:ℝ)/6))):
    head = WilsonThermometerCourseHearing.offered R Z simple b.lt_succ_self o ∧
    ∃ base:post b hi (head), HEq base.model (primitive R Z N₀ per o.origin σ₀) ∧ base.inputIndex=Empty ∧
      ∃ L:post j mj (arr j jb), L.rent ≤ η*g j^(r+2) ∧
      (∀l,(L.passport.coarser ((C).path.levels.clock.op j per).ratio).origin l=
        ((C).S.toDepth (jb.trans b.le_succ) per).parent (o.origin l)) ∧
      ((8*(arrFee mj L)^L.op.count)*L.rent+(1/4)*(g (j+1))^q≤(g (j+1))^q) ∧
      (∀c:(J₀).Mode→ℂ,(g (j+1))^41*WilsonGeometricSignedCapture.weightBill c L.w≤earning c) ∧
      (∀u j₀:ℕ,WilsonThermometerWardShoulderResponse.Paid (j:=j₀) (u:=u)
        R simple (Nat.lt_succ_of_le jb) hk D Q π Γ Ψ books mj ahead school.order school.horizon school.pieces
        disks S₀ dim (arr j jb) L WilsonThermometerCourseHearing.fired q 41
        (fun c=>earning c) o.origin v) ∧
      ((arr j jb) WilsonThermometerCourseHearing.fired =
        gust (C).path N₀ per N₀ (WilsonCapturedPrimaryWardAppointment.input R dim o.origin v (J₀)) (j+1)
          (Nat.succ_le_succ jb)) ∧
      ∀x:Wallet disks,
        let upper:=WilsonThermometerRegisteredPupil.bare R Z D π (φ:=φ) school o x
        ∀(grid:Side)(div:((C).side j per).val ∣ grid.val)(d:ℕ),d ≤ school.order → ∀field,
          (WilsonOriginalCoveredEvolution.run R b.lt_succ_self π Γ depth school.order dim upper) j jb grid div d field =
            peek div (teacher j mj L) dim (π (j+1)) tape x d field :=by
  classical
  obtain ⟨y,solved,wages⟩:=((eventually_atTop.mp (WilsonThermometerWardNamedFare.original R simple degree cap)).choose_spec b fiscal)
    j jb close N₀ per b.lt_succ_self k₀ o S live Z near payment honest
  have named:=WilsonThermometerWardNamedProgram.original R Z simple o S live y solved refs
  have exact:=WilsonThermometerWardNamedProgram.on_shelf R dim o.origin S live y v solved
  have issued:=WilsonThermometerWardCloseCoverAssay.original R simple hk D Q π Γ Ψ history scroll books chamber hi warm top
    school o S live y op lesson cal ahead hospital W one admitted q degree base r orders shape slots space fit room future stamp cover
    width refs jb mj path pass month fits deep aged ep unit late small paid asking upper available rootWidth close within slow
    geometry prepared arrived funded
  rw [exact] at issued named
  obtain ⟨basePost,source,blank,L,rent,homes,bill,old,_,physical,copied⟩:=issued
  refine ⟨named.2.1,basePost,source,blank,L,rent,homes,bill,fun c=>wages c L.w (old c),?_,physical,copied⟩
  intro u j₀
  exact WilsonThermometerWardShoulderResponse.original (j:=j₀) (u:=u) R simple (Nat.lt_succ_of_le jb)
    hk D Q π Γ Ψ history books mj ahead school.order school.horizon school.pieces disks S₀ dim
    (arr j jb) L WilsonThermometerCourseHearing.fired q 41 (fun c=>earning c) o.origin v
    (fun c=>wages c L.w (old c)) bill physical (small (j+1) j.le_succ (Nat.succ_le_succ jb)).1.le
    (small (j+1) j.le_succ (Nat.succ_le_succ jb)).2
end YM.Integration.WilsonThermometerWardNamedCloseAssay
