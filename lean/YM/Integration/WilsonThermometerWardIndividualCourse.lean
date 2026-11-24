import YM.Integration.WilsonThermometerWardIndividualLaunch
import YM.Integration.WilsonThermometerWardBareTrace
import YM.Integration.WilsonCapturedPrimaryTrailSites
import YM.Integration.WilsonGeometricSignedCapture

/-! The actual source tuition, first post and every finite older filed library on the same original trajectory. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardIndividualCourse
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
  (o:Positions (Fin 3) (R.family.side (b+1) per)) (dim:Fin 3→ℕ)
  (high:∀j,0<dim j) (v:(j:Fin 3)→R.family.label (dim j))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (b+1)) (R.alloy.B.a.clock.J b))
  (lesson:Lesson (N:=b+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=b+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (b+1))
local notation "M₀" => WilsonThermometerWardBareScene.models R dim (b+1) per o.origin v σ₀ high
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

private theorem wager {initial final:Fin 3→ℝ} {Z:Fin 3→ℝ} {D:ℝ} (started:∀v,initial v=(Z v)⁻¹)
    (radius:∀v,final v=initial v/D) (c:(J₀).Mode→ℂ):
    WilsonGeometricSignedCapture.weightBill c final=∑s,‖c s‖*(∏v∈s.val,Z v*D):=by
  have fixed (v):final v=(Z v*D)⁻¹:=by rw [radius,started,div_eq_mul_inv,mul_inv]
  have toll (s:(J₀).Mode):Poly.toll final s=(∏v∈s.val,Z v*D)⁻¹:=by
    simp only [Poly.toll,fixed,Finset.prod_inv_distrib]
  simp only [WilsonGeometricSignedCapture.weightBill,toll,div_eq_mul_inv,inv_inv]
include simple history scroll chamber warm top cal hospital in
theorem original (one:1 ≤ Ω₀)
    (r:ℕ) (shape:op.count=school.pieces) (slots:3 ≤ op.count) (space:∑j,dim j ≤ school.horizon)
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
    (paid:WilsonThermometerAncestralLongLaunch.Funded R r (η/2^(r+5)) j):
    let A:=WilsonThermometerIndividualSourceWallet.aperture R dim coins σ₀ Ω₀
    ∃ base:post b hi (head), HEq base.model M₀ ∧ base.inputIndex=Empty ∧ base.w=(fun v=>(A v)⁻¹) ∧
      ∃ L:post j mj (arr j jb), L.rent ≤ η*g j^(r+2) ∧
      (∀v,(L.passport.coarser ((C).path.levels.clock.op j per).ratio).origin v=
        ((C).S.toDepth (jb.trans b.le_succ) per).parent (o.origin v)) ∧
      (∃d:ℝ,1 ≤ d ∧ d ≤ ∏l∈Ico j b,(budgetR R l)^2*(budgetR R (l+1))^7 ∧
        (∀v,L.w v=(A v)⁻¹/d) ∧ ∀c:(J₀).Mode→ℂ,WilsonGeometricSignedCapture.weightBill c L.w=∑s,‖c s‖*(∏v∈s.val,A v*d)) ∧
      ((arr j jb) WilsonThermometerCourseHearing.fired =
        gust (C).path N₀ per N₀ (WilsonCapturedPrimaryWardAppointment.input R dim o.origin v (J₀)) (j+1)
          (Nat.succ_le_succ jb)) ∧
      ∀x:Wallet disks,
        let upper:=WilsonThermometerWardDeclaredPost.bare R D π (φ:=φ) school o dim high v x
        ∀(grid:Side)(div:((C).side j per).val ∣ grid.val)(d:ℕ),d ≤ school.order → ∀field,
          (WilsonOriginalCoveredEvolution.run R b.lt_succ_self π Γ depth school.order dim upper) j jb grid div d field =
            peek div (teacher j mj L) dim (π (j+1)) tape x d field :=by
  classical
  intro A
  obtain ⟨base,wage,rent,_,passport,_,empty,models,_,_,decl⟩:=WilsonThermometerWardIndividualLaunch.original R simple
    hk D Q π Γ Ψ history scroll books chamber hi warm top school o dim high v op lesson cal ahead hospital
    one (r+5) shape slots space fit room future stamp cover width refs
  have counted:Countable base.inputIndex:=by rw [empty]; infer_instance
  have eight:1 ≤ 8*Ω₀^op.count := one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ one)
  have start:base.rent ≤ g N₀^(r+5):=(le_mul_of_one_le_left base.active.le eight).trans rent
  obtain ⟨L,count,tr,rented,⟨d,d0,bill,rad⟩,raw,copied⟩:=
    WilsonThermometerWardBareTrace.original R hk D Q π Γ Ψ books ahead dim school.order school.horizon school.pieces
      W hi o.origin v base counted path pass month fits cover r deep aged ep unit late small paid start mj jb
  have loc:=WilsonCapturedPrimaryTrailSites.outgoing R hk D Q π Γ Ψ books ahead disks S₀ dim school.order school.horizon
    school.pieces hi (head) (store base counted b.lt_succ_self) jb (tr.trail R hk D Q π Γ Ψ books ahead
      disks S₀ dim school.order school.horizon school.pieces W hi (head) base counted b.lt_succ_self (r+5) ε)
  have first (v):base.w v=(A v)⁻¹:=congrFun wage v
  refine ⟨base,models,empty,wage,L,rented,?_,⟨d,d0,bill,fun v=>(rad v).trans (by rw [first]),wager first rad⟩,raw,fun x=>copied x _ (decl x)⟩
  intro v
  have site:=loc v
  change (L.passport.coarser ((C).path.levels.clock.op j per).ratio).origin v =
    ((C).S.toDepth (jb.trans b.le_succ) per).parent (base.passport.origin v) at site
  simpa only [passport,Passport.point] using site
end YM.Integration.WilsonThermometerWardIndividualCourse
