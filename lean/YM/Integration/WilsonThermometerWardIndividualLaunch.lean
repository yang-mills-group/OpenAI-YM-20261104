import YM.Integration.WilsonThermometerWardDeclaredPost
import YM.Integration.WilsonThermometerWardIndividualScene

/-! Purchase on the genuine bare source before passing to the next true Wilson post. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardIndividualLaunch
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor 
open WilsonPositionThermometerCapStation WilsonOriginalStarSceneWords WilsonOriginalThermometerPalette
open WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m per k i:ℕ}
  (hk:Burn.horizon k+2  ≤  R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m (i+1) per k Ψ) {φ:ℕ→ℕ}
  (scroll:VowsR.LawScroll G φ) (books:Mentor.Offices.Books D R.rolls Q φ)
  (chamber:VowsR.Chamber scroll R.kit D Q books) (hi:m  ≤  i)
  (warm:Spill.Raffle.Warm G D R.alloy.delay φ)
  (top:Topline (Ψ (i+1)) (R.family.path.levels.clock.forcedAllowance (i+1)))
  (school:Syl.School k)
  (o:Positions (Fin 3) (R.family.side (i+1) per)) (dim:Fin 3→ℕ)
  (high:∀j,0<dim j) (v:(j:Fin 3)→R.family.label (dim j))
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=i+1) R hk D Q π Γ hi)
  (cal:Oak.Calendar R hk D Q π Γ Ψ hi (N:=i+1) lesson)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  (hospital:MintClock.Hospital D R.rolls Q R.kit.target φ books ahead R.alloy.delay)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "M₀" => WilsonThermometerWardBareScene.models R dim (i+1) per o.origin v σ₀ high
local notation "S₀" => WilsonThermometerCourseHearing.sectors
local notation "P₀" => Ψ (i+1)
local notation "J₀" => Stock.census (Fin 3)
local notation "E₀" => Passport.point o.origin
local notation "Ω₀" => Oak.expenseReal R hk D Q π Γ books hi op lesson ahead school.order school.horizon
local notation "head" => WilsonThermometerWardBareScene.physical R dim (i+1) per o.origin v

local notation "C" => R.family
local notation "coins" => (fun j=>Next.Rank.Price.awake (C) (dim j) (i+1) (i+1) per (v j))
open FVA1Physical.TwoReset Stationary Further.PhysicalPeriodLimitF933
local notation "tape₀" => AllOrder.Floe.Step.tape (Burn.horizon k+2)
local notation "teach" P:max => Oak.student (n:=per) R hk D Q π Γ books hi (P).op (P).lesson ahead disks
  (P).model school.order (P).voter
include simple history scroll chamber warm top cal hospital in
theorem original (one:1 ≤ Ω₀)
    (q:ℕ) (shape:op.count=school.pieces) (slots:3 ≤ op.count) (space:∑j,dim j ≤ school.horizon)
    (fit:WilsonOriginalStarSceneWords.maximum R dim ≤ school.order) (room:school.order+1  ≤  op.stage)
    (future:school.order ≤ R.alloy.B.a.clock.J i) (stamp:∀j,dim j ≤ R.alloy.B.a.clock.J i)
    (cover:school.order+school.horizon ≤ Burn.horizon k+2)
    (width:Sycamore.Boot.need 0 school  ≤  R.alloy.B.a.clock.J (i+1))
    (refs:∀j,(C).ref (dim j)  ≤  i+1):
    let g:=Coat.gStep ((C).path.rep (i+1) per (i+1)).beta
    let A:=WilsonThermometerIndividualSourceWallet.aperture R dim coins σ₀ Ω₀
    let w:=fun j=>(A j)⁻¹
    ∃ P:WilsonOriginalReceivedChain.Post (N:=i+1) R hk D Q π Γ Ψ books ahead disks S₀ dim
      school.order school.horizon school.pieces i hi (head),
      P.w=w ∧ (8*Ω₀^op.count)*P.rent ≤ g^q ∧ P.cost=(Ω₀)⁻¹ ∧ P.passport=E₀ ∧
      P.op=op ∧ P.inputIndex=Empty ∧ HEq P.model M₀ ∧
      (∀s:(J₀).Mode,Poly.toll P.w s*(∏l∈s.val,A l)=1) ∧
      (head) WilsonThermometerCourseHearing.fired =
        WilsonCapturedPrimaryWardAppointment.input R dim o.origin v (J₀) ∧
      ∀ (x:Wallet disks) (grid:Side) (mult:(R.family.side i per).val∣grid.val) (d:ℕ),d ≤ school.order→
        ∀a:Stationary.Link G grid,WilsonThermometerWardDeclaredPost.bare R D π (φ:=φ) school o dim high v x grid mult d a=
          peek mult (teach P) dim (π (i+1)) tape₀ x d a :=by
  intro g A w
  obtain ⟨crew,voter,test,pay⟩:=WilsonThermometerWardIndividualScene.purchased R dim (i+1) per o.origin v
    high σ₀ Ω₀ one school.order op.count school.horizon op.stage k (R.alloy.B.a.clock.J i)
    slots space fit room future stamp cover
  let B:=8*Ω₀^op.count
  have bp:0<B:=mul_pos (by norm_num) (pow_pos (zero_lt_one.trans_le one) _)
  have gp:0<g:=ActualRunKernelPackets.regulator_pos R (i+1) per (i+1) le_rfl
  let τ:=min 1 (g^q/B)
  have tp:0<τ:=lt_min zero_lt_one (div_pos (pow_pos gp _) bp)
  have debt:B*τ ≤ g^q:=by
    rw [mul_comm,←le_div_iff₀ bp]
    exact min_le_right _ _
  obtain ⟨P,rad,rent,cost,passport,post,bare,models,written⟩:=WilsonThermometerWardDeclaredPost.original R simple hk
    D Q π Γ Ψ history scroll books chamber hi warm top school w o dim high v op lesson cal ahead hospital
    tp (min_le_left _ _) (inv_le_one_of_one_le₀ one) le_rfl shape crew voter test width refs
  refine ⟨P,rad,?_,cost,passport,post,bare,models,?_,WilsonThermometerWardBareScene.filled R dim (i+1) per o.origin v,written⟩
  · rw [rent]
    exact debt
  · simpa only [rad] using pay
end YM.Integration.WilsonThermometerWardIndividualLaunch
