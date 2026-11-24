import YM.Integration.WilsonOriginalNullBareGerm
import YM.Integration.WilsonOriginalNullBareGross
import YM.Integration.WilsonOriginalNullBareSplit
import YM.Integration.WilsonOriginalNullBareInvoice
import YM.Integration.WilsonOriginalNullBareBookHearing
import YM.Integration.WilsonOriginalNullBarePanel
import YM.Integration.WilsonCapturedPrimarySection
import YM.Integration.WilsonCenteredCaptureClock
import YM.Integration.WilsonOriginalNullBareClean
import YM.Integration.WilsonOriginalNullBareGallery
import YM.QuadraticLocal.Advent
import YM.Integration.WilsonOlderFreshWordReversion
import YM.Integration.WilsonCenteredFullDensity

/-! The genuine uncut top word, on the complete clean-domain detector in the original vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullBareFunding
open Function Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org
open AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open Push Push.PriceCompiler QuadraticLocal.Rebirth QuadraticLocal.Affinity ConnectedActivityE6
open AnalyticBridge VerifiedReset RemainderComparison LocalComparison Comparison.RG02
open Extra.Histories Extra.Trajectories Source Labels Push.Local Planned.GuardedAtom
open Comparison.RG02.Cumulants Ac
open WilsonOlderFreshGraphHostTarget WilsonCenteredFiledAtoms
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {m i N per k d:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:(j:ℕ)→RG.Rep G (R.family.side j per))
  (history:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) {φ:ℕ→ℕ}
  (books:Mentor.Offices.Books D R.rolls Q φ) (hi:m ≤ i) (live:i+1 ≤ N) (school:Syl.School k)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {P:Earn.Passport (R.family.side (i+1) per) Unit} (A:Unit→Set ℂ)
  {J:Type} (M:J→Row P (Stock.census Unit) G (Wallet A))
local notation "U" => Ψ (i+1)
local notation "σ₀" => Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))
local notation "κ" => forcedDivisor R.family (i+1)
local notation "β" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "fire" => (Stock.census Unit).fire ()


open Trace.Physical.Germ Pert.Asymptotics WilsonCapturedPrimaryPaid
local notation "side" => R.family.side (i+1) per
local notation "μ" => (R.family.path.levels.params (i+1)).columns
local notation "η" => R.alloy.B.a.clock.forcedAllowance (i+1)
variable (e:ℕ)
local notation "Fr" => R.family.labels.level e
local notation "Y" => R.family.params
local notation "Sec" => R.family.localSection e
local notation "gs" => regulatorRun R.family ((i+1)+1) per ((i+1)+1)

open Trace.Physical.GermGraph WilsonOlderSignedOneMarkTariff Next.Foundations RG16
variable (simple:G.Simple) (slow:∀ j,((R.family.S.block j).val:ℝ) ≤ Real.log (Lambda R.family.path.levels j))
  (ready:WilsonReportLampForecast.Ready R.family.path.levels)
local notation "decoder" => WilsonCapturedPrimaryDecoder.invoice Fr Y e
local notation "Wfee" => WilsonCapturedPrimaryCoreBill.wrapFee Fr Y
local notation "cpp" => 8*Real.exp 102*(1+2*charge Y Sec)+2*Real.exp 102
local notation "stamp" => (2:ℝ)^(school.order+school.horizon+1)
local notation "head" => grade 3 e 1

def first:ℕ:=
  max (R.t e) (max (WilsonCenteredCaptureClock.first R simple)
    (max (eventually_atTop.mp (Trace.Physical.GermGraph.cut_flat R.family simple 0)).choose
    (max (eventually_atTop.mp (WilsonCapturedPrimaryOnRun.readouts R simple Fr Y Sec 3 0 1 le_rfl)).choose
    (max (eventually_atTop.mp (WilsonOriginalNullBareScale.original R simple slow ready decoder)).choose
    (eventually_atTop.mp (WilsonOriginalNullBareTariff.original R Sec Y simple slow ready)).choose))))

include history live in
theorem original {τ c w fac θ:ℝ} {cut:ℕ}
    (post:Landed (d:=d) (N:=N) R hk D Q π Γ Ψ books hi school ahead A M τ c w cut)
    (cp:0<c) (wp:0<w)
    (wallet:Invoice.Supports (U).p fac ((U).p.supportExponent+2) (Coat.gStep (U).beta) σ₀ θ)
    (bought:Invoice.price (U).p fac (school.order+school.horizon+1) school.pieces
      ((U).p.supportExponent+2) θ G ≤ stamp*budgetR R (i+1))
    (fixed:(R.family.path.levels.budget (i+1)).supportExponent=100)
    (time:first R e simple slow ready ≤ i+1) (home:Opened R.family e (i+1) per) (t:Wallet A):
    let C:=WilsonOriginalNullBareGross.price stamp cpp decoder Wfee head
    let y:=P.origin ()
    let P₁:=R.family.path.rep N per (i+1)
    ∃ (x:(Fr).Coeff) (v u:Coefficient Fr side) (B D:ℝ),
      v.Format y Y U ∧ v.remBound y U κ B ∧ u.Format y Y P₁ ∧ u.remBound y P₁ κ D ∧
      projection Fr Y (U).p.threshold y v=0 ∧ projection Fr Y P₁.p.threshold y u=0 ∧
      (fun V=>((U).eval V:ℂ)*(Spill.Foundry.uncut M (Coat.gStep (U).beta) t V).part fire)=
        ((calValues (C:=R.family) e N per (i+1) x) ∘ translate y)+(v.density y Sec U+u.density y Sec P₁) ∧
      w*(B+D) ≤ C*(1+R.alloy.B.a.clock.hatBeta ((i+1)+1))^(head+5) :=by
  intro C y P₁
  have timed:=time
  simp only [first,max_le_iff] at timed
  obtain ⟨rank,clock,wrapped,late,scale,tariff⟩:=timed
  have step:=history.1.walk (i+1) (Nat.le_succ_of_le hi) live
  have f100:(U).p.supportExponent=100:=by rw [step.truep.point];exact fixed
  let H:=R.alloy.B.a.clock.hatBeta ((i+1)+1)
  let ap:=Invoice.price (U).p fac (school.order+school.horizon+1) school.pieces ((U).p.supportExponent+2) θ G
  let E:=ap*c
  let B:=WilsonOlderSignedSingletonFare.fare (U).p Sec Y (fun _:Unit=>w) fire 1 {y} 0 E (κ*β^(-(cut:ℝ))) κ η μ
  let Jm:=2*(decoder*gs^3)*((E/w)/gs^head+μ*(Wfee*B)+B)
  obtain ⟨warm,within,gp,g1,gm,mp,mk,small⟩:=
    (eventually_atTop.mp (WilsonOriginalNullBareScale.original R simple slow ready decoder)).choose_spec (i+1) scale per
  obtain ⟨h,hf,hp,hv,hr,_⟩:=WilsonOriginalNullBareGerm.original R hk D Q π Γ Ψ history books hi live
    school ahead A M e simple post wallet rank (by rw [f100];norm_num) clock wrapped late small t
  have result:=WilsonOriginalNullBareSplit.original R e N per (i+1) live home y U
    (step.truep.point.trans (R.makes.wilson.represents N per (i+1) live).vac.symm) (fun V=>congrFun step.view V) h hf hp hr
  obtain ⟨x,v,u,vf,vp,uf,up,vn,un,allfield⟩:=result
  refine ⟨x,v,u,B,2*μ*Jm,vf,vp,uf,up,vn,un,?_,?_⟩
  · convert allfield using 1
    funext V
    exact (hv V).symm
  have native:=WilsonOriginalNullBareBookHearing.original R hk D Q π Γ Ψ books hi school ahead A M
    post wallet t 1 1 (UVNext.CouplingReset.flags_one (U).p)
  have nh:0≤E/w:=by
    simpa only [one_mul,norm_one] using (norm_nonneg _).trans native
  have en:0≤E:=by simpa only [div_mul_cancel₀ _ wp.ne'] using mul_nonneg nh wp.le
  have an:0≤ap:=by
    by_contra! neg
    exact (not_lt_of_ge en) (mul_neg_of_neg_of_pos neg cp)
  have c1:c≤1:=by
    obtain ⟨F,_,_,hc,_,_,_,_,_⟩:=post
    rw [←hc]
    exact F.affordable.trans (inv_le_one_of_one_le₀ F.issued.Waffle.cool)
  have sp:0 ≤ stamp:=by positivity
  have income:E ≤ stamp*H:=calc
    _ ≤ ap:=mul_le_of_le_one_right an c1
    _ ≤ _:=bought.trans (mul_le_mul_of_nonneg_left (WilsonOriginalThermometerTollBudget.parameter R (i+1)) sp)
  have ep:0≤8*Real.exp 102*(1+2*charge Y Sec):=by unfold charge;positivity
  have bill:= (eventually_atTop.mp (WilsonOriginalNullBareTariff.original R Sec Y simple slow ready)).choose_spec
    (i+1) tariff per U step.truep.point f100.le w E wp en y cut
  have rent:w*B ≤ cpp*H^2*E+cpp:=bill.trans (add_le_add
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith only [Real.exp_pos (102:ℝ)]) (sq_nonneg H)) en) (by linarith only [ep]))
  exact WilsonOriginalNullBareGross.original head ((by norm_num:(1:ℝ)≤2).trans (warm.trans within))
    gp g1 gm mp mk wp en (rem_nonneg hp) (by positivity) sp income rent le_rfl
end YM.Integration.WilsonOriginalNullBareFunding
