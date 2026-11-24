import YM.Integration.WilsonThermometerWardBareLaunch
import YM.Integration.WilsonThermometerAncestralLongLaunch

/-! All finite appointments for the same actual E cutoff source with its original coefficient tuition. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerWardBareTrace
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard AllOrder AllOrder.Floe AllOrder.Floe.Step PlanV AllOrder.Transit WheelP
open QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Rebirth AnalyticBridge VerifiedReset RemainderComparison
open ConnectedActivityE6 LocalComparison Mentor OPE.Therm Pert.Asymptotics WilsonReceivedFirstTrace
open WilsonOriginalCopiedHistory FVA1Physical.TwoReset MergeProof.Accent Extra.Histories
open WilsonOriginalThermometerPalette
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {m b per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ→ℕ} (books:Mentor.Offices.Books D R.rolls Q φ) (ahead:Mentor.Forecast D R.rolls Q φ books)
  (dims:Fin 3→ℕ) (order shelf seats:ℕ)
  (W:Registration (m:=m) (N:=b+1) (k:=k) R D Q π Γ Ψ books ahead disks shelf seats)
  (mb:m ≤ b) (o:Fin 3→Site (R.family.side (b+1) per)) (vec:(v:Fin 3)→R.family.label (dims v))
local notation "actors" => WilsonOriginalThermometerPalette.disks
local notation "kernels" => WilsonThermometerCourseHearing.sectors
local notation "C" => R.family
local notation "N₀" => (b+1)
local notation "J₃" => Stock.census (Fin 3)
local notation "source" => WilsonThermometerWardBareScene.physical R dims N₀ per o vec
local notation "arr" j:max jb:max => WilsonReceivedCloseHistory.history (N:=N₀) R actors source j jb
local notation "P" i:max mi:max y:max => WilsonOriginalReceivedChain.Post (N:=N₀) R hk D Q π Γ Ψ books ahead
  actors kernels dims order shelf seats i mi y
local notation "teacher" j:max mj:max L:max => Oak.student (i:=j) (n:=per) R hk D Q π Γ books mj
  (L).op (L).lesson ahead actors (L).model order (L).voter
local notation "store" L:max c:max cut:max => WilsonReceivedFirstTrace.install R hk D Q π Γ Ψ books ahead
  actors kernels dims order shelf seats W L c cut
local notation "g" => regulatorRun (C) N₀ per
local notation "depth" => Burn.horizon k+2
local notation "tape" => AllOrder.Floe.Step.tape depth

theorem original (base:P b mb source) (counted:Countable base.inputIndex) (path:PlanV.Path D R.alloy Q (Burn.horizon k) N₀ m π Γ)
    (pass:Pass D Q R.alloy R.kit) (month:Scholar.Month R.rolls D Q R.alloy.delay)
    (fits:order ≤ Burn.horizon k+1) (packed:order+shelf ≤ Burn.horizon k+2)
    (r:ℕ) {ε η:ℝ} (deep:2*(r+5)+8 ≤ order) (aged:r+5+3 ≤ 3*k+2) (ep:0<ε) (unit:ε ≤ 1)
    {j:ℕ} (late:WilsonReceivedMeasuredStampPrice.opening R W.simple (r+5) order k deep aged ep ≤ j+1)
    (small:∀l,j ≤ l→l ≤ N₀→0<g l ∧ g l ≤ 1)
    (paid:WilsonThermometerAncestralLongLaunch.Funded R r (η/2^(r+5)) j)
    (start:base.rent ≤ g N₀^(r+5)) (mj:m ≤ j) (jb:j ≤ b):
    ∃ L:P j mj (arr j jb), ∃ count:Countable L.inputIndex,
      WilsonReceivedFirstTrace.Chain R hk D Q π Γ Ψ books ahead actors kernels dims order shelf seats W
        mb source base counted b.lt_succ_self (r+5) ε j mj (jb.trans_lt b.lt_succ_self) (arr j jb) L count ∧
      L.rent ≤ η*g j^(r+2) ∧
      (∃d:ℝ,1 ≤ d ∧ d ≤ ∏l∈Ico j b,(budgetR R l)^2*(budgetR R (l+1))^7 ∧ ∀v,L.w v=base.w v/d) ∧
      ((arr j jb) WilsonThermometerCourseHearing.fired =
        gust (C).path N₀ per N₀ (WilsonCapturedPrimaryWardAppointment.input R dims o vec (J₃)) (j+1)
          (Nat.succ_le_succ jb)) ∧
      ∀(x:Wallet actors) (upper:WilsonOriginalCopiedHistory.Values G (J₃) ((C).side b per)),
        (∀(grid:Side)(div:((C).side b per).val ∣ grid.val)(d:ℕ),d ≤ order → ∀z,
          upper grid div d z=peek div (teacher b mb base) dims (π (b+1)) tape x d z) →
        ∀(grid:Side)(div:((C).side j per).val ∣ grid.val)(d:ℕ),d ≤ order → ∀field,
          (WilsonOriginalCoveredEvolution.run R b.lt_succ_self π Γ depth order dims upper) j jb grid div d field =
            peek div (teacher j mj L) dims (π (j+1)) tape x d field :=by
  classical
  obtain ⟨L,count,tr,rent⟩:=WilsonReceivedFirstTrace.from_date R hk D Q π Γ Ψ books ahead actors kernels dims order shelf seats
    W mb source base counted b.lt_succ_self (r+5) ε j path pass month fits packed deep aged ep unit late small j jb mj le_rfl
  let Z:ℝ:=2^(r+5)
  have one:1 ≤ Z:=one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have pos:0<Z:=zero_lt_one.trans_le one
  have ratio:g N₀ ≤ 2*g b:=WilsonLocalCompactRichPortUnits.compared R W.simple b.le_succ le_rfl per
  have initial:base.rent/Z ≤ g b^(r+5):=by
    apply (div_le_iff₀ pos).2
    have bound:=pow_le_pow_left₀ (small N₀ (jb.trans b.le_succ) le_rfl).1.le ratio (r+5)
    simpa only [mul_pow,mul_comm (g b ^ (r+5))] using start.trans bound
  have grant:=paid b N₀ per jb b.lt_succ_self (M:=base.rent/Z) (e:=ε/Z)
    ((div_le_one₀ pos).2 (unit.trans one)) initial
  have pooled:(base.rent+∑l∈Ico j b,ε*(g (l+2))^(r+5))/Z ≤ (η*g j^(r+2))/Z:=by
    simpa only [add_div,Finset.sum_div,div_mul_eq_mul_div] using grant
  obtain ⟨_,d,positive,roof,rad⟩:=tr.trail.wallet
  refine ⟨L,count,tr,rent.trans ((div_le_div_iff_of_pos_right pos).mp pooled),⟨d,positive,roof,rad⟩,?_,?_⟩
  · unfold WilsonReceivedCloseHistory.history
    rw [WilsonThermometerWardBareScene.filled R dims N₀ per o vec]
  · intro x upper enters
    have track:=tr.trail R hk D Q π Γ Ψ books ahead actors kernels dims order shelf seats W mb source base counted
      b.lt_succ_self (r+5) ε
    obtain ⟨_,paid⟩:=WilsonOriginalCoveredTrail.full R hk D Q π Γ Ψ books ahead actors kernels dims
      order shelf seats mb source (store base counted b.lt_succ_self) x upper b.lt_succ_self W.course pass month fits W.narrow enters track
    exact paid
end YM.Integration.WilsonThermometerWardBareTrace
