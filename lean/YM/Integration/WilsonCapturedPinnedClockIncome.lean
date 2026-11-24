import YM.Integration.WilsonCapturedClockRankProjection
import YM.Integration.WilsonCapturedPinnedGroupClock

/-! Reprice the positive angular ranks at the very clock used on the submitted
subroster. The finite sum retains each thermal grade and its own original toll. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPinnedClockIncome
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Comparison.RG02 Multi AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonEmittedRootedJetWage WilsonCapturedCoveredSourceWage WilsonOriginalPinnedDeckOrbit WilsonOriginalJointDeckMotion WilsonOriginalLinkedAngularPage
open WilsonOriginalCenteredSeamSalary WilsonCapturedRootedAngularSlots WilsonOriginalSuspendedTensor WilsonOriginalPaidWalkCover WilsonOriginalSuspendedFootprint
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Booth RegulatorIR.FVAAlt2.Pipeline
open Adjacent Moving.Path Assembly WilsonCapturedOccupiedClockTaylor WilsonCapturedPinnedGroupClock WilsonCapturedClockRankProjection
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
    (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (v:s.val)
    {w:V→ℝ}{grades:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf)(hs:0<σ)(cut:ι→Prop)
    (b:PagesOf n N)(clock:UnitCost)(pole e:ℕ)(quiet:ℝ → Config G N → ℝ)

def reportedRow:Link G N→ℂ:=fun a=>See.noseC (Stock.census Unit) () clock
    (ink h (crop M cut) t s v b pole quiet) e (Stationary.arm G N 1 a)

include stock hs in
theorem mounted (r:ℕ)(hr:0<r)(x:Fin r→Site N×Loc G 1):
    coefficient r (reportedRow h M t s v cut b clock pole e quiet) x=
      ∑i∈range (pole+e+1),motion (money clock (-(pole:ℤ)) i r) (pole+e) *
        coefficient r (field h M t s v cut 0 i b) x:=by
  have stockCut:=earned M stock cut
  have regular:ContDiffAt ℝ ω (localField h (crop M cut) t s v b) 0:=(WilsonCapturedPinnedGroupClock.regular h (crop M cut) t s v stockCut hs b).contDiffAt
  let F:=localField h (crop M cut) t s v b
  have read:reportedRow h M t s v cut b clock pole e quiet=born (layers F) clock (-(pole:ℤ)) (pole+e) (pole+e):=by
    unfold reportedRow
    rw [WilsonCapturedPinnedGroupClock.clock]
    exact funext (WilsonCapturedOccupiedClockTaylor.original clock pole (pole+e) F regular)
  rw [read]
  change iteratedFDeriv ℝ r _ 0 _=_
  rw [WilsonCapturedClockRankProjection.original clock _ _ _ hr (layers F) (WilsonCapturedOccupiedClockTaylor.grades F regular (pole+e))]
  apply sum_congr rfl;intro i _
  rw [show layers F i=field h M t s v cut 0 i b from layer h (crop M cut) t s v stockCut hs b i]
  rfl

include stock hs in
theorem total (α weight:ℝ)(aw:0≤weight)(r:ℕ)(hr:0<r)(root:Site N)(P:ℕ→ℝ)
    (wage:∀i≤pole+e,weight*exposure α r root (field h M t s v cut 0 i b)≤P i):
    weight*exposure α r root (reportedRow h M t s v cut b clock pole e quiet) ≤
      charge clock (-(pole:ℤ)) (pole+e) r P:=by
  let a (i:ℕ):ℂ:=motion (money clock (-(pole:ℤ)) i r) (pole+e)
  let F(i:ℕ):=field h M t s v cut 0 i b
  let tariff (x:Fin r→Site N×Loc G 1):=Real.exp (α*(radius root (sites x):ℝ))
  unfold exposure
  rw [mul_sum]
  calc
    _ ≤ ∑x:Fin r→Site N×Loc G 1,∑i∈range (pole+e+1),‖a i‖*(weight*(tariff x*‖coefficient r (F i) x‖)):=by
      apply sum_le_sum;intro x _
      rw [mounted h M t s v stock hs cut b clock pole e quiet r hr x]
      change weight*(tariff x*‖∑i∈range (pole+e+1),a i*coefficient r (F i) x‖)≤_
      apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le ..) (Real.exp_pos _).le) aw).trans
      rw [mul_sum,mul_sum]
      apply sum_le_sum;intro i _;rw [norm_mul];exact le_of_eq (by ring)
    _ = ∑i∈range (pole+e+1),‖a i‖*(weight*exposure α r root (F i)):=by
      rw [sum_comm];apply sum_congr rfl;intro i _;simp only [exposure,mul_sum,tariff]
    _ ≤ _:=sum_le_sum fun i hi=>mul_le_mul_of_nonneg_left (wage i (mem_range_succ_iff.mp hi)) (norm_nonneg _)

include stock hs in
theorem original (r:ℕ)(hr:0<r):
    Poly.toll w s*exposure (σ/8) r (page h (o.origin v.val) b).val (reportedRow h M t s v cut b clock pole e quiet) ≤
      charge clock (-(pole:ℤ)) (pole+e) r (fun i=>fare G i r σ C):=by
  apply total h M t s v stock hs cut b clock pole e quiet _ _ (prod_nonneg fun y _=>(stock.positive y).le) r hr
  intro i _;exact WilsonCapturedCoveredSourceWage.original h M t s v stock hs cut 0 i r b

end YM.Integration.WilsonCapturedPinnedClockIncome
