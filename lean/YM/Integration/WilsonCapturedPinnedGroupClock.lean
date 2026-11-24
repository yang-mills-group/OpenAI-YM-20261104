import YM.Integration.WilsonCapturedOccupiedClockTaylor
import YM.Integration.WilsonCapturedCoveredSourceWage
import YM.FVAAlt2.Pipeline.Film

/-! The original group-valued source at one marked lift, including its actual
quiet and its own marked power at the nominated reporting clock. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPinnedGroupClock
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Comparison.RG02 Multi AllOrder.Floe Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonOriginalPinnedDeckOrbit WilsonEmittedRootedJetWage WilsonOriginalPaidWalkCover
open WilsonOriginalJointDeckMotion WilsonCapturedCoveredSourceWage WilsonCapturedRootedAngularSlots
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Booth WilsonCapturedOccupiedClockTaylor
open Adjacent Moving.Path Assembly RegulatorIR.FVAAlt2.Pipeline
open scoped Classical BigOperators ContDiff
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}
    (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (v:s.val)

def group (b:PagesOf n N)(θ:ℝ)(U:Config G N):ℂ:=
  ∑'i,∑p:PagesOf n N,if (M i).mode=s ∧ index h (M i) p v.val=b then
    (M i).paint t*Complex.ofReal (Loan.letter (row h (M i) p).lamp (row h (M i) p).atom (row h (M i) p).center θ U) else 0

def ink (b:PagesOf n N)(power:ℕ)(quiet:ℝ → Config G N→ℝ):Bulk.Colors (Stock.census Unit) G N where
  vac:=quiet
  mark _:=group h M t s v b
  power _:=power

def basis (G:Gauge) (n:Side) : (ℝ×Link G n) ≃L[ℝ] Joint G n:=
  (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr edgeColor

def localField (b:PagesOf n N) : ℝ×Link G N → ℂ:=needle h M t s v 0 b ∘ basis G N

theorem seen (b:PagesOf n N)(z:ℝ×Link G N):
    group h M t s v b z.1 (RG.increment 1 (edgeColor z.2))=localField h M t s v b z:=by
  simp only [localField,basis,Function.comp_apply,needle,shade,pow_zero,Complex.ofReal_one,one_mul]
  unfold group WilsonOriginalOccupiedFieldLayout.frame
  apply tsum_congr;intro i;apply sum_congr rfl;intro p _
  by_cases k:(M i).mode=s ∧ index h (M i) p v.val=b
  · rw [if_pos k,if_pos k];rfl
  · rw [if_neg k,if_neg k]

theorem regular {w:V→ℝ}{grades:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf)(hs:0<σ)(b:PagesOf n N):
    ContDiff ℝ ω (localField h M t s v b):=
  (WilsonOriginalOccupiedFieldLayout.analytic h M t stock hs 0 _).comp (basis G N).contDiff

theorem layer {w:V→ℝ}{grades:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf)(hs:0<σ)(b:PagesOf n N)(i:ℕ):
    layers (localField h M t s v b) i = thermal (needle h M t s v 0 b) i:=by
  funext A
  exact jet_continuous_right (basis G N).toContinuousLinearMap
    ((WilsonOriginalOccupiedFieldLayout.analytic h M t stock hs 0 _).contDiffAt.of_le le_top) (1,A)

theorem draw (a:Link G N)(θ:ℝ):
    Integral.sample θ (Stationary.arm G N 1 a)=RG.increment 1 (edgeColor (θ • a)):=by
  have tested:=WilsonOriginalPinnedGradedPeek.tested (G:=G) (N:=N) (θ,edgeColor (θ • a))
  unfold Bulk.projected at tested
  rw [show (WilsonOriginalPinnedGradedPeek.chart G N (θ,edgeColor (θ • a))).2=θ • Stationary.arm G N 1 a from ?_] at tested
  · exact tested
  · simp [WilsonOriginalPinnedGradedPeek.chart]

theorem clock (C:UnitCost)(b:PagesOf n N)(power e:ℕ)(quiet:ℝ → Config G N→ℝ):
    (fun a:Link G N=> See.noseC (Stock.census Unit) () C (ink h M t s v b power quiet) e (Stationary.arm G N 1 a))=
      reported C power (power+e) (localField h M t s v b):=by
  funext a
  apply congrArg (fun f=>motion f (power+e))
  funext θ
  change _ • group h M t s v b (C.enter θ) _= _ • localField h M t s v b (WilsonCapturedOriginalClockTaylor.ray C a θ)
  rw [draw]
  exact congrArg (((C.rating θ)^power)⁻¹ • ·) (seen h M t s v b (C.enter θ,θ • a))

end YM.Integration.WilsonCapturedPinnedGroupClock
