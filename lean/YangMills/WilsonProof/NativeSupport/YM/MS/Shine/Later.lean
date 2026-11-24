import YM.MS.Shine.Later
import YangMills.WilsonProof.NativeSupport.YM.MS.Shine.Ash
import YM.MS.Garment.Pivot
/-!
# Hol support with ∀z hards at every prescribed finite contour
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rock
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Path Oceans Plum Alps Garment
open scoped Topology ContDiff
variable {G:Gauge}{b:Bool}{D W:Set ℂ}{R T:ℝ}{c:ℂ}{F H:Mob G}{U:Rip G}{x:ℂ→ℂ}{f g:ℂ→ Mob G}
namespace Hol
lemma mono (h:Hol D f)(hv:W⊆D): Hol W f := ⟨ fun c R hr hp=> h.price c R hr (hp.trans hv),fun m l z zH=> h.top m l z (hv zH)⟩
lemma con (h: Hol D f)(hv:IsOpen D)(he:EqOn f g D): Hol D g:= by
   refine ⟨fun c R hr hp=>?_,fun m l z zH=>?_⟩; · rw [show (fun i:closedBall c R=> g i)=(fun i:closedBall c R=> f i) from funext fun i=> (he (hp i.property)).symm]; exact h.price _ _ hr hp
   refine DifferentiableAt.congr_of_eventuallyEq (h.top m l z zH) ?_; filter_upwards [hv.mem_nhds zH] with p hp; rw [(he hp)]
lemma add (h:Hol D f)(hp:Hol D g) : Hol D (f+g) := hills_add h hp
lemma sub (h:Hol D f)(hp:Hol D g): Hol D (f-g):= ⟨fun c R hr he=> fall_sub (h.price c R hr he) (hp.price c R hr he),fun m l z hz=> (h.top m l z hz).sub (hp.top m l z hz)⟩
lemma stays (h:kPrice F): Hol D (fun _=>F):= ⟨fun _ _ _ _=> travel h, fun _ _ _ _=> differentiableAt_const _⟩
lemma zero : Hol D (0:ℂ→Mob G):= stays (Form0.zero (b:=true)).price
lemma neg (h:Hol D f): Hol D (-f):= by simpa only [zero_sub] using Hol.zero.sub h
lemma rate (h:Hol D f)(hp:Forest D x): Hol D (x • f):= by
   refine ⟨fun c R hr hu=>?_,fun m l z zH=> ( hp z zH).mul (h.top m l z zH)⟩; obtain ⟨p,H,Hx⟩:= (isCompact_closedBall c R).exists_isMaxOn ⟨c,mem_closedBall_self hr.le⟩ ((show ContinuousOn x (closedBall c R) from fun p h=>(hp _ (hu h)).continuousAt.continuousWithinAt).norm); exact fun m E _ _ _ w=> (_root_.YM.MS.Shine.uWore (x:=fun i:closedBall c R=> x i) (h.price c R hr hu m E w) (lt_max_of_lt_left (b:= (1:ℝ)) zero_lt_one) (fun i=> le_max_of_le_right (Hx i.property))) -- b arg
lemma smul (h:Hol D f)(c:ℂ): Hol D (c • f):= h.rate (x:=fun _=>c) (fun _ _=> differentiableAt_const _)
lemma spot (h:Hol D f)(k:ℤ): Hol D (fun i=> Garment.spot k (f i)) := spot_hol h k
lemma link (h:Hol D f)(hp: c∈D)(hr:IsOpen D): kPrice (f c):= by obtain ⟨R,hR,hc⟩:=Metric.mem_nhds_iff.mp (hr.mem_nhds hp); exact fee (h.price c (R/2) (half_pos hR) (Subset.trans (closedBall_subset_ball (by linarith)) hc)) ⟨c,mem_closedBall_self (half_pos hR).le⟩
lemma grazes (h:Hol D f)(t:ℝ)(a:ℂ): Hol D (fun i=> plow a t (f i)):= ⟨fun c R hr hu=> plowP (p:=t) (q:=t) (v:=fun _=> t) (fun _=>le_rfl) (fun _=>le_rfl) (h.price c R hr hu) a, fun m _ z hz=> (h.top m _ z hz).const_mul _⟩
end Hol
lemma Hop.crate (h:rPrice U): Hop D (fun _=> U) := ⟨fun _ _ _ _=> transport h, fun _ _ _ _ _ _=> differentiableAt_const _⟩
end YM.MS.Rock
namespace YM.MS.Shine
open Set Filter Function Finset MeasureTheory Metric Arc
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment
open scoped Topology ContDiff
variable {G:Gauge}{b:Bool}{D W:Set ℂ}{R T:ℝ}{c:ℂ}{F H:Mob G}{U:Rip G}{x:ℂ→ℂ}{f g:ℂ→ Mob G}
-- full disk form at shock
end YM.MS.Shine
