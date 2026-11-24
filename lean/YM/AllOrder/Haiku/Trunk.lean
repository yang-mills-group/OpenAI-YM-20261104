import YM.AllOrder.Response.Vane
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial Asymptotics MeasureTheory
open scoped Topology ContDiff BigOperators Classical
open GaussianScore
open Lattice Gauge RG Wilson Pressure Precision Tree Push Push.Uniform
open ConnectedActivityE6 Blaze Poll PhysicalNext Repeat Local.Vote
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : ℝ → Config G f→ℝ}
   {F J:Forest S.ratio}{O O':ChartRatio G}{k j:S.Choices} (D:Desk F O B k)(H:Desk J O B j)
set_option quotPrecheck false
local notation "K"=> D.paid
local notation "A"=> D.high
local notation "V"=> D.hard
local notation "T"=> fderiv ℝ D.quiet 0
local notation "Γ"=> castle D.hard D.quiet D.pay.steer
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "X"=> Apex c G
local notation "I₀"=> Impulse T A K

lemma postage {P Q:ℝ→ Config G c} {f:ℕ→ℝ} {R:ℝ→Poll.Body (Precision.Key F G)}(H0 : verdict F R B P k f)(ht : P=ᶠ[𝓝 0] Q): verdict F R B Q k f:= by
 apply Laplace.Receipt.moved H0 (Eventually.of_forall fun δ=>?_); filter_upwards [ht.filter_mono (show PertExtension.Series.Tested.germ ≤ 𝓝 0 from nhdsWithin_le_nhds)] with t he; unfold angle collar poundA rootA; rw [he]

variable (hD:0<(D.paid 0))(hO:LocalRatio O)(hS:S.patch.Branches S.kernel G)(hT:∀ t,Toll f (B t))
include hO hD hS hT
lemma tinted {P P':ℝ→Apex c G}(hp:ContDiffAt ℝ ω P 0)(hp':ContDiffAt ℝ ω P' 0) {u:ℝ→(Site c→G.El)} {x:G.El}(hu:Tendsto u (𝓝 0) (𝓝 (fun _=> x)))(hs : courier P' =ᶠ[𝓝 0] fun i=> Lattice.gauge (u i) (courier P i)) : weigh P (ratePlan D)= weigh P' (ratePlan D):= by
 rw [← logprice D hp hD, ← logprice D hp' hD]; let U:=lends hp (ρ:=D.quiet); let U':= lends hp' (ρ:=D.quiet)
 congr 1; exact confirmed_color F (U.w0 ▸ U.progress.continuousAt) (light_courier hp) (sounds D hp hO hS hT) hT hS u x hu rfl ((light_courier hp').congr' hs) _ (U'.w0 ▸ U'.progress.continuousAt) (postage (sounds D hp' hO hS hT) hs)
end YM.AllOrder.Response
