import YM.AllOrder.Response.Thermal
import YM.AllOrder.Laplace.Native
/-!
# The signed, gauge-coherent formal vacuum operator on every finite period

Template on any symmetric <invariant> input `B` (not presumed uniform)
whose cylinder is supplied already. This predicates propagational
staging, not a definition of higher perturbative coefficients by reading
from the TRUE hierarchy. `seed_shadow` proves cap4+ trajectory applicability
for pure inputs with its K stencil & grip (see `MSC`).
-/
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

def preview (D:Desk F O B k):= Real.log (D.paid 0 * capital (castle D.hard D.quiet D.pay.steer) volume)
def distilled:Book (Apex c G):=connected Γ volume I₀
/-- Includes scalar affine term, the leading free Hessian and vacuum unit together. -/
def ratePlan (D:Desk F O B k):Book (Apex c G):= wirings (fun x=> preview D-liftQ D.hard (fderiv ℝ D.quiet 0) x)+distilled D
lemma all_cost : ∀ i,Plausible (ratePlan D i):= by
 intro i; let a x:= preview D-liftQ V T x; have he:Plausible a:= (Plausible.atom (preview D)).sub (lift_cost V T)
 apply Plausible.add (f:=wirings a i) _ (climbers volume (fun i=> impulse_cost T A K i) (win0 _) i); by_cases hi:i=0; exact hi.symm ▸ he; rw [show wirings a i=(fun (_:X)=>0) from funext fun _=> if_neg hi]; exact Plausible.atom _
def courier (P:ℝ→Apex c G):= Desk.night ∘ echo P
variable {P P':ℝ→Apex c G}(hp:ContDiffAt ℝ ω P 0)
include hp in
lemma light_courier : Tendsto (courier P) (𝓝 0) (𝓝 1):= by
   have hu:Tendsto (echo P) (𝓝 0) (𝓝 0):=(show echo P 0=0 from zero_smul ..) ▸ ((show ContDiffAt ℝ ω (echo P) 0 from contDiffAt_id.smul hp).continuousAt) -- invalid args
   have hv:Desk.night (0:X)= (1:Config G c):=by unfold Desk.night; rw [_root_.map_zero,Precision.link_one]
   exact ((show Tendsto (Desk.night (c:=c) (G:=G)) (𝓝 0) (𝓝 (1:Config G c)) from hv ▸ (nights (G:=G) (c:=c)).continuousAt.tendsto)).comp hu

def grants (P:ℝ→Apex c G) := D.drawdown (echo P) (trust P (fderiv ℝ D.quiet 0))
variable (he:0<D.paid 0)
include hp he in
lemma logprice : logS (grants D P)=weigh P (ratePlan D):= by
   set r:=1-D.perk (echo P) (trust P (fderiv ℝ D.quiet 0))
   have h := thermal volume D.pay hp he (r:=r) (show 0<D.perk (echo P) (trust P (fderiv ℝ D.quiet 0))+r by dsimp only [r]; simp); unfold grants Desk.drawdown Desk.issued; rw [h]; let f:= -forecast V P T; let a x:=preview D-liftQ V T x; have ht:Plausible a:=(Plausible.atom (preview D)).sub (lift_cost V T)
   funext i; change _=weigh P (wirings a + distilled D) i; rw [weigh_add hp (v:=distilled D) (install_just _ ht.smooth.contDiffAt) (fun i _=> (climbers volume (fun i=> impulse_cost T A K i) (win0 _) i).smooth.contDiffAt) (le_refl i),just_read hp ht.smooth.contDiffAt, show a ∘ P=(fun (_:ℝ)=>preview D)-forecast V P T from rfl,some_sub (G:=forecast V P T) contDiffAt_const ((lift_cost V T).smooth.contDiffAt.comp _ hp),show someJ _=just (preview D) from funext fun i=> (Act.static (n:=i) (preview D)).writes _ le_rfl]; rfl
variable (hO:LocalRatio O)(hS:S.patch.Branches S.kernel G)(hT:∀ t,Toll f (B t))
include hO hS hT hp
lemma sounds : verdict F (trust P (fderiv ℝ D.quiet 0)) B (courier P) k (grants D P) := Desk.award (L:=D) hS hO hT (lends hp)
include he
lemma coherent (he':0<H.paid 0): weigh P (ratePlan D)=weigh P (ratePlan H):= by
  rw [← logprice D hp he, ← logprice H hp he']; let h:=lends hp (ρ:=D.quiet); let H':=lends hp (ρ:=H.quiet)
  congr 1; exact confirmed_cross F (h.w0 ▸ h.progress.continuousAt) (H'.w0 ▸ H'.progress.continuousAt) (light_courier hp) (sounds D hp hO hS hT) hT hS (sounds H hp hO hS hT)
omit hp in
lemma exactly (he':0<H.paid 0) : ratePlan D=ratePlan H := by
   funext i x; have he:=congr_fun (coherent D H (P:=fun _=>x) contDiffAt_const he hO hS hT he') i; rw [weigh_const,weigh_const] at he; exact he
lemma colored (hp':ContDiffAt ℝ ω P' 0) {u:ℝ→(Site c→G.El)} {x:G.El}(hu:Tendsto u (𝓝 0) (𝓝 (fun _=> x)))(hs : ∀ i,courier P' i=Lattice.gauge (u i) (courier P i)): weigh P (ratePlan D) = weigh P' (ratePlan D) := by
   rw [← logprice D hp he, ← logprice D hp' he]; let H:=lends hp (ρ:=D.quiet); let H':=lends hp' (ρ:=D.quiet)
   congr 1; exact confirmed_color F (H.w0 ▸ H.progress.continuousAt) (light_courier hp) (sounds D hp hO hS hT) hT hS u x hu (funext hs) (light_courier hp') _ (H'.w0 ▸ H'.progress.continuousAt) (sounds D hp' hO hS hT)
open AnalyticBridge.GaussianFieldAlignment Locations
lemma balanced (s:Signed)(x:Site c)(H:Desk (Locations.forest s x F) O B j)(he':0<H.paid 0)(hp':ContDiffAt ℝ ω P' 0) (hc: courier P'= pull s x ∘ courier P): weigh P (ratePlan D)=weigh P' (ratePlan H):= by
   rw [← logprice D hp he, ← logprice H hp' he']; let q:=lends hp (ρ:=D.quiet); let q':=lends hp' (ρ:=H.quiet)
   congr 1; exact confirmed_pulled F (q.w0 ▸ q.progress.continuousAt) (light_courier hp) (sounds D hp hO hS hT) hT hS s x hc (light_courier hp') _ (q'.w0 ▸ q'.progress.continuousAt) (sounds H hp' hO hS hT)
-- centered graph prediction literal worsch. remove const normalization via local comparison; Dependence in const agreement with solar separately, priced only off.
omit hS hT hp he
variable (F k) (U : Pressure.Tube G S) {σ C L:ℝ}{n:ℕ}{ρ: Bid.Dir G c→AxisChart G F}(Q : Push.Uniform.Before G σ C S.patch.J S.kernel (n+3))(hG:Bid.Larger (G:=G) S)(hB:U.up.Bounds U.high σ C L)(h:Q.Service F U.high U.up ρ) -- typo
lemma seed_shadow (x:Apex c G) (i:ℕ): let D:=startup F O k U.up U.high Q hG hB h hO; ratePlan D i x= just (Real.log (scaleP (ρ:=ρ) F O k U)) i + Local.Pure.flip F U O ρ k i x := by
 intro D; have he:logS (grants D (fun _=>x))= Function.swap (ratePlan D) x:= (logprice D (P:=fun _=>x) contDiffAt_const (by change 0<O.scale^Fintype.card F.Free*Real.exp _; exact mul_pos (pow_pos hO.scale _) (Real.exp_pos _))).trans (weigh_const _)
 have hp:= voted F O k U Q hG hB h hO x i; let P':= echo (fun (_:ℝ)=>x); let hT:= lends (ρ:=D.quiet) (P:=fun _=>x) contDiffAt_const; let H:= belong D.pay.steer hT.p0 hT.cont;
 have hg:grants D (fun _=>x)=D.drawdown P' (D.quiet ∘ P'):= by
   let hV (t:ℝ) : Toll f (primitive U.up U.high t):= (toll_main hB).add ((toll_loop hB).scale (t^2))
   exact confirmed_cross F (hT.w0 ▸ hT.progress.continuousAt) (H.w0 ▸ H.progress.continuousAt) (light_courier (P:=fun (_:ℝ)=>x) contDiffAt_const) (sounds D contDiffAt_const hO hG.1 hV) hV hG.1 (Desk.award hG.1 hO hV (L:=D) H)
 rw [show ratePlan D i x=_ from (congr_fun he i).symm, hg]; exact hp
end YM.AllOrder.Response
