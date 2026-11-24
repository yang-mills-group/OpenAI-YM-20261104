import YM.AllOrder.Laplace.Bright
import YM.AllOrder.Local.Render
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Metric Filter
open scoped Topology ENNReal ContDiff Classical MatrixOrder
open Lattice Wilson RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext Repeat Lapis Lantern Fare Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 Blaze Brush Poll Coat
open scoped BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}
variable (F: Forest S.ratio) (O: ChartRatio G)(k:S.Choices) (R:PathData G)(p:Clip)
local notation "K"=>Precision.Key F G
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "X"=> Apex c G
local notation "A"=> Lapis.table F k R p
local notation "Ω"=> ℝ×(X×Y)
variable {C q L :ℝ}{n:ℕ} {ρ : Bid.Dir G c→AxisChart G F} (T:Push.Uniform.Before G q C S.patch.J S.kernel (n+3))
   (hG:Bid.Larger (G:=G) S)(h:R.Bounds p q C L)(he:T.Service F p R ρ)(hO:LocalRatio O)
local notation "Y0"=> orbit F ρ
local notation "K0"=> gram F R p ρ k 0
include T hG h he
lemma curvature_spine (y:Y) : Laplace.curvature A 0 y = 1/2 * dotProduct y.ofLp (K0*ᵥ y.ofLp):= by
   obtain ⟨-,-,-,H⟩:=wakes F k R p ρ q C L T hG h he 0 (by rw [norm_zero]; exact he.x_pos); unfold Laplace.curvature; rw [H,zeroO F R p ρ q C T he,jet_two_H]; simp only [one_div]; rfl -- h y
lemma interest : Steered (Lapis.table F k R p) (orbit F ρ):= by
   obtain ⟨hx,hk,hg,-⟩:= price_identity F k h hG.1; let Cmap:= (paint F G).toContinuousLinearMap ∘L (combineH (G:=G) F).toContinuousLinearMap -- paint args
   let s:= uncurry (tested F k p R); change s 0=0 at hk; change ContDiffAt ℝ ω s 0 at hx
   have hw:ContDiffAt ℝ ω A 0:= (show ContDiffAt ℝ ω s (Cmap 0) from (by rw [_root_.map_zero]; exact hx)).comp _ Cmap.contDiff.contDiffAt
   have hp:HasFDerivAt (𝕜:=ℝ) A 0 0:= by
      have hh:HasFDerivAt (𝕜:=ℝ) s 0 (Cmap 0):=by rw [_root_.map_zero]; exact hg ▸ (hx.differentiableAt (by simp)).hasFDerivAt
      simpa only [ContinuousLinearMap.zero_comp] using! (hh.comp 0 Cmap.hasFDerivAt)
   have hz0:ContDiffAt ℝ ω (orbit F ρ) 0:= (((weld K).symm).contDiff.contDiffAt).comp _ (he.series (mem_ball_self he.x_pos))
   have h' := zeroO F R p ρ q C T he
   refine ⟨hw,hk,hp.fderiv,h',hz0,curvature_separate A Y0 hw hz0 h' ?_,?_⟩
   · intro z; exact (show ∀ᶠ x in 𝓝 (0:Apex c G), x∈ ball 0 (T.tables p S.patch).horizon from ball_mem_nhds _ he.x_pos).mono fun x hx=> heart F k R p ρ q C L T hG h he x (mem_ball_zero_iff.mp hx) z
   intro x hx; have hh := (wakes F k R p ρ q C L T hG h he 0 (by simp [he.x_pos])).1; rw [curvature_spine F k R p T hG h he]
   apply mul_pos (by norm_num); simpa using hh.dotProduct_mulVec_pos (show x.ofLp ≠ 0 from fun h=> hx ((WithLp.equiv ..).injective h))
include hO
omit hG he in
lemma mist_nice : ContDiffAt ℝ ω (mist F O R) 0:= by
 let Y₀:=Positions (Joint F G); let F₁: Y₀→ℝ:=perch F R
 have ha: ContDiffAt ℝ ω F₁ 0:= by
    unfold F₁ perch Precision.loop uncut Patch.average Function.comp; apply contDiffAt_const.mul; refine ContDiffAt.sum fun s _=>ContDiffAt.sum fun i _=>?_ ; exact label_analytic F _ h.width h.two s T.labels i 0 (mem_ball_self (by norm_num)) -- args
 have hB: ContDiffAt ℝ ω (sumAt F O) 0:= by
    refine ContDiffAt.sum fun i _=>?_ ; let L:= (Hmap F G i) ∘L (weld K).toContinuousLinearMap
    have hh : L 0=0:=_root_.map_zero _; apply ContDiffAt.comp (g:=fun x=> Real.log (O.J x)) (f:=L) _ _ L.contDiff.contDiffAt
    exact hh.symm ▸ (hO.germ 0 (mem_ball_self hO.patch)).log (hO.anchored.trans_ne one_ne_zero)
 let v:=combineH (G:=G) F; have hh:v 0=0:= _root_.map_zero _; refine (ContDiffAt.comp (g:=F₁) (f:=v) (0:Apex c G×Y) (hh.symm ▸ ha) v.contDiff.contDiffAt).sub (show ContDiffAt ℝ ω (Lapis.sumAt F O ∘ Prod.snd) (0:X×Y) from hB.comp (f:=Prod.snd) (0:X×Y) contDiffAt_snd)

abbrev primitive (n:ℝ)(V:Config G f):=mainTerm p R V+n^2*Precision.loop R V
def fixed : Ω→ℝ:= fun x=>O.scale^Fintype.card F.Free*Real.exp (-mist F O R x.2)
def startup (T:Push.Uniform.Before G q C S.patch.J S.kernel (n+3)) (hG:Bid.Larger (G:=G) S)(h:R.Bounds p q C L)(he:T.Service F p R ρ)(hO:LocalRatio O) : Desk F O (primitive (f:=f) R p) k where
   hard:=A
   quiet:=Y0
   high:= A ∘ Prod.snd
   paid:=fixed F O R
   pay:= by
      have he:= interest F k R p T hG h he
      have hp: ContDiffAt ℝ ω (fun x:Ω=> mist F O R x.2) 0:=(mist_nice F O R p T h hO).comp (f:=Prod.snd) (0:Ω) contDiffAt_snd
      exact ⟨he,he.hard.comp (f:=Prod.snd) 0 contDiffAt_snd,fun i _=> rfl,contDiffAt_const.mul (hp.neg.exp)⟩
   aff:= by
      let f (x: X):= represent (tint G _ x)
      have hh : Tendsto (fun x:Ω=> x.2.2) (𝓝 0) (𝓝 0):= (continuous_snd.comp continuous_snd).continuousAt.tendsto
      filter_upwards [hh.eventually (wind_gate F O hO)] with q hq ht; obtain ⟨t,x,y⟩:=q; dsimp only at ht; let u:= F.drape (draw F (f x) y)
      let g:= mainTerm p R u +noiseTaylor S (f x) u k; let b := Precision.loop R u; let a:= O.scale^Fintype.card F.Free
      have hu: Next.SectorChange.pay O (windmill F y)= a* Real.exp (Lapis.sumAt F O y):=by
         unfold Next.SectorChange.pay a sumAt; rw [Real.exp_sum,Finset.prod_mul_distrib,Finset.prod_const,card_univ]; apply congr_arg; refine Finset.prod_congr rfl (fun i hi=> ((Real.exp_log (hO.pos _ (hq i (Set.mem_univ _)))).symm))
      change Real.exp (-(mainTerm p R u+t^2*b+noiseTaylor S (f x) u k)/t^2)*_= Real.exp (-A (x,y)/t^2)*(a*Real.exp (-mist F O R (x,y)))
      rw [hu,Lapis.plume]; change _= Real.exp (-g/ t^2)*(a*Real.exp (-(b-Lapis.sumAt F O y)))
      rw [show -(mainTerm p R u+t^2*b+noiseTaylor S (f x) u k)/t^2= -g/t^2 - b from (by unfold g; field_simp; ring), mul_left_comm _ a, mul_left_comm (Real.exp (-g/t^2)) a, ← Real.exp_add, ← Real.exp_add]; ring_nf
end YM.AllOrder.Laplace
