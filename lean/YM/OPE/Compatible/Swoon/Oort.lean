import YM.OPE.Compatible.Swoon.Worn
/-!
# log hats at second order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Coin
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset Matrix LinearMap Flock
variable {G:Gauge}{I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
open YM.Stationary -- avoid Radial.Stationary
attribute [local instance] Gauge.frobInner
local notation "W"=>Keys G I
lemma njet (f:E→ℝ)(x:E): jet f 2 x=iteratedFDeriv ℝ 2 f 0 ![x,x]/2:=by rw [jet,show (fun _ :Fin 2=>x)=![x,x] from funext fun i=>by fin_cases i <;> rfl]; norm_num;ring
lemma jetExp2 (f:E→ℝ)(x:E)(h:ContDiffAt ℝ ω f 0)(hp:fderiv ℝ f 0=0): jet (Real.exp∘f) 2 x= Real.exp (f 0)*jet f 2 x:=by
     rw [njet,njet,pay_second (show ContDiffAt ℝ ω Real.exp (f 0) from Real.contDiff_exp.contDiffAt) h,hp, _root_.zero_apply]; have ht: iteratedFDeriv ℝ 2 Real.exp (f 0) ![0,0]=0:=by
           exact ContinuousMultilinearMap.map_coord_zero _ (0:Fin 2) rfl
     rw [ht,add_zero, show fderiv ℝ Real.exp (f 0)=_ from (Real.hasDerivAt_exp (f 0)).hasFDerivAt.fderiv]; simp;ring
variable [Fintype I]
def FlumeCoinAdj (p:ChartRatio G)(x:Keys G I):= ∑ i:I,(Real.log p.scale+ Real.log (p.J (x i)))
open Metric
lemma jake (p:ChartRatio G)(h:LocalRatio p) : ∀ᶠ x:W in 𝓝 0,0<Chart.jacobian p x∧ Real.log (Chart.jacobian p x)=FlumeCoinAdj p x := by -- define below
    filter_upwards [Metric.ball_mem_nhds (0:W) h.patch] with x hx
    have hp(j:I): x j ∈ Metric.ball 0 p.radius:=by rw [ball_pi _ h.patch] at hx; exact hx j (Set.mem_univ _)
    have hh(j:I):0<p.scale * p.J (x j):=mul_pos h.scale (h.pos _ (hp j))
    unfold Chart.jacobian Chart.fee; simp_rw [max_eq_left (hh _).le]; refine ⟨prod_pos (fun i _=> hh i),?_⟩; rw [Real.log_prod (fun i _=> (hh i).ne')]; exact sum_congr rfl (fun i _=> Real.log_mul h.scale.ne' (h.pos _ (hp i)).ne')
def looper (p: ChartRatio G) (x:Keys G I):= ∑ i:I,Real.log (p.J (x i))
def jackpot (p:ChartRatio G)(I:Type)[Fintype I]:= ∑ _ : I,Real.log p.scale
lemma parW (p:ChartRatio G)(h:LocalRatio p): Chart.jacobian p (U:=I) =ᶠ[𝓝 0] Real.exp ∘ ((looper p)+ fun _=>jackpot p I):=by filter_upwards [jake (I:=I) p h] with x hx; rw [← Real.exp_log hx.1,hx.2, FlumeCoinAdj,sum_add_distrib]; rw [add_comm]; rfl
lemma pals (p:ChartRatio G)(h:LocalRatio p): ContDiffAt ℝ ω (looper p (I:=I)) 0∧ fderiv ℝ (looper p (I:=I)) 0=0:=by
    let U(i:I): W→ℝ:= fun x=> Real.log (p.J (x i)); let R(i:I): W→L[ℝ] G.Color:= ContinuousLinearMap.proj i; let Q:=Real.log ∘ p.J; obtain ⟨hx,hQ⟩ := YM.OPE.Flume.Virgin.jet_trunk h; have hv(i:I): ContDiffAt ℝ ω (U i) 0:= hx.comp (f:=R i) 0 (R i).contDiff.contDiffAt; refine ⟨ContDiffAt.sum fun i _=> hv i,?_⟩
    rw [show looper p (I:=I)=fun x=> ∑ i:I,U i x from rfl,fderiv_fun_sum (fun i _=> (hv i).differentiableAt (by simp))]; refine sum_eq_zero fun i _=>?_ ; change fderiv ℝ (Q ∘ R i) 0=0; rw [fderiv_comp (0:W) (show DifferentiableAt ℝ Q (R i 0) from hx.differentiableAt (by simp)) (R i).differentiableAt,show fderiv ℝ Q ((R i) 0)=0 from hQ];rfl
-- Λ for token
abbrev flareTok (u v:ℝ): Token:= ⟨1,u,v+u^2/2⟩
lemma blazeTok (u v s t:ℝ): flareTok u v * flareTok s t= flareTok (u+s) (v+t):=by apply JetS.eta <;>simp only [JetS.ml_s,JetS.ml_h,JetS.ml_l,flareTok] <;> ring
lemma keyWarm (D:Lid G I)(p:ChartRatio G)(h:LocalRatio p)(u: W→ℝ)(hp:D.w=ᶠ[𝓝 0] Real.exp ∘ u) (hh:ContDiffAt ℝ ω u 0)(hk:fderiv ℝ u 0=0)(x:W):
    D.hat p x= flareTok (-jet D.f 3 x) (-jet D.f 4 x + jet u 2 x + jet (looper p) 2 x):=by
     let V:=looper p (I:=I); let t:=jackpot p I; let W':= u +V+ fun (_:W)=> t; let P:=warmer p D.w; have he : P =ᶠ[𝓝 0] Real.exp ∘ W':=by
          filter_upwards [hp,parW (I:=I) p h] with i hi hb; unfold P warmer; simp only [Pi.mul_apply]; rw [hi,hb]; simp [_root_.Function.comp_apply,← Real.exp_add,W', V,t, add_assoc]
     obtain ⟨hV,hM⟩:= pals (I:=I) p h; have hz:ContDiffAt ℝ ω V 0:=hV; have hb: ContDiffAt ℝ ω W' 0:= (hh.add hz).add contDiffAt_const; have hA: fderiv ℝ W' 0=0:=by unfold W'; rw [fderiv_add (f:=u+V) ((hh.add hz).differentiableAt (by simp)) (differentiableAt_const _),fderiv_add (hh.differentiableAt (by simp)) (hz.differentiableAt (by simp)),hk,show fderiv ℝ V 0=0 from hM, fderiv_const_apply, add_zero,add_zero]
     have ht: jet P 1 x=0:=by unfold jet; rw [iteratedFDeriv_one_apply,he.fderiv_eq,fderiv_comp _ (Real.differentiableAt_exp) (hb.differentiableAt (by simp)),hA];simp
     have hF: jet P 2 x=P 0*(jet u 2 x+jet V 2 x):=by
            rw [show jet P 2 x=jet (Real.exp ∘ W') 2 x from (by rw [njet,njet,(he.iteratedFDeriv ℝ 2 |>.eq_of_nhds)]), jetExp2 _ x hb hA, he.eq_of_nhds]; congr 1
            rw [njet,njet,njet]; unfold W'; rw [iteratedFDeriv_add_apply (f:=u+V) ((hh.add hz).of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne (by decide), Pi.zero_apply,add_zero, iteratedFDeriv_add_apply (hh.of_le le_top) (hz.of_le le_top), _root_.add_apply,add_div]
     let a:= D.seedPrice p; have ha: a≠0:= (D.seed_pos h).ne'; have hy:= jet_zero P x
     apply JetS.eta; · exact D.hat_full h x
     · rw [Lid.hat, Lid.heat]; simp only [JetS.ml_l,JetS.plain_l,JetS.plain_s,zero_mul,add_zero,Pi.mul_apply]; change a⁻¹*(jet P 0 x*(-jet D.f 3 x)+jet P 1 x*1)= -jet D.f 3 x; rw [hy, ht]; change _*(a*_+_)=_; field_simp;simp
     rw [Lid.hat,Lid.heat]; simp only [JetS.ml_h,JetS.plain_s,JetS.plain_l,JetS.plain_h,zero_mul,add_zero,Pi.mul_apply]; change a⁻¹ * (jet P 0 x*(-jet D.f 4 x + (jet D.f 3 x)^2/2)+ jet P 1 x*_+jet P 2 x*1)= -jet D.f 4 x+_+jet V 2 x+_; rw [hy,ht,hF]; change a⁻¹*(a* _+ 0*_+a* _*1)=_; field_simp; ring
end YM.OPE.Libra.Coin
