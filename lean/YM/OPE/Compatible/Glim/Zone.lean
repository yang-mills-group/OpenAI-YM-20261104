import YM.OPE.Compatible.Glim.Law
/-! # Lift chart fee.Div identity at finite stand avoiding edge. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {E F I Q:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (u:I→E)(W:I→E→ℝ)(S:Finset I)
lemma prio (J:E→ℝ)(hj:ContDiffAt ℝ ω J 0)(hp:∀ i∈S,ContDiffAt ℝ ω (W i) 0)(hz:(∑ i∈S,(bat (u i) (W i)*J + W i *bat (u i) J))=ᶠ[𝓝 0] (0:E→ℝ)):
    let f(i:I):=Pawn.mold (W i) 0
    divergence u f S * Pawn.mold J 0+ Flux u f S (Pawn.mold J 0)=0:=by
       intro f; let Y (i:I):= bat (u i) (W i)*J+ W i *bat (u i) J; unfold divergence Flux; rw [Finset.sum_mul, ← sum_add_distrib]; rw [show (∑ i∈S,_)=Un E*(∑ i∈S,Pawn.mold (Y i) 0) from ?_]; swap
       · rw [mul_sum]; apply sum_congr rfl; intro i hi; have hx:= hp i hi; have hq:= picked (W i) hx (u i); have he:= picked J hj (u i); unfold Y f; erw [pry_m0 _ hx,pry_m0 _ hj]; rw [meldAdd _ _ (show ContDiffAt ℝ ω (bat _ _*J) _ from hq.mul hj) (show ContDiffAt ℝ ω (W i*bat (u i) J) _ from hx.mul he),meltJ _ _ hq hj,meltJ _ _ hx he]; ring
       rw [← melts Y S (fun i hi=> ((picked _ (hp i hi) _).mul hj).add ((hp i hi).mul (picked _ hj _))),meltSame _ _ (show (∑ i ∈ S,Y i) =ᶠ[𝓝 0] (0:E→ℝ) from hz),show Pawn.mold (0:E→ℝ) 0= _ from ?_,mul_zero]; funext x; exact ((Pawn.calm (contDiffAt_const (c:=(0:ℝ)))).stale x).equality (Reads.constants 0)
variable [Fintype I](p:I)(H:LocalRatio P)
lemma jac_slice(x: Keys G I)(y:G.Color)(t:ℝ):
    let K:=(∏ i∈univ.erase p,Chart.fee P (x i)); let q:= fun i:I=> x i+(t • (Pi.single (M:=fun _:I=>G.Color) p y):Keys G I) i
    Chart.jacobian P q=Chart.fee P (x p+t•y)*K:=by
       intro K q; unfold Chart.jacobian; rw [← mul_prod_erase _ _ (mem_univ p),show q p=_ from (show q p=x p+t•y from by simp[q])]; apply congrArg; apply Finset.prod_congr rfl; intro k hk; simp [q,Pi.single_eq_of_ne (ne_of_mem_erase hk)]
variable (a:G.Color)(b:Bool)(B:Module.Basis G.ColorIndex ℝ G.Color)
local notation "E!"=> Keys G I
include H
lemma jac_gait : ∀ᶠ x:G.Color in 𝓝 0,fderiv ℝ (Chart.fee P) x (Cast b a x) + duty B (fderiv ℝ (Cast b a) x)*Chart.fee P x=0:=by
     let f:G.Color→ℝ:=P.scale • P.J; have he: Chart.fee P =ᶠ[𝓝 0] f:=by filter_upwards [ball_mem_nhds (0:G.Color) H.patch] with x hx; unfold Chart.fee; exact max_eq_left (mul_nonneg H.scale.le (H.pos x hx).le)
     filter_upwards [eventually_eventually_nhds.mpr he,CastPrice b a H B,ball_mem_nhds (0:G.Color) H.patch] with x hx h hq
     change Chart.fee P =ᶠ[𝓝 x] f at hx; rw [hx.eq_of_nhds,hx.fderiv_eq]; unfold f; rw [fderiv_const_smul]; simp only[_root_.smul_apply,Pi.smul_apply,smul_eq_mul]; rw [mul_left_comm (duty ..),← mul_add, h,mul_zero]; exact (H.germ x hq).differentiableAt (by simp)
noncomputable abbrev tou (b:Bool)(a:G.Color)(v:G.ColorIndex): E!→ℝ:=fun x=> B.coord v (Cast b a (x p))
omit H
noncomputable abbrev An (i:G.ColorIndex) : Keys G I:= Pi.single p (B i)
lemma CharterS (i:G.ColorIndex) : ContDiffAt ℝ ω (tou p B b a i) 0:= by
     let v:= (B.coord i).toContinuousLinearMap; exact v.contDiff.contDiffAt.comp _ ((cast_sm b a).comp (f:=fun x:E!=>x p) 0 (contDiffAt_apply ..))
include H
lemma winds' : (∑ i:G.ColorIndex,(bat (An p B i) (tou p B b a i)*Chart.jacobian P + tou p B b a i * bat (An p B i) (Chart.jacobian P)))=ᶠ[𝓝 0] (0:E!→ℝ) :=by
      have ht:= jac_gait H a b B; have hx:= Chart.Ratio.jacobian_smooth H (U:=I); let u:E!→L[ℝ] G.Color:= ContinuousLinearMap.proj p
      filter_upwards [(u.continuous.tendsto 0).eventually ht, (u.continuous.tendsto 0).eventually ((cast_sm b a).eventually (by simp)),hx.eventually (by simp), (u.continuous.tendsto 0).eventually ((Chart.Ratio.fee_smooth H).eventually (by simp))] with x he hq hf hh
      let J:= Chart.fee P; let C:=∏ i∈univ.erase p,J (x i); have hU: Chart.jacobian P x= J (u x)*C:= by rw [Chart.jacobian, ← mul_prod_erase _ _ (mem_univ p)]; rfl
      have hp(i:G.ColorIndex): bat (An p B i) (tou p B b a i) x=B.coord i (fderiv ℝ (Cast b a) (x p) (B i)):=by
           unfold bat tou; let f:= (B.coord i).toContinuousLinearMap; change fderiv ℝ (f ∘ Cast b a ∘ u) x _=f _; rw [fderiv_comp x f.differentiableAt ((hq.differentiableAt (by simp)).comp x u.differentiableAt), fderiv_comp x (hq.differentiableAt (by simp)) u.differentiableAt,u.fderiv,f.fderiv]; simp only[ContinuousLinearMap.comp_apply,u,ContinuousLinearMap.proj_apply,Pi.single_eq_same]
      have hQ(y:G.Color): fderiv ℝ (Chart.jacobian P) x (Pi.single p y)=C * fderiv ℝ J (u x) y:=by
           let w(t:ℝ):=x+t • (Pi.single p y:E!); have hw:w 0=x:=by simp [w]
           have hy:HasDerivAt w (Pi.single p y) 0:=by unfold w; simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const (Pi.single p y)).const_add x
           apply HasDerivAt.unique ((show HasFDerivAt (Chart.jacobian P) (fderiv ℝ (Chart.jacobian P) x) (w 0) by rw [hw]; exact ((show ContDiffAt ℝ ω (Chart.jacobian P) x from hf).differentiableAt (by simp)).hasFDerivAt).comp_hasDerivAt 0 hy)
           rw [show Chart.jacobian P ∘ w=(fun i:ℝ=> C * (J (x p+i • y))) from funext fun i=>(jac_slice p x y i (P:=P)).trans (mul_comm ..)]
           refine HasDerivAt.const_mul _ ?_; have h: HasDerivAt (fun i:ℝ=>x p+i • y) y 0 := by simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const y).const_add (x p)
           exact HasFDerivAt.comp_hasDerivAt 0 (show HasFDerivAt J (fderiv ℝ J (u x)) (x p+(0:ℝ) • y) from (by rw [zero_smul,add_zero]; exact (hh.differentiableAt (by simp)).hasFDerivAt)) h
      rw [Finset.sum_apply]; simp_rw [Pi.add_apply,Pi.mul_apply,hp]; rw [sum_add_distrib]; simp_rw [hU]; rw [← sum_mul]; let z:= Cast b a (x p); have hb(i:G.ColorIndex) := hQ (B i);
      change duty B (fderiv ℝ (Cast b a) (u x))* (J _*C)+(∑ i, (B.coord i z * fderiv ℝ (Chart.jacobian P) x (An p B i)))=0
      simp_rw [hb,mul_left_comm (B.coord _ _) C,← mul_sum]; have hv:(∑ i, B.coord i z * (fderiv ℝ J (u x) (B i)))=fderiv ℝ J (u x) z:=by symm; nth_rw 1 [← B.sum_repr z];rw [map_sum]; apply sum_congr rfl; intro i _; exact map_smul (fderiv ℝ J (u x)) _ _
      rw [hv, show ∀ v: E!,u v=v p from fun _=>rfl]; change fderiv ℝ J (x p) z+ duty B (fderiv ℝ (Cast b a) (x p))*J (x p)=0 at he; linear_combination C*he
end YM.OPE.Variance
