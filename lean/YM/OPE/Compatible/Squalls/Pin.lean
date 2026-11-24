import YM.OPE.Compatible.Squalls.Prow
/-! # Curvature and value on a scaled ray through translated stencils. explicit colour. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable [Fintype I]
abbrev Bark (x:I→fieldX (Shade G))(k:I→ℕ)(s:Signed)(t:ℝ) : CoverConfig G:=pull s 0 (lotU (spout x k t))
abbrev CurlX (x:I→fieldX (Shade G))(k:I→ℕ)(s:Signed)(p:PlaqAxes):G.Color:= stemDer x k s p.val.2 (step p.val.1)-stemDer x k s p.val.1 (step p.val.2) + G.ad (idleStem x k s p.val.1) (idleStem x k s p.val.2)
variable {x:I→fieldX (Shade G)}{k:I→ℕ}
lemma landU (b:Signed)(i:Edge Cover): sideLimit (fun t:ℝ=>G.mat (Bark x k b t i)) 1:=by
    simp_rw [Bark,tide_pose]; simpa only [G.mat_lieExp_zero,G.mat_one,Function.comp_def,sideLimit] using ((G.continuous_mat.tendsto _).comp ((G.lieExp_cont.tendsto _).comp (spoutX_lil (k:=k) (x:=x) i b)))
lemma arrive_stem (h:radiantX x k)(b:Signed)(i:Edge Cover): sideLimit (fun t:ℝ=> t⁻¹ • (G.mat (Bark x k b t i)-1)) (G.colorMat (idleStem x k b i.2)):=by
    simp_rw [Bark,tide_pose]; have he:= drawn (v:=fun t=> tide i b (spout x k t)) (w:=fun _=> 0) (spoutX_lil i b) tendsto_const_nhds (fun t=>t⁻¹) _ (by simp only [sub_zero]; exact spoutShape h b i.1 i.2)
    simp only [Gauge.mat_lieExp_zero,G.mat_one] at he; exact he
lemma arrive_d (h:radiantX x k)(b:Signed)(i:Edge Cover)(a:Cover): sideLimit (fun t:ℝ=> (t^2)⁻¹ • (G.mat (Bark x k b t (i.1+a,i.2))-G.mat (Bark x k b t i))) (G.colorMat (stemDer x k b i.2 a)):=by
    simp_rw [Bark,tide_pose]; exact drawn _ _ (spoutX_lil _ _) (spoutX_lil _ _) _ _ (spoutShift h b _ _ _)
lemma seesV (U:CoverConfig G) (x:Cover)(a b: Axis)(p:PlaqAxes)(h:p.val=(a,b)):
   faceValue U (x,p) = (U (x,a)*U (x+step a,b))*(U (x,b)*U (x+step b,a))⁻¹:=by
      unfold faceValue; rw [h]; simp only [square,travel, Step.pos_read, Step.neg_read, _root_.mul_one,Step.vec_pos, Step.vec_neg,_root_.mul_inv_rev]; rw [← sub_eq_add_neg,show x+step a+step b-step a=x+step b by abel]; simp only [add_sub_cancel_right,_root_.mul_assoc]
lemma seeCoin {A B:ℝ→G.Mat}{a b:G.Color}
   (hp:sideLimit (fun t:ℝ=> t⁻¹ • (A t-1)) (G.colorMat a))(hq:sideLimit (fun t:ℝ=> t⁻¹ • (B t-1)) (G.colorMat b)):
   sideLimit (fun t:ℝ=> (t^2)⁻¹ • (A t* B t -B t*A t)) (G.colorMat (G.ad a b)):=by
    rw [G.colorMat_ad]; apply ((hp.mul hq).sub (hq.mul hp)).congr; intro t; change t⁻¹ • (A t-1) * (t⁻¹ • (B t-1))- t⁻¹ • (B t-1) * (t⁻¹ • (A t-1))=_; simp_rw [smul_mul_assoc,mul_smul_comm,smul_smul,← sq, inv_pow,← smul_sub]; congr 1; noncomm_ring
lemma face_spine (h:radiantX x k)(b:Signed)(p:PlaqAxes)(a:Cover):sideLimit (fun t:ℝ=> (t^2)⁻¹ • (G.mat (faceValue (Bark x k b t) (a,p))-1)) (G.colorMat (CurlX x k b p)):=by
   let i:= p.val.1; let j:= p.val.2; let V:= Bark x k b; let A(t):= G.mat (V t (a,i)); let B(t):= G.mat (V t (a,j)); let X(t):= G.mat (V t (a+step j,i)); let Y(t):=G.mat (V t (a+step i,j)); let z:= CurlX x k b p
   have he : sideLimit (fun t:ℝ=> (t^2)⁻¹ • (A t*Y t-B t*X t)) (G.colorMat z):=by
       have hA:= (landU (x:=x) (k:=k) b (a,i)).mul (arrive_d h b (a,j) (step i)); have hB:= (landU (x:=x) (k:=k) b (a,j)).mul (arrive_d h b (a,i) (step j)); have hx:= seeCoin (A:=A) (B:=B) (arrive_stem h b (a,i)) (arrive_stem h b (a,j)); simp only [_root_.one_mul] at hA hB; unfold z CurlX; rw [map_add,map_sub]; apply ((hA.sub hB).add hx).congr; intro t; change A t * ((t^2)⁻¹ • (Y t - B t))- B t * ((t^2)⁻¹ • (X t-A t))+(t^2)⁻¹ • (A t*B t-B t*A t)=_; rw [mul_smul_comm,mul_smul_comm,← smul_sub,← smul_add]; apply congr_arg; noncomm_ring
   have hX:= (landU (x:=x) (k:=k) b (a+step j,i)).star
   have hB:= (landU (x:=x) (k:=k) b (a,j)).star
   have hh:= he.mul (hX.mul hB); rw [star_one,_root_.mul_one,_root_.mul_one] at hh; apply hh.congr; intro t
   change ((t^2)⁻¹ • (A t*Y t-B t*X t))*(star (X t)*star (B t))= _; rw [seesV _ _ i j p rfl,G.mat_mul,G.mat_mul,G.mat_inv,G.mat_mul,star_mul,smul_mul_assoc,_root_.sub_mul]; congr 2; rw [← star_mul,show B t*X t=G.mat ((V t (a,j)) * (V t (a+step j,i))) from rfl,G.mat_mul_star]

end Script
end YM.OPE.Flume
