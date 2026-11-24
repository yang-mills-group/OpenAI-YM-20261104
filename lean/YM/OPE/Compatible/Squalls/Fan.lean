import YM.OPE.Compatible.Squalls.Pin
/-! # Leading values of individual marched rays. Kernel costs commute earlier. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
lemma ticket_curve (v:ℝ→G.El)(k:G.Color)(j:ℕ)(h:sideLimit (fun t:ℝ=>(t^j)⁻¹ • (G.mat (v t)-1)) (G.colorMat k)): sideLimit (fun t:ℝ=> (t^(2*j))⁻¹ * G.price (v t)) (‖k‖^2/2)∧ sideLimit (fun t:ℝ=> (t^j)⁻¹ • G.curvature (v t)) k:=by
    let V:=fun t:ℝ=> G.mat (v t); constructor
    · have he:= ((h.norm.div_const G.colorScale).pow 2).div_const 2; rw [G.colorMat_norm, mul_div_cancel_left₀ _ G.colorScale_pos.ne'] at he; apply he.congr; intro t
      change ((‖(t^j)⁻¹ • (V t-1)‖/G.colorScale)^2)/2=_; rw [norm_smul,mul_div_assoc]; change ((‖(t^j)⁻¹‖ * G.chord (v t))^2)/2=_; rw [mul_pow,G.chord_price, Real.norm_eq_abs, sq_abs,inv_pow];ring -- test
    have he:= G.projectColor.continuous_of_finiteDimensional.continuousAt.tendsto.comp ((h.sub h.star).const_smul (1/2:ℝ)); rw [G.colorMat_skew,sub_neg_eq_add,← two_smul ℝ,smul_smul,div_mul_cancel₀ _ two_ne_zero,one_smul,G.project_colorMat] at he; apply he.congr; intro t
    change G.projectColor ((1/2:ℝ) • ((t^j)⁻¹ • _-star ((t^j)⁻¹ • _)))=_; unfold Gauge.curvature; rw [star_smul,star_trivial,← smul_sub,star_sub,star_one,sub_sub_sub_cancel_right,smul_comm,map_smul,G.mat_inv]
variable [Fintype I]{x:I→fieldX (Shade G)}{k:I→ℕ}
lemma ticket_spice (h:radiantX x k)(b:Signed)(p:RG.Slot): sideLimit (fun t:ℝ=> (t^2)⁻¹ • p.eval (Bark x k b t)) (CurlX x k b p.plaq):=by
    let A(t:ℝ):= Bark x k b t; let X(t):=travel (A t) 0 p.walk; let q:= CurlX x k b p.plaq; let χ (t):= G.curvature (faceValue (A t) (p.offset,p.plaq))
    have hu : sideLimit (fun t:ℝ=> G.mat (X t)) 1:=by
        suffices h:∀ u:Walk,∀ i:Cover,sideLimit (fun t:ℝ=>G.mat (travel (A t) i u)) 1 from h ..
        intro w i; induction w generalizing i with
        | nil=> simp only [travel,G.mat_one]; exact tendsto_const_nhds
        | cons j w ih=>
           rw [show (fun t:ℝ=>G.mat (travel (A t) i (j::w)))=(fun t=> G.mat (j.read (A t) i)* G.mat (travel (A t) (i+j.vec) w)) from rfl]; apply (show _=_ from (_root_.one_mul (1:G.Mat))) ▸ Tendsto.mul _ (ih _)
           unfold Step.read; cases he:j.neg<;>simp only [Bool.false_eq_true,↓reduceIte,G.mat_inv]; exact landU b _; exact by simpa only [star_one,sideLimit] using (landU (x:=x) (k:=k) b (j.used i)).star -- casts
    have hx: sideLimit (fun t:ℝ=>(t^2)⁻¹ • χ t) q:=(ticket_curve _ _ 2 (face_spine h b p.plaq p.offset)).2
    let P:= G.projectColor.toContinuousLinearMap; let f:= G.colorMat.toContinuousLinearMap
    have ht := P.continuous.continuousAt.tendsto.comp ((hu.mul (f.continuous.continuousAt.tendsto.comp hx)).mul hu.star); erw [star_one,_root_.one_mul,_root_.mul_one,show P (f q)=q from G.project_colorMat q] at ht
    apply ht.congr; intro t; change P (G.mat (X t) * f _ * star (G.mat (X t)))=(t^2)⁻¹ • G.adjoint (X t) (χ t); rw [← map_smul];rfl
end Script
end YM.OPE.Flume
