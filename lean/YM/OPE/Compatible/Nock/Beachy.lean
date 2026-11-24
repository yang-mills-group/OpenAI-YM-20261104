import YM.OPE.Compatible.Nock.Beach
/-!
# Product Gaussian readings and triangular M. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Flock
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset
variable {D E F:Type}[NormedAddCommGroup D][NormedSpace ℝ D][FiniteDimensional ℝ D]
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
def united (A:Law E)(L:Law F): Law (E×F):= by
     let P:(E × F)→ₗ[ℝ] Dual' (E × F):= {
          toFun x:= (A.P x.1).comp (LinearMap.fst ..) + (L.P x.2).comp (LinearMap.snd ..)
          map_add' a b:= by apply LinearMap.ext; intro i; simp; ring
          map_smul' c x:=by apply LinearMap.ext; intro i; simp [map_smul,smul_add] }
     refine Libra.giraffe P ?_ ?_
     · rintro ⟨x,i⟩ ⟨y,j⟩; exact congr_arg₂ (·+·) (A.turns x y) (L.turns i j)
     rintro ⟨x,y⟩ h; obtain ⟨c,hc,H⟩:=A.slope; obtain ⟨b,hb,hK⟩:=L.slope; change 0<A.P x x+ L.P y y; by_cases he:x=0
     · have ht : y≠0:= fun hy=> h (Prod.ext he hy); exact add_pos_of_nonneg_of_pos (by rw [he,map_zero]) (by nlinarith only [mul_pos hb (sq_pos_of_pos (norm_pos_iff.mpr ht)),hK y])
     exact add_pos_of_pos_of_nonneg (by nlinarith only [mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr he)), H x]) (by nlinarith only [mul_nonneg hb.le (sq_nonneg ‖y‖), hK y])
lemma united_shape (A:Law E)(L:Law F)(x y:E×F): (united A L).P x y=A.P x.1 y.1+L.P x.2 y.2:=rfl
lemma formed (A:Law E)(L:Law F)(x:E×F): (united A L).kern x=A.kern x.1*L.kern x.2:=by unfold Law.kern; rw [united_shape,← Real.exp_add]; congr 1; ring
variable [MeasurableSpace D][BorelSpace D][MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F]
variable (μ:Measure E)[μ.IsAddHaarMeasure] (ν:Measure F)[ν.IsAddHaarMeasure]
lemma harvested (P:Law E)(L:Law F)(f:E×F→ℝ)(h:Bond f): (united P L).average (μ.prod ν) f=P.average μ (fun x=> L.average ν (fun y=>f (x,y))):=by
      let Q:=united P L; haveI : (μ.prod ν).IsAddHaarMeasure:=inferInstance
      have he : (∫ x: E×F, (united P L).kern x ∂μ.prod ν)=(∫ x,P.kern x ∂μ)*(∫ x,L.kern x ∂ν):=by simp_rw [formed]; exact integral_prod_mul _ _
      unfold Law.average; rw [he,MeasureTheory.integral_prod _ (show Integrable _ (μ.prod ν) from lumpZ (μ.prod ν) _ f h)]
      simp only [Pi.mul_apply,formed]; simp_rw [show ∀ x:E, ∫ y:F,f (x,y)*(P.kern x*L.kern y) ∂ν= (∫ y:F,f (x,y)*L.kern y ∂ν)*P.kern x from fun i=>by simp_rw [mul_comm (P.kern i),← mul_assoc]; rw [integral_mul_const]] -- rw binder can't?
      simp_rw [div_mul_eq_mul_div]; rw [integral_div]; ring
omit μ ν
end YM.OPE.Libra.Flock
