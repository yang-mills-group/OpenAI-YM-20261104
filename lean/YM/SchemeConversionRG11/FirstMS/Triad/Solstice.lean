import YM.SchemeConversionRG11.FirstMS.Triad.Pontryagin
import YM.Pert.Triangle.Subtracted

/-! Two helicity vertices - single FF line. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.Triad
open Function Set Filter MSbar MeasureTheory Metric Complex DR Maxwell Maxwell.Free Pert.Triangle Analysis
open scoped Topology ContDiff BigOperators Classical InnerProductSpace

-- mark i to vertex t. argument z = w -mark.
def clasp (h:Bool)(i:Fin 3)(v:Bool)(m:Fin 3)(t:ℝ)(z:E4):ℝ:= ∑ a:Axis,∑ b:Axis,fan v m a b*surf h i a b t z
lemma clasp_sum (h:Bool)(i:Fin 3)(v:Bool)(m:Fin 3){t:ℝ}{z:E4}(hx : (t,z)≠(0,0)): clasp h i v m t z = -∑ c:Axis,∑ a:Axis,grad a (grad c (soften t)) z*(∑ b:Axis,fan h i c b*fan v m a b):=by
    simp only [clasp,surf_value _ _ _ _ hx, Finset.mul_sum,← Finset.sum_neg_distrib]
    conv_rhs=> rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _=> ?_
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun c _=>by ring

private lemma symmetry {t:ℝ}{z:E4}(hx : (t,z)≠(0,0))(c a:Axis): grad a (grad c (soften t)) z=grad c (grad a (soften t)) z:=by
    have he : t^2+‖z‖^2≠0:= (refilling (t,z) hx).ne'
    rw [soften_second he,soften_second he]; rcases eq_or_ne a c with rfl|hr
    · rfl
    simp only [basis_eq, if_neg hr,if_neg hr.symm]; ring

lemma same (h:Bool)(i m:Fin 3){t:ℝ}{z:E4}(hp:(t,z)≠(0,0)):
    clasp h i h m t z = if i=m then 2⁻¹*source t z else 0 := by
   have he : t^2+‖z‖^2≠0:= (refilling (t,z) hp).ne'
   rw [clasp_sum _ _ _ _ hp]; let H(a c:Axis):= grad a (grad c (soften t)) z; let B(i m:Fin 3)(c a:Axis):=∑ b:Axis,fan h i c b*fan h m a b
   have hh : (∑ c,∑ a,H a c*B i m c a)= ∑ c,∑ a,H a c* B m i c a:= by
      rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun c _=> Finset.sum_congr rfl fun a _=> ?_
      rw [show H c a= H a c from symmetry hp ..]; congr 1; exact Finset.sum_congr rfl fun _ _=> mul_comm ..
   let W:=∑ c,∑ a,H a c*B i m c a
   have hx : W+W= ∑ c:Axis,∑ a:Axis,H a c* (if i=m∧ c=a then 1 else 0):=by
      conv_lhs=> rhs; unfold W; rw [hh];
      unfold W; simp only [←Finset.sum_add_distrib,← mul_add]; simp only [B, fan_anticommute]
   have hd : (∑ c,H c c)=-source t z:= by
      unfold H source; simp only [soften_second he,basis_eq, ↓reduceIte, Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one]
      rw [← Finset.sum_mul]; simp_rw [mul_assoc (8*normal),← sq, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
      field_simp; ring
   change -W=ite _ _ _
   split_ifs with hs
   ·
     simp [hs,mul_ite] at hx
     linarith
   simp [hs] at hx; linarith

lemma mixed_value (i m:Fin 3){w:E4}(hp:w≠0) : clasp true i false m 0 w=mixed i m w := by
   rw [clasp_sum _ _ _ _ (by simp [hp]), mixed_contact _ _ hp]; unfold tensorSum atHessian rotatedProduct
   rw [soften_zero]; congr 1; exact Finset.sum_congr rfl fun c _=> Finset.sum_congr rfl fun a _=> by rw [Hess_sym hp]

lemma minus_zero (h:Bool)(i m:Fin 3){z:E4}(hp:z≠0): clasp h i h m 0 z=0 := by rw [same _ _ _ (by simp [hp])]; simp [source]

-- FF/BF in d, orientation separated.
def spark (d:ℝ×Patch):= d -- dummy

def strike (s:ℂ)(h:Bool)(i:Fin 3)(v:Bool)(m:Fin 3)(z:E4):= ∑ a:Axis,∑ b:Axis,(↑(fan v m a b):ℂ)*bar s h i a b z 0

lemma four_strike {h v:Bool}{i m:Fin 3}{z:E4}(hp:z≠0): strike 0 h i v m z=↑(clasp h i v m 0 z) := by unfold strike clasp; simp_rw [bar_real _ _ _ _ hp,ofReal_sum,ofReal_mul]
lemma strike_analytic {h v:Bool}{i m:Fin 3}{z:E4}(hp:z≠0): AnalyticAt ℂ (fun s=> strike s h i v m z) 0:= by
    have he:(z,(0:ℝ))∈region:= show 0< ‖z‖^2+0 from by rw [add_zero]; exact pow_pos (norm_pos_iff.mpr hp) _
    apply DifferentiableOn.analyticAt _ (opened.mem_nhds occurs)
    intro s hs; exact (DifferentiableAt.fun_sum (u:=Finset.univ) (fun a _=> DifferentiableAt.fun_sum (u:=Finset.univ) (fun b _=> ((off_bar h i a b).colors s hs _ he).const_mul (↑(fan v m a b):ℂ)))).differentiableWithinAt

end YM.SchemeConversionRG11.FirstMS.Triad
