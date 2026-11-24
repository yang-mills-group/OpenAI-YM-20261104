import YM.Pert.Triangle.ScalarFan
import YM.Pert.Triangle.Identities
import YM.Pert.Scale.Radial

/-! Diagonal in the mixed helicity transfer along a ray (off origin). Half per ordered fan contraction,
orthonormal on positive curvature pairs. For a potential-to-curvature line the derivative is at the
field position, not at the integration endpoint. -/

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric
open scoped ContDiff Topology RealInnerProductSpace Classical
local notation "I3" => Fin 3

def mixed (i j : I3) (w : E4) := (1/4:ℝ) * ∑ a,∑ b, fan true i a b * (∑ c,∑ d,fan false j c d * bareCurl a b c d w)
def tensorSum (i j : I3) (H : Axis→Axis→ℝ) := ∑ a,∑ c, H a c * rotatedProduct true i false j a c
lemma contraction_fans (i j : I3) (H : Axis→Axis→ℝ) :
    rawPair H true i false j = -4 * tensorSum i j H := by
  let Y := fan false j
  let X := fan true i
  change (∑ a,∑ b, X a b * fanRow H Y a b) = _
  simp only [show ∀ a b, fanRow H Y a b= 2 * contractionHalf H Y a b - 2 * contractionHalf H Y b a from (fun a b => by
       rw [partial_row H Y (fan_flip false j)]; ring)]
  simp_rw [mul_sub,show ∀ (A B:ℝ),A*(2*B)=2*(A*B) from fun _ _=>by ring,Finset.sum_sub_distrib,←Finset.mul_sum]
  have he : (∑a,∑b, X a b * contractionHalf H Y b a) = -(∑a,∑b, X a b * contractionHalf H Y a b) := by
    rw [Finset.sum_comm]; simp_rw [←Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _=> Finset.sum_congr rfl fun a _=>congrArg (fun t:ℝ=>t * contractionHalf H Y b a) (fan_flip true i b a) |>.trans (neg_mul ..)
  rw [he,sumHalf X Y H (fan_flip false j)]; unfold X Y fan at * -- only at end use definition?
  unfold tensorSum rotatedProduct fan; ring

lemma mixed_contact (i j : I3) {w : E4} (hw : w ≠ 0) : mixed i j w = -tensorSum i j (atHessian w) := by
  rw [show mixed i j w = (1/4:ℝ) * rawPair (atHessian w) true i false j from ?_]
  · rw [contraction_fans]; ring
  unfold mixed rawPair fanRow bareCurl atHessian; simp only [Pi.sub_apply,Bare.opp_grad hw,entry]
lemma mixed_rays (i j : I3) : Scale.Rays (mixed i j) 4 where
  diff := fun hx => by
    unfold mixed
    refine contDiffAt_const.mul (ContDiffAt.sum ?_); intro a _
    refine ContDiffAt.sum ?_; intro b _
    refine contDiffAt_const.mul (ContDiffAt.sum ?_); intro c _
    refine ContDiffAt.sum ?_; intro d _
    exact contDiffAt_const.mul (Scale.uncolored _ _ _ _ |>.diff hx)
  stretch := fun {_} hx {u} ha => by
    simp only [smul_eq_mul, mixed, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro d _
    rw [show ∀ u v t q s : ℝ, u*(v*(t*(q*s)))=v*(t*(q*(u*s))) from fun _ _ _ _ _=>by ring]
    rw [show u^4 * _ = _ from (Scale.uncolored _ _ _ _).stretch hx ha]

def rawProduct (i j : I3) a c := rotatedProduct true i false j a c
def atTensor (i j : I3) (w : E4) := ∑ a,∑ c, (w a * w c) * rawProduct i j a c
section
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
attribute [-instance] Classical.propDecidable
lemma int_trace : ∀ i j, (∑ a:Axis,∑ b:Axis, fanI true i a b * fanI false j a b) = 0 := by decide
lemma int_firstrow : ∀ i j, (∑ b:Axis, fanI true i 0 b * fanI false j 0 b) = if i=j then 1 else 0 := by decide
def rawThird (m t n : I3) (u v : Axis) := ∑ a:Axis,∑ b:Axis, fanI false m u a * fanI false t a b * fanI false n v b
lemma int_crush : ∀ m t n u v, rawThird m t n u v + rawThird m t n v u = if u=v then 2 * eps3 m t n else 0 := by decide
lemma eps_flip : ∀ m i n, eps3 m i n = -eps3 i m n := fun m i=> eps_swap12 i m
lemma eps_nonzero_int : (∑ i,∑ m,∑ n,eps3 i m n * eps3 m i n) = -6 := by decide
end
lemma product_rule (i j : I3) (a c : Axis) : rawProduct i j a c = (2:ℝ)⁻¹ * ((∑ b,fanI true i a b * fanI false j c b :ℤ) : ℝ) := by
  unfold rawProduct rotatedProduct; rw [Int.cast_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _=> by rw [fan,fan,div_mul_div_comm,sqrt_two_rule]; push_cast; ring)
lemma trace_rule (i j : I3) : (∑ a,rawProduct i j a a)=0 := by
  simp_rw [product_rule,←Finset.mul_sum,←Int.cast_sum,int_trace,Int.cast_zero, mul_zero]
lemma first_rule (i j : I3) : rawProduct i j 0 0 = if i=j then 2⁻¹ else 0 := by
  rw [product_rule, int_firstrow]
  by_cases h : i=j <;> simp [h]
def along : E4 := basis 0
@[simp] lemma along_apply (i : Axis) : along i = if i=0 then 1 else 0 := by simp [along,basis_eq]
@[simp] lemma along_norm : ‖along‖=1 := basis_norm _
@[simp] lemma along_zero : along≠0 := norm_pos_iff.mp (by simp)
lemma tensor_one (i j : I3) : atTensor i j along = rawProduct i j 0 0 := by
  simp [atTensor,apply_ite, Fintype.sum_ite_eq]
lemma diag_part (r : ℝ) (i j : I3) : (∑ a:Axis,∑ c:Axis, basis c a * r * rawProduct i j a c) = 0 := by
  have e a c : basis c a * r * rawProduct i j a c = if c=a then r*rawProduct i j a a else 0 := by
    by_cases h:a=c <;> simp [basis_eq,eq_comm,h]
  simpa only [e,Fintype.sum_ite_eq',←Finset.mul_sum,trace_rule,mul_zero]
lemma mixed_diagonal (i j : I3) : mixed i j along = if i=j then -4*normal else 0 := by
  rw [mixed_contact _ _ along_zero]; unfold tensorSum atHessian
  simp_rw [second_Green along_zero,along_norm]; norm_num only [one_pow,inv_one,mul_one]
  change -(∑ a:Axis, ∑ c:Axis,_ * rawProduct i j a c) = _
  calc _ = -((∑ a:Axis,∑ c:Axis, basis c a * (-2*normal) * rawProduct i j a c)+(8 * normal) * atTensor i j along) := by
            unfold atTensor; congr 1
            simp only [add_mul,Finset.sum_add_distrib,Finset.mul_sum]
            exact congrArg₂ _ (by congr 1; apply funext; intro a; apply Finset.sum_congr rfl; intro c _; rw [mul_comm (_*normal)]; simp [basis_eq,eq_comm])
              (by apply Finset.sum_congr rfl; intro a _; exact Finset.sum_congr rfl (fun c _ => by rw [mul_assoc]))
       _ = _ := by rw [tensor_one,first_rule,diag_part]; split_ifs <;> ring

/-- gradient toward field insertion, argument `w-x`. -/
def flow (a : Axis) (z : E4) := -grad a Green z
def mLine (j : I3) (μ : Axis) (z : E4) := ∑ a:Axis,fan false j a μ * flow a z
def integralInput (t m n : I3) (x y w : E4) := ∑ a:Axis,∑ b:Axis,fan false t a b * mLine m a (w-x) * mLine n b (w-y)

def third (m t n : I3) (u v : Axis) := ∑ a:Axis,∑ b:Axis, fan false m u a * fan false t a b * fan false n v b
lemma third_rule (m t n : I3) (u v : Axis) : third m t n u v = (Real.sqrt 2 ^3)⁻¹ * rawThird m t n u v := by
  unfold third rawThird; push_cast
  simp_rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _=>Finset.sum_congr rfl (fun _ _=>by rw [fan,fan,div_mul_div_comm,fan,div_mul_div_comm]; ring))
lemma input_expand (t m n : I3) (x y w : E4) : integralInput t m n x y w = ∑ u,∑ v, third m t n u v * (flow u (w-x) * flow v (w-y)) := by
  simp_rw [integralInput,mLine,third,Finset.mul_sum,Finset.sum_mul]
  let F (u v a b:Axis) := fan false m u a * fan false t a b * (fan false n v b * (flow u (w-x)*flow v (w-y)))
  have := Finset.sum_comm (f:= fun (s r : Axis × Axis)=>F r.1 r.2 s.1 s.2) (s:=Finset.univ) (t:=Finset.univ)
  simp_rw [show ∀ v w u p:ℝ, v*w*u*p=v*w*(u*p) from fun _ _ _ _=>mul_assoc ..] at *
  conv_lhs =>
    enter [2, a, 2, b]
    rw [Finset.sum_comm]
  apply Eq.trans ?_ (show (∑a,∑b,∑u,∑v,F u v a b)= (∑u,∑v,∑a,∑b,F u v a b) by simpa only [Fintype.sum_prod_type] using this)
  exact Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=> Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl (fun _ _=>by unfold F; ring)
lemma flow_odd (z : E4) (a : Axis) : flow a (-z) = -flow a z := by
  by_cases h: z=0
  · subst z
    have t:= fderiv_comp_smul (-1:ℝ) (f:=Green) (x:=(0:E4))
    have he : fderiv ℝ Green 0 = - fderiv ℝ Green 0 := by simpa only [neg_smul,one_smul,even_Green, neg_zero] using t
    have ht := DFunLike.congr_fun he (basis a)
    unfold flow grad D; rw [neg_zero]; exact congrArg Neg.neg ht
  · simp [flow,first_Green h, first_Green (neg_ne_zero.mpr h)]
lemma third_exchange (m t n : I3) (u v : Axis) :
    third m t n u v + third m t n v u = if u=v then (Real.sqrt 2)⁻¹ * eps3 m t n else 0 := by
  rw [third_rule,third_rule,← mul_add,← Int.cast_add, int_crush, show Real.sqrt 2^3 = 2 * Real.sqrt 2 by rw [pow_three,sqrt_two_rule]; ring]
  split_ifs <;> push_cast <;> ring
lemma flip_input (t m n : I3) (x y w : E4) :
    integralInput t m n x y w + integralInput t m n x y (x+y-w) = (Real.sqrt 2)⁻¹ * eps3 m t n * ∑ a:Axis, flow a (w-x) * flow a (w-y) := by
  let F := third m t n
  simp only [input_expand,F,show x+y-w-x=-(w-y) by abel, show x+y-w-y=-(w-x) by abel,flow_odd,neg_mul_neg]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  simp_rw [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  have he v : third m t n a v * (flow a (w-x)*flow v (w-y)) + third m t n v a * (flow v (w-y) * flow a (w-x)) = (third m t n a v + third m t n v a)*(flow a (w-x)*flow v (w-y)) := by ring
  simpa only [he,third_exchange,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]

end YM.Pert.Triangle
