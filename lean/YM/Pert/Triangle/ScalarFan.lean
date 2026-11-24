import YM.Pert.Triangle.Fans
/-! Same-helicity cancellation away from collisions on the actual unextended scalar Maxwell kernel. No distributional identity at the origin inferred by plugging in. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis
open scoped Topology Classical
local notation "Rows" => Axis × Axis
local notation "I3" => Fin 3
variable (H Y X : Axis → Axis → ℝ) (hX : ∀ a b, X b a = - X a b) (hY : ∀ a b, Y b a = -Y a b)
def entry (a b c d : Axis) := ((if c=b then H a d else 0) - (if d=b then H a c else 0)) - ((if c=a then H b d else 0) - (if d=a then H b c else 0))
def contractionHalf (a b) := ∑ e:Axis, Y b e*H a e

def fanRow (a b) := ∑ c:Axis,∑ e:Axis, Y c e * entry H a b c e
@[simp] lemma deltasH1 (a b) : (∑ c : Axis,∑ e : Axis,Y c e*(if b=c then H a e else 0))=contractionHalf H Y a b := by
  simp_rw [mul_ite,mul_zero]; rw [Finset.sum_comm]
  simp [contractionHalf]
include hY
lemma deltasH2 (a b) : (∑ c : Axis,∑ e : Axis,Y c e*(if b=e then H a c else 0))= -contractionHalf H Y a b := by simp_rw [mul_ite,mul_zero, Finset.sum_ite_eq,Finset.mem_univ,if_true]; rw [contractionHalf,←Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun c _=> by rw [hY b c,neg_mul])
lemma partial_row (a b) : fanRow H Y a b= 2 * (contractionHalf H Y a b-contractionHalf H Y b a) := by unfold fanRow; simp only [fanRow, entry,mul_sub,Finset.sum_sub_distrib]; simp_rw [show ∀ e:Axis,e=b↔b=e from fun e=>eq_comm, show ∀ c:Axis,c=a↔a=c from fun _=> eq_comm];rw [deltasH1,deltasH1, deltasH2 _ Y hY,deltasH2 _ Y hY]; ring

def rawPair (h₁ : Bool) (i : I3) (h₂ : Bool) (j : I3) := ∑ a,∑ b, fan h₁ i a b * fanRow H (fan h₂ j) a b
def rotatedProduct (h₁ : Bool) (i : I3) (h₂ : Bool) (j : I3) (a c) := ∑ b, fan h₁ i a b * fan h₂ j c b
lemma exchange_axis (h : Bool) (i : I3) (j : I3) : (∑ a,∑ b, fan h i a b * contractionHalf H (fan h j) b a) = -(∑ b,∑ a, fan h i b a * contractionHalf H (fan h j) b a) := by rw [Finset.sum_comm]; simp_rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun b _=> Finset.sum_congr rfl fun a _=> by nth_rw 1 [fan_flip h i b a]; rw [neg_mul])
omit hY in
lemma sumHalf (X Y H : Axis→Axis→ℝ) (hY : ∀ a b, Y b a = -Y a b) : (∑a,∑b, X a b * contractionHalf H Y a b) = -∑ a,∑ c,H a c * (∑ b, X a b * Y c b) := by
  simp_rw [contractionHalf,Finset.mul_sum,←Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun c _=> Finset.sum_congr rfl (fun b _=> by rw [hY c b];ring)) -- anti sym direction
omit hY in
lemma rotated_trace (h : Bool) i j : rawPair H h i h j = -4* ∑ a,∑ c,H a c * rotatedProduct h i h j a c := by
  let Y:=fan h j; let X:=fan h i
  have hY : ∀ a b, Y b a= -Y a b := fan_flip h j
  have he:=exchange_axis H (Y:=Y) hY h i j
  have hi:=sumHalf X Y H hY
  unfold Y X at *
  -- simplify one step at time
  unfold rawPair
  simp_rw [partial_row H _ hY]
  conv_lhs => simp only [show ∀ u v w : ℝ, u*(2*(v-w))=2*(u*v)-2*(u*w) from fun _ _ _=> by ring,Finset.sum_sub_distrib,← Finset.mul_sum]
  unfold rotatedProduct
  rw [he,hi]; ring
variable (hH : ∀ a b, H b a = H a b)
include hH
omit hY in
lemma pays_trace (h : Bool) (i j : I3) : 2* ∑ a,∑ c,H a c * rotatedProduct h i h j a c = if i=j then ∑ a,H a a else 0 := by
  let t := ∑ a,∑ c,H a c*rotatedProduct h i h j a c
  have he : t=∑ a,∑ c, H a c * rotatedProduct h j h i a c:= by unfold t rotatedProduct; rw [Finset.sum_comm]; exact Finset.sum_congr rfl (fun a _=>Finset.sum_congr rfl fun c _=> by rw [hH]; exact congrArg _ (Finset.sum_congr rfl (fun j _=>mul_comm ..))) -- order
  calc
    2*t=t+t := by ring
    _ = t + ∑ _,∑ _, _ := congrArg (t+·) he
    _ = ∑ a,∑ c,H a c*(rotatedProduct h i h j a c+rotatedProduct h j h i a c) := by simp only [mul_add,Finset.sum_add_distrib,t]
    _ = _ := by simp only [rotatedProduct,fan_anticommute];by_cases he : i=j <;> simp [he,eq_comm]
omit hY in
lemma annihilation (h i j) : rawPair H h i h j = -2*(if i=j then ∑ a,H a a else 0) := by rw [rotated_trace]; have he:=pays_trace H hH h i j; linarith

omit hH
omit hY
-- continuum scalar covariance
def atHessian (z : E4) := fun a c=> grad a (grad c Green) z
lemma green_antiself (h : Bool) (i j : I3) {z : E4} (hz : z≠0) : (∑ a,∑ b,fan h i a b * (∑ c,∑ d, fan h j c d * bareCurl a b c d z))=0 := by
  have HH : ∀ a b, atHessian z b a=atHessian z a b := fun a b=>Hess_sym hz b a
  have he := annihilation (atHessian z) HH h i j
  have e : (∑ a : Axis, atHessian z a a)=0 := harmonic hz
  rw [e,ite_self,mul_zero] at he
  simpa only [bareCurl,Pi.sub_apply, Bare.opp_grad hz,rawPair,fanRow,atHessian,entry] using he
end YM.Pert.Triangle
