import YM.XSpace.CurledActions

/-!
# Infinite-volume self covariance for the top Wick-jet matrix

Apply physical-coordinate symmetries BEFORE imposing the on-shell quotient. In particular,
prove covariance survives the linear maps on Snap: this lets us use ordinary tensor algebra
in exactly those coordinates without an assumption of same-point reflection positivity etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Top
open Function Filter Set Lattice Wilson Labels Source Source.Drops Bid InnerProductSpace
open scoped Topology BigOperators InnerProductSpace
variable {G : Gauge} {H : Hol G} {d : ℕ} (A : Survey G H d)
abbrev Bean := (_ : Fin A.size) × G.ColorIndex

def beanBasis : Module.Basis (Bean A) ℝ (GaugePanel G A.size) := Pi.basis fun _ : Fin A.size => (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis
lemma repr_panel (p : GaugePanel G A.size) (i : Bean A) : (beanBasis A).repr p i=p i.1 i.2:=by
  rw [beanBasis, Pi.basis_repr]; simp
lemma bean_reconstruct (p : GaugePanel G A.size) : (∑ i : Bean A, p i.1 i.2 • beanBasis A i)=p := by simp_rw [← repr_panel A p]; exact (beanBasis A).sum_repr _

def bills (L : Module.Dual ℝ (Snap G d)) (i : Bean A) : ℝ := L (A.extract (beanBasis A i))
def covariancePosition (i j : Bean A) := (A.looks i.1).offset-(A.looks j.1).offset

def bean_kernel (V : PlaqAxes → PlaqAxes → Cover → ℂ) (i j : Bean A) : ℝ := if i.2=j.2 then
  (V (A.looks i.1).plaq (A.looks j.1).plaq (covariancePosition A i j)).re else 0

def bean_cov (V : PlaqAxes → PlaqAxes → Cover → ℂ) (L M : Module.Dual ℝ (Snap G d)) : ℝ := ∑ i:Bean A, ∑ j:Bean A, bills A L i*bills A M j*bean_kernel A V i j

section finite
variable (n : Side)
def beanPoint (i : Bean A) : Faces n:=Work.F03.slotFace (A.looks i.1) (0:Site n)
def testBean (i : Bean A) : Forms G n := unitFace (beanPoint A n i) i.2

def announce (L : Module.Dual ℝ (Snap G d)) : Forms G n:= ∑ i:Bean A, bills A L i • testBean A n i
def reply (L : Module.Dual ℝ (Snap G d)) : Curled G n:=(Curled G n).orthogonalProjectionOnto (announce A n L)

lemma full_kernel (i j : Bean A) : inner ℝ (testBean A n i) ((Curled G n).starProjection (testBean A n j))= bean_kernel A (fourier n) i j:= by
  have ht (i j : Bean A) : wrap n (covariancePosition A i j)= (beanPoint A n i).1-(beanPoint A n j).1:= by simp [beanPoint,covariancePosition,Work.F03.slotFace]
  have h:= spectral (beanPoint A n i) (beanPoint A n j) i.2 j.2 (ht i j)
  unfold bean_kernel; split; swap
  · rename_i H; rw [if_neg H] at h; exact Complex.ofReal_eq_zero.mp h
  rename_i H; rw [if_pos H] at h; exact congr_arg Complex.re h

lemma inner_reply (L : Module.Dual ℝ (Snap G d)) (x : Curled G n) : inner ℝ (reply A n L) x = L (detector n A x):=by
  change inner ℝ ((Curled G n).starProjection (announce A n L)) x.val = _
  rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr x.property, announce,sum_inner, detects]
  conv_rhs => rw [← (beanBasis A).sum_repr (readPanel n A x.val),map_sum,map_sum]
  apply Finset.sum_congr rfl; intro i _; rw [real_inner_smul_left, map_smul,map_smul,smul_eq_mul,repr_panel, mul_comm,bills,testBean,Top.atFace]; rfl

lemma finite_cov (L M : Module.Dual ℝ (Snap G d)) :
    inner ℝ (reply A n L) (reply A n M)=bean_cov A (fourier n) L M:= by
  let f:= announce A n L; let g:=announce A n M
  change inner ℝ ((Curled G n).starProjection f) ((Curled G n).starProjection g) = _
  rw [Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem ..)]
  simp only [f,g, announce, sum_inner, map_sum,inner_sum,real_inner_smul_left, map_smul,real_inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [full_kernel]; ring

-- Transformation preserves covariance by ordinary comparison on this same period; no
-- assumption that the induced action is orthogonal on either Snap or all stencil labels.
lemma finite_invariant (T : Module.End ℝ (Snap G d))
    (h : ∃ R : Curled G n ≃ₗᵢ[ℝ] Curled G n, ∀ x : Curled G n, detector n A (R x) = T (detector n A x)) (L M : Module.Dual ℝ (Snap G d)) :
    bean_cov A (fourier n) (L.comp T) (M.comp T)=bean_cov A (fourier n) L M:=by
  obtain ⟨R,h⟩:=h
  have hi (R : Curled G n ≃ₗᵢ[ℝ] Curled G n) (x y : Curled G n) : inner ℝ (R x) (R y)=inner ℝ x y:=by
    rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,← map_add,R.norm_map,R.norm_map,R.norm_map]
  have he (L : Module.Dual ℝ (Snap G d)) : reply A n (L.comp T)=R.symm (reply A n L):=by
    apply ext_inner_right ℝ; intro x; rw [inner_reply, LinearMap.comp_apply, ← h, ← hi R (R.symm _) _,LinearIsometryEquiv.apply_symm_apply,inner_reply]
  rw [← finite_cov,← finite_cov,he,he]; exact hi R.symm _ _
end finite

lemma bean_limit (i j : Bean A) {f : ℕ→Side} (h : Tendsto (fun i=>(f i).val) atTop atTop) :
    Tendsto (fun k=> bean_kernel A (fourier (f k)) i j) atTop (𝓝 (bean_kernel A coverLine i j)):=by
  unfold bean_kernel; split
  · exact Complex.continuous_re.continuousAt.tendsto.comp (fourier_limit h _ _ _)
  exact tendsto_const_nhds
lemma covariance_limit (L M : Module.Dual ℝ (Snap G d)) {f : ℕ→Side} (h : Tendsto (fun i=>(f i).val) atTop atTop) :
    Tendsto (fun k=> bean_cov A (fourier (f k)) L M) atTop (𝓝 (bean_cov A coverLine L M)):=
  tendsto_finsetSum _ fun i _=>tendsto_finsetSum _ fun j _=> (bean_limit A i j h).const_mul _

def realCov : LinearMap.BilinForm ℝ (Module.Dual ℝ (Snap G d)) :=
  LinearMap.mk₂ ℝ (bean_cov A coverLine)
   (fun x y z=> by simp [bean_cov,bills,add_mul,Finset.sum_add_distrib]) (fun a x y=> by simp [bean_cov,bills,mul_assoc,Finset.mul_sum])
   (fun x y z=> by simp [bean_cov,bills,mul_add,add_mul,Finset.sum_add_distrib]) (fun a x y=> by simp only [bean_cov,bills,LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring)

lemma realCov_symm (L M : Module.Dual ℝ (Snap G d)) : realCov A L M=realCov A M L:=
  tendsto_nhds_unique (covariance_limit A L M (f:=side) grows) ((covariance_limit A M L (f:=side) grows).congr fun n=> by rw [← finite_cov,← finite_cov]; exact real_inner_comm ..)
lemma realCov_semi (L : Module.Dual ℝ (Snap G d)) : 0≤realCov A L L:=
  ge_of_tendsto (covariance_limit A L L (f:=side) grows) (Eventually.of_forall fun n=> by rw [← finite_cov]; exact real_inner_self_nonneg)
lemma realCov_invariant (T : Module.End ℝ (Snap G d))
    (h : ∀ n, ∃ R : Curled G n ≃ₗᵢ[ℝ] Curled G n, ∀ x : Curled G n, detector n A (R x) = T (detector n A x)) (L M : Module.Dual ℝ (Snap G d)) :
    realCov A (L.comp T) (M.comp T) = realCov A L M:= tendsto_nhds_unique ((covariance_limit A _ _ (f:=side) grows).congr (fun n=>finite_invariant A (side n) T (h _) L M)) (covariance_limit A L M (f:=side) grows)
lemma realCov_turn (s : Signed) (L M : Module.Dual ℝ (Snap G d)) :
    realCov A (L.comp (snapTurn s.ortho⁻¹).toLinearMap) (M.comp (snapTurn s.ortho⁻¹).toLinearMap)=realCov A L M:=
  realCov_invariant A _ (fun n=> bridges_signed n A s) L M
lemma realCov_color (a : G.El) (L M : Module.Dual ℝ (Snap G d)) :
    realCov A (L.comp (snapColor a).toLinearMap) (M.comp (snapColor a).toLinearMap)=realCov A L M:=
  realCov_invariant A _ (fun n=>bridges_color n A a) L M

end YM.XSpace.Top
