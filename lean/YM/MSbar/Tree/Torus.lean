import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Window

/-!
# Tree propagating lines with inversion quotient infrared regulator

Wilson lattice gauge theory, native space units. Use actual discrete
radian momenta `mon` and two-curl `symbol`. Full field species space is
as in YM. These leading rules only need scalar propagators, replicated
independently across `G.ColorIndex`. In the quotient we use the image
formula (factor `1/2` in the quadratic action, and inversion projection),
not dropping the second term. We implement it as the definition of the
finite-regulator diagram rule on curls. The torus potential rule before
both curls is here Feynman-gauge scalar; longitudinal components omitted /
added in Landau convention have no effect on this line. This does not
implement finite torus FP rules beyond the tree lines. Mesh and support
rates are separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree.Torus
open Function Set Filter Lattice Laurent Bloch Matrix Exterior
open Further.FreeCovariance.KP
open scoped Topology BigOperators ComplexConjugate Classical

variable {n : Side} {G : Gauge}

/-- Ordinary scalar Wilson Laplacian symbol. -/
def lap (p : Momentum) := ∑ i, ‖q p i‖ ^ 2

lemma divisor_lap (p : Site n) : Next.Free.divisor 1 (mon p) = lap (mon p) := by
  rw [Next.Free.divisor_normSq 1 (show _ from real_frequency p)]
  unfold lap; simp [Next.Free.seedQ, Next.Free.narrow_apply,q,Next.Free.chip]

lemma positive (p : Site n) (hp : p≠0) : 0 < lap (mon p) := by
  have he : mon p≠0 := by
    obtain ⟨i,hi⟩ := step_picks p hp
    intro h; apply hi; rw [cell_step,h]; simp
  have hv := Next.Free.divisor_ne 1 (Next.Free.base_subset_realCube Next.Free.zone_pos (Next.Free.mon_mem n p)) he
  rw [divisor_lap] at hv
  have hz:0 ≤ lap (mon p):= Finset.sum_nonneg fun i _=>sq_nonneg _
  exact lt_of_le_of_ne hz (Ne.symm (fun h=>hv (by rw [h]; simp)))

/-- Two curls of the propagator. At zero this evaluates to zero. -/
def twoCurl (p : Site n) : Matrix X2 X2 ℂ := ((lap (mon p):ℂ)⁻¹) •
  (symbol 1 (mon p) * (symbol 1 (mon p))ᴴ)

lemma arc_eq (p : Site n) : Episode.arc 1 (Next.Free.Train.top 4) (mon p)= twoCurl p := by
  let v := Next.Free.Train.top 4
  let z:= mon p
  have he i : Next.Free.scaleD 1 1 v z i=(Next.Free.divisor 1 z)⁻¹ := by
    unfold Next.Free.scaleD Next.Free.Train.levelD; rw [Next.Free.feed_top]; simp [v,Next.Free.Train.levelNoise, Next.Free.Train.stream, Next.Free.Train.nozzle]
  have hv : Next.Free.fieldD 1 1 v z=(↑(lap z):ℂ)⁻¹ • 1:= by
    unfold Next.Free.fieldD; rw [funext he,divisor_lap]; simpa only [mul_one,pow_one,Next.Free.mask_one] using Next.Free.mask_scale 1 (fun _=>1) ((↑(lap z):ℂ)⁻¹)
  unfold Episode.arc twoCurl; rw [show Next.Free.fieldD 1 1 _ _=_ from hv, Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]

/-- Lap check against actual free Wilson precision symbol after longitudinal gauge term. -/
theorem hessian_gf (p : Site n) :
    (symbol 1 (mon p))ᴴ * symbol 1 (mon p) + symbol 0 (mon p) * (symbol 0 (mon p))ᴴ =
      (↑(lap (mon p)):ℂ) • (1:Matrix X1 X1 ℂ) := by
  have he:= blade_id (Exterior.q (mon p)); rw [outside,Matrix.mul_one,Work.F06.sqLength_apply] at he; exact he

/-- Preprojection covariance for curvatures at specific positive faces. -/
def kernel (m : Side) (u v : Cover) (a b : PlaqAxes) : ℝ :=
  (meter m * ∑ p:Site m, mode (mon p) (u-v) * twoCurl p (plaquette a) (plaquette b)).re

def bumpFace (a : PlaqAxes) : Cover := step a.val.1 + step a.val.2

def reflectPos (v : Cover) (a : PlaqAxes) := -v - bumpFace a

/-- Single-color covariance on the inversion quotient. The orientation
sign for the second term with **two-form** is positive. The reflection of
both directions shifts the root by `-bumpFace`. We'll use this rule with
large **even** M. -/
def kernelOrbit (m : Side) (u v : Cover) (a b : PlaqAxes) :=
  kernel m u v a b + kernel m u (reflectPos v b) a b

lemma kernel_found (m : Side) (u v : Cover) (a b : PlaqAxes) : kernel m u v a b=
    (Episode.found 1 (Next.Free.Train.top 4) m (plaquette a) (plaquette b) (u-v)).re := by
  unfold kernel Episode.found; simp_rw [arc_eq]

lemma respects (u v u' v' : Cover) (a b : PlaqAxes) (hu : wrap n u=wrap n u') (hv : wrap n v=wrap n v') :
    kernel n u v a b = kernel n u' v' a b := by rw [kernel_found,kernel_found,Episode.wraps _ _ _ (show wrap n (u-v) = wrap n (u'-v') from (by simp [hu,hv]))]

private theorem swap_lag (p : Site n) (z : Cover) : star (mode (mon p) z)=mode (mon p) (-z):= by
  rw [← mode_adjoint (mon p) z,real_frequency]

lemma kernel_symm (m : Side) (u v : Cover) (a b : PlaqAxes) : kernel m u v a b=kernel m v u b a:= by
  have h (p:Site m) : star (twoCurl p (plaquette a) (plaquette b))=twoCurl p (plaquette b) (plaquette a):= by
    have he : (twoCurl p)ᴴ= twoCurl p:= by unfold twoCurl; simp
    exact congr_fun (congr_fun he (plaquette b)) (plaquette a)
  nth_rw 1 [kernel,← Complex.conj_re]
  unfold kernel; rw [map_mul,map_sum]; simp_rw [map_mul, show ∀ p:Site m, conj (twoCurl p (plaquette a) (plaquette b))=_ from h, show ∀ p:Site m, conj (mode (mon p) (u-v)) = mode _ _ from fun p =>swap_lag p _,neg_sub]; simp [meter]
-- Private helper from YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Window.
private lemma wedge_front (a : PA) (q : Axis → ℂ) (v : X1→ℂ) :
    (wedge 1 q *ᵥ v) (plaquette a) = q a.val.1 * v (coord a.val.2)-q a.val.2 * v (coord a.val.1) := by
  let b := a.val.1; let d := a.val.2; have hb : b<d := a.property
  let F := plaquette a
  have hh : F.val={b,d} := rfl
  unfold wedge; rw [Matrix.sum_mulVec]; simp_rw [Matrix.smul_mulVec]; rw [Finset.sum_apply]
  change ∑ i, q i * ((left ℂ 1 i)*ᵥv) F=_
  rw [← Finset.sum_subset (Finset.subset_univ ({b,d}:Finset Axis)),Finset.sum_insert (by simp [hb.ne]), Finset.sum_singleton]
  · have hs : b∈F.val := hh ▸ Finset.mem_insert_self ..
    have ht : d∈F.val := by simp [hh]
    have hb' : remove b F hs=coord d := by ext i; by_cases he:i=b <;> simp [coord,remove,hh,he,hb.ne]
    have hd' : remove d F ht=coord b := by ext i; by_cases he:i=d <;> simp [coord,remove,hh,he,hb.ne']
    simp_rw [eliminate]; rw [dif_pos hs,dif_pos ht,hb',hd']
    rw [parity,parity,pre,pre]; simp [hh,Finset.filter_insert,Finset.filter_singleton,hb,hb.not_gt]; rfl
  intro i _ h; rw [eliminate,dif_neg (show i∉F.val from hh ▸ h),mul_zero]

private theorem goes (p : Site n) (a : PA) (i : Axis) :
    (star (symbol 1 (mon p) (plaquette a) (coord i))) * mode (mon p) (bumpFace a-step i)
       = -symbol 1 (mon p) (plaquette a) (coord i) := by
  have he (u : Axis): star (q (mon p) u) * mode (mon p) (step u)= - q (mon p) u:= by
    unfold Exterior.q; rw [← factor,star_sub,star_one,swap_lag,mode_opposite, sub_mul,inv_mul_cancel₀ (mode_ne (mon p) (step u)),one_mul, neg_sub]
  have hx : symbol 1 (mon p) (plaquette a) (coord i)= q (mon p) a.val.1*(if a.val.2=i then 1 else 0)-q (mon p) a.val.2*(if a.val.1=i then 1 else 0):= by
    have hz:= wedge_front a (q (mon p)) (Pi.single (coord i) 1)
    simpa only [symbol,mulVec_single_one,Pi.single_apply,coord_iff,Matrix.col,transpose_apply] using hz
  have hA:=a.property; rw [hx]; unfold bumpFace
  by_cases h:i=a.val.2
  · subst i; rw [if_pos rfl,if_neg hA.ne,add_sub_cancel_right]; simpa using he _
  by_cases h':i=a.val.1
  · subst i; rw [if_pos rfl,if_neg hA.ne',mul_one,mul_zero,zero_sub,star_neg, add_sub_cancel_left,neg_mul,he]
  simp [Ne.symm h,Ne.symm h']

lemma kernel_reflect (m : Side) (u v : Cover) (a b : PlaqAxes) :
    kernel m (reflectPos u a) (reflectPos v b) a b=kernel m u v a b:= by
  have ht (p:Site m) : mode (mon p) (reflectPos u a-reflectPos v b)* twoCurl p (plaquette a) (plaquette b)=
      star (mode (mon p) (u-v) * twoCurl p (plaquette a) (plaquette b)):= by
    unfold twoCurl; simp only [Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply]; rw [star_mul',star_mul'];
    simp only [Finset.mul_sum,star_inv₀, Complex.star_def,Complex.conj_ofReal, map_sum]
    apply Finset.sum_congr rfl; intro i _
    obtain ⟨i,rfl⟩:= axisEquiv.surjective i
    simp only [coord_map]; let z:= mon p; let M:=mode z; let F (a:PA):=symbol 1 z (plaquette a) (coord i)
    let L (a:PA):= bumpFace a-step i ; let B:=(↑(lap z):ℂ)⁻¹; let U:=reflectPos u a-reflectPos v b
    change M U*(B*(F a*star (F b)))=star (M (u-v))*(B*star (F a*star (F b)))
    have hA:= goes p a i; have hB:= goes p b i
    change star (F a)*M (L a)= -F a at hA; change star (F b)*M (L b) = - F b at hB
    rw [show U=-(u-v)+L b-L a from by unfold U reflectPos L; abel]
    change mode _ _ * (_*(_*_))=star (mode (mon p) _) * (_*star (F a * star (F b)))
    rw [swap_lag,sub_eq_add_neg _ (L a),mode_shift,mode_shift,mode_opposite _ (L a),star_mul,star_star]
    change ((M (-(u-v))*M (L b))* (M (L a))⁻¹)*(B*(F a*star (F b))) = M (-(u-v))*(B*(F b*star (F a)))
    apply mul_left_cancel₀ (mode_ne z (L a))
    change M (L a)*_=M (L a)*_
    field_simp [show M (L a)≠0 from mode_ne z (L a)]
    linear_combination F a * M (-(u-v))*B * hB - F b * M (-(u-v))*B * hA
  unfold kernel; simp_rw [ht]
  let f(p:Site m):= mode (mon p) (u-v)*twoCurl p (plaquette a) (plaquette b)
  change (meter m * ∑ p : Site m, conj (f p)).re=(meter m * ∑ p, f p).re
  rw [← map_sum,← show conj (meter m)= meter m from by unfold meter; simp] -- rewrites both
  nth_rw 2 [show conj (meter m)= meter m from by unfold meter; simp]
  rw [← map_mul]; exact Complex.conj_re _

theorem kernelOrbit_symm (m : Side) (u v : Cover) (a b : PlaqAxes) :
    kernelOrbit m u v a b = kernelOrbit m v u b a := by
  have hh : reflectPos (reflectPos v b) b=v := by unfold reflectPos; abel
  unfold kernelOrbit; rw [kernel_symm m u v, ← kernel_symm m (reflectPos u a) v a b,
    ← kernel_reflect m u (reflectPos v b),hh]
end YM.MSbar.Tree.Torus
