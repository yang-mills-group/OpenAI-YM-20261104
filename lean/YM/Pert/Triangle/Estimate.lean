import YM.Pert.Triangle.Inflation
import YM.Pert.Triangle.Crosswind
/-! The reduced first-order triangle kernel of equation trians (using a local subtraction as in Subtracted.lean) is not zero identically on separated positions. This lemma is about the continuum Taylor side, not the matching limit. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
noncomputable section

namespace YM.Pert.Triangle
open Maxwell Analysis Set Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace
local notation "I3" => Fin 3

variable {G : Gauge}
variable (x y z:E4) (i j k m n:I3)

lemma flipAverage (t : I3) (h:x≠y) : (∫ w, integralInput t m n x y w) = (2:ℝ)⁻¹ * ((Real.sqrt 2)⁻¹ * eps3 m t n) * overlap x y := by
  let U := integralInput t m n x y
  have he : (∫ w,U (x+y-w)) = (∫ w,U w) := integral_sub_left_eq_self U volume (x+y)
  calc
    _ = (2:ℝ)⁻¹ * ((∫ w, U w) + (∫ w,U (x+y-w))) := by rw [he];ring
    _ = (2:ℝ)⁻¹ * (∫ w, (U w + U (x+y-w)) ∂volume) := by
          congr 1; rw [integral_add (inputPayable _ _ _ h) (by simpa only [sub_eq_add_neg] using (((inputPayable t m n h).comp_add_left (x+y)).comp_neg))]
    _ = _ := by simp only [U,flip_input,integral_const_mul,overlap]; simp only [mul_assoc]

lemma pDirect (i m) : Tendsto (fun R=> R^4 * mixed i m (outZ R-x)) atTop (𝓝 (if i=m then -4*normal else 0)) := by
    have h := (((mixed_rays i m).diff along_zero).continuousAt.tendsto.comp
          (f:=fun R:ℝ=> along-R⁻¹ • x) (by simpa using (tendsto_const_nhds (x:=along)).sub ((tendsto_inv_atTop_zero (𝕜:=ℝ)).smul_const x))).congr'
          (((eventuallyOuter x x x).and (eventually_ge_atTop (reachDistance x x))).mono (fun R h=>(transported x x i m x h.2 h.1).symm))
    simpa only [mixed_diagonal] using h
-- replace unknown method

def terminal := ∑ a,∑ b, fan true i a b * (mLine m a (z-x) * mLine n b (z-y))
def impact := terminal x y z i m n - 2 * ∑ t, against i t m n z x y
def classified := ∑ i:I3,∑ j:I3,∑ k:I3,∑ m:I3,∑ n:I3,(eps3 i j k:ℝ) * mixed j m (z-x) * mixed k n (z-y) * impact x y z i m n
def detector (G : Gauge) := (6 * ∑a : G.ColorIndex,∑b,∑c, (colorF (G:=G) a b c)^2) * classified x y z

lemma mLine_energy (j m) (v: E4) (r : ℝ) (hr : r≠0): r^3 * mLine j m (r•v) = mLine j m v := by
  by_cases hv : v=0
  · subst v; suffices mLine j m (0:E4)=0 by rw [smul_zero,this,mul_zero]
    have h (i:Axis) : flow i 0=0 := by have := flow_odd 0 i; rw [neg_zero] at this;linarith
    unfold mLine; simp_rw [h,mul_zero,Finset.sum_const_zero]
  unfold mLine; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _
  rw [←mul_assoc,mul_comm (_^_) _,mul_assoc,flow_energy _ hr hv]
lemma vanishLine (j m) : Tendsto (fun R=> R^2 * mLine j m (outZ R-x)) atTop (𝓝 0) := by
  have h := (mLine_regular j m along_zero).continuousAt.tendsto.comp (f:=fun R:ℝ=>along-R⁻¹ • x) (by simpa using (tendsto_const_nhds (x:=along)).sub ((tendsto_inv_atTop_zero (𝕜:=ℝ)).smul_const x))
  have he := tendsto_inv_atTop_zero.mul h
  rw [zero_mul] at he
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  dsimp
  rw [← mLine_energy j m _ R hR.ne',smul_sub,smul_inv_smul₀ hR.ne',outZ]
  field_simp
lemma vanishTerminal : Tendsto (fun R=>R^4 * terminal x y (outZ R) i m n) atTop (𝓝 0) := by
  simp_rw [terminal,Finset.mul_sum]
  have he (R u v w:ℝ) : R^4 * (u*(v*w)) = u * ((R^2*v)*(R^2*w)) := by ring
  simp_rw [he]
  rw [← Finset.sum_const_zero (s:=(Finset.univ : Finset Axis)), show (∑ _: Axis,(0:ℝ)) = ∑ _:Axis, ∑ _:Axis,(0:ℝ) by simp]
  exact tendsto_finsetSum _ fun a _=> tendsto_finsetSum _ fun b _=> by simpa using (tendsto_const_nhds (x:=fan true i a b)).mul ((vanishLine x _ _).mul (vanishLine y _ _))
lemma impactLimit (h : x ≠ y) : Tendsto (fun R=>R^4 * impact x y (outZ R) i m n) atTop (𝓝 ((4*normal)*((Real.sqrt 2)⁻¹ * eps3 m i n) * overlap x y)) := by
  have hlim := (vanishTerminal x y i m n).sub (tendsto_const_nhds (x:=2) |>.mul (tendsto_finsetSum Finset.univ (fun t _=>against_limit x y i t m n h)))
  convert! hlim using 1
  · ext R; unfold impact;rw [mul_sub]; congr 1; rw [←mul_assoc,mul_comm (_^_) 2,mul_assoc,Finset.mul_sum]
  apply congrArg (𝓝 ·)
  simp_rw [ite_mul,zero_mul]; simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [flipAverage _ _ _ _ _ h];ring

def κ := -4*normal
def fee (u v:I3) : ℝ := if u=v then κ else 0
def pricePattern (s:ℝ) := ∑ i:I3,∑ j:I3,∑ k:I3,∑ m:I3,∑ n:I3, ((eps3 i j k):ℝ) * fee j m * fee k n * (s*eps3 m i n)
-- laws in fee coordinates
lemma pattern (s:ℝ) : pricePattern s = (-6*s) * κ^2 := by
  unfold pricePattern fee
  simp only [mul_ite,ite_mul,zero_mul,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true,Finset.sum_const_zero]
  have he (i j k) : (eps3 i j k : ℝ) * κ * κ * (s * (eps3 j i k:ℝ)) = s*κ^2*(eps3 i j k * eps3 j i k : ℤ) := by push_cast; ring
  rw [show (-6*s)*κ^2 = s*κ^2*(-6) by ring]
  simpa only [he,←Finset.mul_sum,←Int.cast_sum,eps_nonzero_int,Int.cast_neg,Int.cast_ofNat]
def classTotal (x y:E4) := pricePattern (4*normal * ((Real.sqrt 2)⁻¹) * overlap x y)
lemma classifiedLimit (h : x≠y) : Tendsto (fun R=>R^12 * classified x y (outZ R)) atTop (𝓝 (classTotal x y)) := by
  simp_rw [classified, Finset.mul_sum,classTotal,pricePattern]
  have hb (R u v w s:ℝ) : R^12*(u*v*w*s) = u*(R^4*v)*(R^4*w)*(R^4*s) := by ring
  simp_rw [hb]
  refine tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=> tendsto_finsetSum _ (fun k _=> tendsto_finsetSum _ (fun m _=> tendsto_finsetSum _ (fun n _=> ?_)))))
  have he := ((((tendsto_const_nhds (x:=(eps3 i j k:ℝ))).mul (pDirect x j m)).mul (pDirect y k n)).mul (impactLimit x y i m n h))
  convert! he using 1
  unfold fee κ; congr 1;ring
lemma detector_nonzero_first_separated (hG : G.Simple) : ∃ x y z, x≠y ∧ z≠x ∧ z≠y ∧ detector x y z G≠0 := by
  obtain ⟨u,_,v,_,hu,he⟩ := overlap_exists_nonzero
  suffices h : classTotal u v ≠ 0 by
    have ht := ((classifiedLimit u v hu).eventually ((isOpen_ne_fun continuous_id continuous_const).mem_nhds h)).and ((eventually_gt_atTop ‖u‖).and ((eventually_gt_atTop ‖v‖).and (eventually_ge_atTop (reachDistance u v))))
    obtain ⟨R,H,Hx,Hy,I⟩ := ht.exists
    have e := norm_out u v I
    exact ⟨u,v,outZ R,hu,fun q=>by rw [q] at e; linarith,fun q=>by rw [q] at e; linarith, mul_ne_zero (mul_ne_zero (by norm_num) (structure_price hG).ne') (right_ne_zero_of_mul H)⟩
  unfold classTotal; rw [pattern]; unfold κ
  exact mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero (by have := normal_pos; exact (by positivity : 0<4*normal*(Real.sqrt 2)⁻¹).ne') he)) (pow_ne_zero _ (mul_ne_zero (by norm_num) normal_pos.ne'))
end YM.Pert.Triangle
