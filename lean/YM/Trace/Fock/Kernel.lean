import YM.Trace.Schwartz
import YM.Trace.Weight
import YM.Mink.Geometry
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Analytic.Composition
import Mathlib.MeasureTheory.Constructions.HaarToSphere
/-!
Coordinates for the comparison to free Fock (not a proposal for the
physical spectral measure). Leg origin harmless for the shell measure `ν`; frequency
is paired by plus sign and `timeAxis` last as in the continuation. Ambient tensor slots
are finite Cartesian components; the projected waves are transverse. No Wick-polynomial
assumption on candidate vectors. Vacuum tests of Weyl translations use only the indicated
Gaussian vacuum vectors with the `q` normalization. The larger unsymmetrized space
below will allow explicit symmetry/transversality conditions imposed just on tested waves.
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace YM.Trace.Shell
open Boundary YM Function MeasureTheory Filter Complex Set
open scoped Topology ENNReal InnerProductSpace BigOperators Pointwise
variable (m : ℕ) {n : ℕ}
abbrev Mom := Space3
abbrev Cords (n : ℕ) := Fin n→Mom
abbrev Mode := Fin m × SpaceAxis -- fix name
abbrev Fiber (n : ℕ) := EuclideanSpace ℂ (Fin n→Mode m)
def scalarWeight (p : Mom) : ℝ := (2*‖p‖)⁻¹
lemma scalar_pos (p : Mom) : 0 ≤ scalarWeight p := by dsimp [scalarWeight]; positivity
noncomputable def ν : Measure Mom := volume.withDensity (ENNReal.ofReal ∘ scalarWeight)
@[fun_prop] lemma scalar_meas : Measurable scalarWeight := by unfold scalarWeight; fun_prop
lemma shell_real (p : Mom) : (ENNReal.ofReal (scalarWeight p)).toReal = scalarWeight p := ENNReal.toReal_ofReal (scalar_pos _)
noncomputable instance : SigmaFinite ν := inferInstanceAs (SigmaFinite (volume.withDensity fun x: Mom => ENNReal.ofReal (scalarWeight x)))
abbrev νpow (n : ℕ) : Measure (Cords n) := Measure.pi (fun _=> ν)
noncomputable instance (n : ℕ) : SigmaFinite (νpow n) := inferInstanceAs (SigmaFinite (Measure.pi (fun _:Fin n=> ν)))
abbrev Wave (n : ℕ) : Type := MeasureTheory.Lp (Fiber m n) 2 (νpow n)
abbrev Sum : Type := lp (Wave m) 2
abbrev SlotField := Mode m→Boundary.Test4
noncomputable def ray (p : Mom) : E4 := position p ‖p‖ -- need import Mink for continuous etc
noncomputable def total (x : Cords n) : E4 := ∑ i, ray (x i)
@[simp] lemma ray_time (x) : time (ray x)=‖x‖ := by simp [ray]
@[simp] lemma ray_space (x) : spatial (ray x) = x := by simp [ray]

-- tests
noncomputable def projKernel (x : Mom) (i j : SpaceAxis) : ℝ := (if i=j then 1 else 0) - (x j * x i)/‖x‖^2
variable {m}
noncomputable def jet (p : Mom) (f : SlotField m) : EuclideanSpace ℂ (Mode m) := WithLp.toLp 2 fun j => ‖p‖ •
     ∑ (k : SpaceAxis), projKernel p j.2 k • (plus (f (j.1,k)) (ray p))
noncomputable def rawTensor (r : Fin n→EuclideanSpace ℂ (Mode m)) : Fiber m n := WithLp.toLp 2 fun I => ∏ (i : Fin n), r i (I i)
noncomputable def productTest (h : SlotField m) (p : Cords n) : Fiber m n := rawTensor fun i => jet (p i) h

lemma tensor_sq (r : Fin n→EuclideanSpace ℂ (Mode m)) : ‖rawTensor r‖^2 = ∏ k, ‖r k‖^2 := by
     rw [EuclideanSpace.norm_sq_eq]
     change ∑ I : Fin n→Mode m, ‖∏ (i : Fin n), r i (I i)‖^2 = _
     simp_rw [norm_prod, ← Finset.prod_pow,EuclideanSpace.norm_sq_eq]
     exact (Fintype.prod_sum (f:=fun i j=> ‖r i j‖^2)).symm
lemma tensor_norm (r : Fin n→EuclideanSpace ℂ (Mode m)) : ‖rawTensor r‖=∏ i,‖r i‖ :=
     sq_eq_sq₀ (norm_nonneg _) (by positivity) |>.1 (by rw [tensor_sq, ← Finset.prod_pow])

lemma integrate (f : Mom→ℝ) : (∫ x, f x∂ν)=∫ p, scalarWeight p*f p := by
   apply Eq.trans (integral_withDensity_eq_integral_toReal_smul (ENNReal.measurable_ofReal.comp scalar_meas) (by simp) f)
   exact integral_congr_ae (.of_forall fun x=>by change _ • _ = _; rw [show ((ENNReal.ofReal ∘ scalarWeight) x).toReal = _ from shell_real x,smul_eq_mul])
lemma shell_integrable_iff (f : Mom→ℝ) : Integrable f ν ↔ Integrable (fun x => scalarWeight x * f x) := by
   unfold ν comp; rw [integrable_withDensity_iff (μ:=volume) (f:=fun x:Mom => ENNReal.ofReal (scalarWeight x))
     (ENNReal.measurable_ofReal.comp scalar_meas) (by simp) (g:=f)]; simp_rw [shell_real,mul_comm (f _)]

private lemma radial_weight_int (f : Mom→ℝ) (g : ℝ→ℝ) (hm : IntegrableOn (fun x=>x*g x) (Ioi 0))
    (hf : ∀ x, ‖f x‖ ≤ g ‖x‖) (hc : Measurable f) (_hg : Measurable g) : Integrable f ν := by
   have hq : Integrable (fun p : Mom => scalarWeight p*g ‖p‖) := by
         unfold scalarWeight; apply (MeasureTheory.integrable_fun_norm_addHaar volume (f:=fun x:ℝ => (2*x)⁻¹*g x)).2
         exact MeasureTheory.IntegrableOn.congr_fun (hm.const_mul (1/2:ℝ)) (fun x (hx : x>0) => by norm_num [smul_eq_mul]; field) measurableSet_Ioi
   apply Integrable.mono' ((shell_integrable_iff (fun p => g ‖p‖)).2 hq) hc.aestronglyMeasurable (.of_forall hf)

lemma integrable_shell_arbitrary_bound (f : Mom→ℝ) (hm : Measurable f) (c k : ℝ) (hk : 2<k) (hf : ∀ x, ‖f x‖ ≤ c * ((1+‖x‖)^(-k:ℝ))) : Integrable f ν := by
   refine radial_weight_int f (fun x=> c * ((1+x)^(-k:ℝ))) ?_ hf hm (by fun_prop)
   let F (x : ℝ) := x * (c*(1+x)^(-k:ℝ))
   change IntegrableOn F (Ioi 0)
   have ht : ContinuousOn F (Ici 0) := by
     apply ContinuousOn.mul continuousOn_id (continuousOn_const.mul _)
     refine ContinuousOn.rpow_const (f:=fun x : ℝ => 1+x) (continuousOn_const.add continuousOn_id) (fun x hx=> Or.inl ?_)
     simpa only using (show 1+x ≠0 from by linarith [show 0≤x from hx])
   have hC : 0≤c:= by
     have := hf (0:Mom); simpa using (norm_nonneg _).trans this
   have hL : IntegrableOn F (Ioc 0 1) := (ht.mono Set.Icc_subset_Ici_self).integrableOn_Icc.mono_set Ioc_subset_Icc_self
   have hR : IntegrableOn F (Ioi 1) := by
       have he := (integrableOn_Ioi_rpow_of_lt (by linarith : 1-k < -1) (by norm_num : 0<(1:ℝ))).const_mul c -- check
       refine Integrable.mono' he ((ht.mono (Ioi_subset_Ici (by norm_num))).aestronglyMeasurable measurableSet_Ioi) (by
           filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
           have hx : 0 < x := by linarith [show 1<x from hx]
           change ‖F x‖ ≤ c * x ^ (1-k)
           unfold F; rw [Real.norm_of_nonneg (by positivity),show (1:ℝ)-k=1+-k by ring,Real.rpow_add (by positivity),Real.rpow_one]
           rw [mul_left_comm] -- inequality use one via Real.rpow_le_rpow_of_exponent_nonpos
           apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hx.le) hC
           apply Real.rpow_le_rpow_of_nonpos (by positivity : x>0) (by linarith) (by linarith) )
   rw [show Ioi (0:ℝ)=Ioc 0 1∪Ioi 1 from Eq.symm (Ioc_union_Ioi_eq_Ioi (by norm_num))]
   exact hL.union hR
@[fun_prop] lemma projKernel_measurable (i j : SpaceAxis) : Measurable (fun x : Mom => projKernel x i j) := Measurable.sub measurable_const
       ((Measurable.mul ((PiLp.continuous_apply 2 (fun _ : SpaceAxis=>ℝ) j).measurable) ((PiLp.continuous_apply 2 _ _).measurable)).div (measurable_norm.pow_const _))
lemma norm_combine (x : Mom) (t : ℝ) : ‖x‖ ≤ ‖position x t‖ := by
     refine le_of_pow_le_pow_left₀ (n:=2) two_ne_zero (norm_nonneg _) (by simp only [Mink.squares (position _ _),time_position,spatial_position]; nlinarith)
lemma norm_ray (x : Mom) : ‖x‖ ≤ ‖ray x‖ := norm_combine ..
@[fun_prop] lemma continuous_ray : Continuous ray := by change Continuous (fun x:Mom => Mink.divide.symm (x,‖x‖)); fun_prop
@[fun_prop] lemma continuous_total (n : ℕ) : Continuous (@total n) := by unfold total; fun_prop

lemma projKernel_le (x : Mom) (i j : SpaceAxis) : |projKernel x i j| ≤ 2 := by
   unfold projKernel
   refine (abs_sub ..).trans (le_trans (b:=1 + 1) (add_le_add ?_ ?_) (by norm_num))
   · split_ifs <;> norm_num
   rw [abs_div,abs_mul]
   by_cases h : x=0; · simp [h]
   have hv : ‖x‖>0 := norm_pos_iff.mpr h
   rw [abs_of_pos (pow_pos hv _)]; apply (div_le_one (pow_pos hv _)).mpr; rw [pow_two]
   exact mul_le_mul (PiLp.norm_apply_le x _) (PiLp.norm_apply_le x _) (abs_nonneg _) hv.le
@[fun_prop] lemma measurable_jet (f : SlotField m) : Measurable (fun x : Mom => jet x f) := (PiLp.continuous_toLp 2 (fun _:Mode m => ℂ) |>.measurable).comp
      (measurable_pi_iff.mpr (fun i =>  by fun_prop)) -- ?

noncomputable def jetBound (f : SlotField m) := 48 * ((Fintype.card (Mode m):ℝ)+1) * (∑ i, orderCost (plus (f i)) 3)
lemma jetFormal (f : Test4) (x : Mom) : ‖plus f (ray x)‖ ≤ 8 * orderCost (plus f) 3 * ((1+‖x‖)^3)⁻¹ := by
    have := orderCost_nonneg (plus f) 3
    apply (weighted_test (plus f) 3 _).trans
    have hi : (weight 3 (ray x))⁻¹ ≤ ((1+‖x‖)^3)⁻¹ := inv_le_inv₀ (weight_pos ..) (by positivity)|>.2
       (by unfold weight; have := norm_ray x; gcongr)
    norm_num only [Nat.reducePow]; push_cast; rw [mul_comm (orderCost ..) (8:ℝ)]; gcongr
lemma jet_le (f : SlotField m) (p : Mom) : ‖jet p f‖ ≤ jetBound f * ((1+‖p‖)^2)⁻¹ := by
    have hG (i) := jetFormal (f i) p
    let M := ∑ i, orderCost (plus (f i)) 3
    have hm : 0≤M := Finset.sum_nonneg fun _ _ => orderCost_nonneg ..
    have heM (i : Mode m) : orderCost (plus (f i)) 3 ≤ M := Finset.single_le_sum (f:=fun i => orderCost (plus (f i)) 3)
        (s:=Finset.univ) (fun _ _=>orderCost_nonneg ..) (Finset.mem_univ _)
    let D := 1+‖p‖
    let K := 8*M * (‖p‖ * (D^3)⁻¹)
    have he (i : Mode m) : ‖p‖ * ‖plus (f i) (ray p)‖ ≤ K := by
        rw [show K=‖p‖*(8*M*(D^3)⁻¹) by dsimp only [K]; ring]; gcongr; exact (hG i).trans (by unfold D; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (heM i) (by positivity)) (by positivity))
    have hR (i : Mode m) : ‖(jet p f) i‖ ≤ 3 * (2*K) := by
        rw [jet]; simp only [norm_smul, norm_norm]
        calc _ ≤ ‖p‖ * ∑ k : SpaceAxis,‖projKernel p i.2 k • _‖ := mul_le_mul_of_nonneg_left (norm_sum_le ..) (norm_nonneg _)
             _ ≤ ∑ (k : SpaceAxis),2*K := by
               rw [Finset.mul_sum]; refine Finset.sum_le_sum (fun x _=>?_)
               rw [norm_smul,Real.norm_eq_abs, mul_left_comm]; exact (mul_le_mul_of_nonneg_right (projKernel_le ..) (by positivity)).trans (mul_le_mul_of_nonneg_left (he (i.1,x)) (by positivity))
             _ = _ := by norm_num
    rw [← sq_le_sq₀ (norm_nonneg _) (by change 0 ≤ (48 * _ * M) * (D^2)⁻¹; positivity), EuclideanSpace.norm_sq_eq]
    calc _ ≤ ∑ i : Mode m, (3*(2*K))^2 := Finset.sum_le_sum (fun i _=> pow_le_pow_left₀ (norm_nonneg _) (hR i) _)
         _ ≤ ((Fintype.card (Mode m)+1)^2*(48*M*(D^2)⁻¹)^2 : ℝ) := by
           simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
           refine mul_le_mul (by nlinarith : ((Fintype.card (Mode m)):ℝ)≤((Fintype.card (Mode m):ℝ)+1)^2) (pow_le_pow_left₀ ?_ ?_ _) (by positivity) (by positivity)
           · unfold K D; positivity
           unfold K
           calc _ = (48*M* (D^2)⁻¹) * (‖p‖/D) := by field_simp [ne_of_gt (by dsimp only [D]; positivity : D>0)]; ring
                _ ≤ _ := mul_le_of_le_one_right (by dsimp [D]; positivity) ((div_le_one (by dsimp only [D]; positivity : D>0)).mpr (by dsimp [D]; linarith))
         _ = _ := by unfold jetBound D M; ring

end YM.Trace.Shell
