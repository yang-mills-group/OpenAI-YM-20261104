import YM.Trace.Fock.Modes
noncomputable section
set_option maxHeartbeats 800000
set_option autoImplicit false
namespace YM.Trace.Shell
open MeasureTheory Function Complex Set Filter YM Boundary
open scoped Pointwise BigOperators ENNReal Topology

variable {n m : ℕ}
def testJoint (k : Fin n → filterRapid) (x : Cords n) := ∏ i : Fin n, (k i).val (x i)
@[fun_prop] lemma testJoint_meas (k : Fin n→filterRapid) : Measurable (testJoint k) := Finset.measurable_prod _ (fun i _=> (k i).property.1.comp (measurable_pi_apply ..))
lemma testJoint_bound (N : ℕ) (k : Fin n→filterRapid) : ∃ C ≥ (0:ℝ), ∀ x, ‖testJoint k x‖ ≤ C * packing x N := by
    choose c hc h using fun i=> (k i).property.2 N
    refine ⟨∏ i : Fin n, c i,Finset.prod_nonneg (fun i _=> hc i),fun x=> ?_⟩
    unfold testJoint packing; rw [← Finset.prod_mul_distrib,norm_prod]; exact Finset.prod_le_prod (fun i _=>norm_nonneg _) (fun i _=>h i _)
variable (v : Test4→L[ℂ] Sum m) (k : @Angle m (n+1)) (hv : FieldImage v)
include hv
lemma bare_joint_integrable (N : ℕ) (hN : Integrable (fun x: Cords (n+1) => ‖fullWave v _ x‖ * weight (n+1) x * packing x N) (νpow _)) (g : Cords (n+1) → ℂ) (hg : Measurable g) (hG : ∃ C ≥ (0:ℝ),∀ x, ‖g x‖ ≤ C * packing x N) : Integrable (fun x => smoothBody v k x * g x) (νpow _) := by
    rcases hG with ⟨C,hC,hc⟩
    refine (hN.const_mul C).mono' ((smoothBody_meas v _).mul hg|>.aestronglyMeasurable) (.of_forall fun x=> ?_)
    rw [norm_mul]; unfold smoothBody; rw [norm_mul,norm_real,Real.norm_of_nonneg (nonnegative_mill _)]
    apply le_trans (b:=((weight (n+1) x) * ‖fullWave v (n+1) x‖) * (C * packing x N)) ?_ (le_of_eq ?_)
    · exact mul_le_mul (mul_le_mul (mill_le _) (PiLp.norm_apply_le _ _) (norm_nonneg _) (weight_pos ..|>.le)) (hc _) (norm_nonneg _) (mul_nonneg (weight_pos _ x|>.le) (norm_nonneg _))
    ring
lemma joint_integrable (w : Fin (n+1)→filterRapid) : Integrable (fun x=> smoothBody v k x * testJoint w x) (νpow _) := by
    obtain ⟨N,hN⟩:= all_moments v hv (n+1) (n+1)
    exact bare_joint_integrable v _ hv N hN _ (testJoint_meas w) (testJoint_bound _ _)
noncomputable def stripeIntegral (w : Fin (n+1)→filterRapid) := ∫ x:Cords (n+1), smoothBody v k x * testJoint w x ∂νpow (n+1)
noncomputable def sliceTest (w : Fin (n+1)→filterRapid) (i : Fin (n+1)) (x : Mom) := ∫ y: Cords n, smoothBody v k (join i (x,y)) * testJoint (w ∘ i.succAbove) y ∂νpow n
omit hv in
lemma join_testJoint (w : Fin (n+1)→filterRapid) (i) (x : Mom×Cords n) : testJoint w (join i x) = (w i).val x.1 * testJoint (w ∘ i.succAbove) x.2 := by simp_rw [testJoint,Fin.prod_univ_succAbove (x:=i) (fun j => (w j).val ((join i x) j)), join_expose,join_pos]; rfl
lemma stripe_cut (w : Fin (n+1)→filterRapid) (i : Fin (n+1)) : stripeIntegral v k w = ∫ p: Mom, (w i).val p * (sliceTest v k w i p)∂ν := by
    unfold stripeIntegral
    rw [integrate_joined _ (joint_integrable v k hv w) i]
    exact integral_congr_ae (.of_forall (fun z=> by unfold sliceTest; dsimp only; rw [← MeasureTheory.integral_const_mul]; exact integral_congr_ae (.of_forall (fun x=> by dsimp only; rw [join_testJoint]; ring))))
omit hv in
lemma replacementMeas (i : Fin (n+1)) (w : Fin (n+1)→filterRapid) : Measurable (fun x:Cords (n+1) => smoothBody v k x * testJoint (w ∘ i.succAbove) (expose i x)) :=
    (smoothBody_meas v _).mul ((testJoint_meas ..).comp (expose_meas i))
lemma replacementControl (i : Fin (n+1)) : ∃ N : ℕ, ∀ w, Control N (sliceTest v k w i) := by
    obtain ⟨N,hN⟩:=all_moments v hv (n+1) (n+1)
    refine ⟨N,fun w=> ?_⟩
    let D := testJoint (w ∘ i.succAbove)
    let R (x : Cords (n+1)) := ((weight N (x i))⁻¹ : ℂ) * D (expose i x)
    let Q (x : Cords (n+1)) := smoothBody v k x * D (expose i x)
    obtain ⟨C,hC,hc⟩ : ∃ C ≥ (0:ℝ), ∀ x:Cords n, ‖D x‖ ≤ C*packing x N := testJoint_bound ..
    have hg := ((testJoint_meas (n:=n) (w ∘ i.succAbove)).comp (expose_meas i))
    have hm : Integrable (fun x=> smoothBody v k x * R x) (νpow _) := bare_joint_integrable v _ hv N hN R
      ((by dsimp only [weight]; fun_prop : Measurable (fun x:Cords (n+1)=> ((weight N (x i))⁻¹ : ℂ))).mul hg) ⟨C,hC,fun x=> ?_⟩
    swap
    · unfold R; rw [norm_mul, ← ofReal_inv,norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (weight_pos ..|>.le)),packing_expose i]
      exact (mul_le_mul_of_nonneg_left (hc _) (inv_nonneg.mpr (weight_pos ..|>.le))).trans (by ring_nf; rfl) -- equality ring perhaps
    have hM : Integrable (fun x : Cords (n+1) => (weight N (x i))⁻¹ * ‖Q x‖) _ := hm.norm.congr (.of_forall fun x=> by dsimp [R,Q]; rw [norm_mul,norm_mul,norm_mul,← ofReal_inv,norm_real,Real.norm_of_nonneg (inv_nonneg.mpr (weight_pos ..|>.le))]; ring)
    have hJ (x): (∫ y:Cords n, Q (join i (x,y)) ∂νpow n) = sliceTest v k w i x := integral_congr_ae (.of_forall (fun y=> by dsimp [Q]; rw [expose_join]))
    have hX := integrable_join_mul Q i (fun x:Mom=> (weight N x)⁻¹) hM (fun _=> inv_nonneg.mpr (weight_pos ..|>.le)) ((replacementMeas v _ ..).aestronglyMeasurable) (by exact (measurable_inv.comp ((measurable_const.add (by exact continuous_norm.measurable : Measurable (fun p:Mom=> ‖p‖))).pow_const N)).aestronglyMeasurable)
    simp_rw [hJ, inv_mul_eq_div] at hX
    have H (x: Mom): (fun y : Cords n=> (Q ∘ join i) (x,y)) = _ := rfl
    refine ⟨?_, hX⟩
    change AEStronglyMeasurable (fun x => sliceTest v k w i x) ν
    simp_rw [← hJ] -- wrong simp rec
    exact (((replacementMeas v k i w).comp (join i|>.measurable)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable

omit hv in
private lemma remove_update (w : Fin (n+1)→filterRapid) (i : Fin (n+1)) (t) : update w i t ∘ i.succAbove = w ∘ i.succAbove := funext (fun q=> by simp [Function.update,Fin.succAbove_ne ..])
omit hv in
lemma slice_update (w:Fin (n+1)→filterRapid) (i t) : sliceTest v k (update w i t) i = sliceTest v k w i := by unfold sliceTest; simp only [remove_update]
lemma stripe_lin1 (w : Fin (n+1)→filterRapid) (i) (a b) : stripeIntegral v k (update w i (a+b))=stripeIntegral v k (update w i a) +stripeIntegral v k (update w i b) := by
 simp_rw [stripe_cut v k hv _ i,slice_update .., update_self,Submodule.coe_add,Pi.add_apply, add_mul]
 suffices H : ∀ r : filterRapid, Integrable (fun p=>r.val p * sliceTest v k w i p) ν by
    exact MeasureTheory.integral_add (H _) (H _)
 obtain ⟨N,hN⟩:=replacementControl v k hv i
 intro r; choose C hC hc using r.property.2 N
 let F := sliceTest v k w i
 refine ((hN w).integrable.const_mul C).mono' (r.property.1.aestronglyMeasurable.mul (hN w).ae) (.of_forall fun p=> ?_)
 rw [norm_mul]; change _ ≤ C*(‖F p‖/ weight N p); rw [div_eq_mul_inv,mul_comm ‖F p‖,← mul_assoc]
 exact mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _)
noncomputable def stripeMap : MultilinearMap ℂ (fun _:Fin (n+1) => filterRapid) ℂ := MultilinearMap.mk' (f:=stripeIntegral v k) (h₁:=stripe_lin1 v k hv) (h₂:=fun w i c a=> by
 simp_rw [stripe_cut v k hv _ i,slice_update ..,update_self,Submodule.coe_smul,Pi.smul_apply,smul_eq_mul,mul_assoc,MeasureTheory.integral_const_mul])

end YM.Trace.Shell
