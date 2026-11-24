import YM.Trace.Fock.Localization
/-!
First isolate a single positive-timelike energy branch on shell, after testing all
other positions as indicated. No evaluation at an individual momentum in the Yang--Mills
theory. The product Fock amplitudes are only conditional within FieldImage.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace YM.Trace.Shell
open YM Boundary Function MeasureTheory Filter Complex Set
open scoped Topology BigOperators ENNReal Topology InnerProductSpace Pointwise
variable {m n : ℕ}
abbrev Leg {n : ℕ} := Mom × Cords n
noncomputable def join (i : Fin (n+1)) : @Leg n ≃ᵐ Cords (n+1) := (MeasurableEquiv.piFinSuccAbove (fun _=> Mom) i).symm -- leg type synonym def univ? abbrev replace
lemma join_eq (i : Fin (n+1)) (x y) : join i (x,y)=Fin.insertNth i x y := rfl
lemma join_preserving (i : Fin (n+1)) : MeasurePreserving (join i) (ν.prod (νpow n)) (νpow _) := MeasurePreserving.symm
   (MeasurableEquiv.piFinSuccAbove (fun _=> Mom) i) (measurePreserving_piFinSuccAbove (fun _=>ν) i)
lemma join_pos (i : Fin (n+1)) (t) : join i t i=t.1 := by rw [← Prod.mk.eta (p:=t),join_eq]; exact Fin.insertNth_apply_same (α:=fun _=>Mom) i t.1 t.2
lemma join_expose (i : Fin (n+1)) (z : Mom × Cords n) (j) : join i z (i.succAbove j)=z.2 j := by rw [← Prod.mk.eta (p:=z),join_eq]; exact Fin.insertNth_apply_succAbove (α:=fun _=>Mom) i z.1 z.2 j
noncomputable def expose (i : Fin (n+1)) (x:Cords (n+1)) : Cords n := fun j=> x (i.succAbove j)
@[fun_prop] lemma expose_meas (i : Fin (n+1)) : Measurable (expose i) := measurable_pi_iff.mpr fun _=> measurable_pi_apply ..
lemma expose_join (i : Fin (n+1)) (x y) : expose i (join i (x,y))=y := funext (join_expose _ _)
lemma packing_expose (i : Fin (n+1)) (x:Cords (n+1)) k : packing x k= (weight k (x i))⁻¹ * packing (expose i x) k := Fin.prod_univ_succAbove (fun j=> (weight k (x j))⁻¹) i
lemma testedPlus_split (i : Fin (n+1)) (f : Test4) (a : Fin n→Test4) (x y) : testedPlus (i.insertNth f a) (join i (x,y)) = plus f (ray x) * testedPlus a y := by
    unfold testedPlus; rw [Fin.prod_univ_succAbove (x:=i)]; simp_rw [Fin.insertNth_apply_succAbove,Fin.insertNth_apply_same,join_expose, join_pos]
lemma testedMinus_split (i : Fin (n+1)) (f : Test4) (a : Fin n→Test4) (x y) : testedMinus (i.insertNth f a) (join i (x,y)) = Probe.hat f (ray x) * testedMinus a y := by
    unfold testedMinus; rw [Fin.prod_univ_succAbove (x:=i)]; simp_rw [Fin.insertNth_apply_succAbove,Fin.insertNth_apply_same,join_expose, join_pos]
lemma integrate_joined {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Cords (n+1)→E) (hf : Integrable f (νpow ..)) (i) :
      (∫ x, f x∂νpow (n+1)) = ∫ r:Mom,∫ x:Cords n, f (join i (r,x))∂νpow n ∂ν := by
      rw [← (join_preserving i).integral_comp (join i|>.measurableEmbedding),integral_prod]; exact (join_preserving i).integrable_comp_emb (join i|>.measurableEmbedding)|>.mpr hf
lemma integrable_join_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Cords (n+1)→E) (i) (g : Mom→ℝ) (hf : Integrable (fun x=> g (x i) * ‖f x‖) (νpow ..)) (he : ∀ p, 0≤g p) (hm : AEStronglyMeasurable f (νpow ..)) (hg : AEStronglyMeasurable g ν): Integrable (fun r : Mom =>
     g r * ‖∫ x:Cords n, f (join i (r,x))∂νpow n‖) ν := by
   have hv := (join_preserving i).integrable_comp_emb (join i|>.measurableEmbedding)|>.mpr hf
   have hi : AEStronglyMeasurable (f ∘ (join i)) (ν.prod (νpow n)) := hm.comp_quasiMeasurePreserving (join_preserving i|>.quasiMeasurePreserving)
   refine (Integrable.integral_prod_left hv).mono' (hg.mul (hi.integral_prod_right'.norm)) (.of_forall (fun x=> ?_))
   simp only [norm_mul,Real.norm_of_nonneg (he ..),norm_norm,Function.comp_apply,join_pos, MeasureTheory.integral_const_mul]
   exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm ..) (he _)


variable (v : Test4→L[ℂ] Sum m) (hv : FieldImage v) (k : @Angle m (n+1)) (t : Fin n → Test4)
noncomputable def smoothBody (x : Cords (n+1)) := (mill x : ℂ) * (fullWave v _ x k)
omit hv in
@[fun_prop] lemma smoothBody_meas : Measurable (smoothBody v k) := (measurable_ofReal.comp (measurable_mill (n+1))).mul
   ((PiLp.continuous_apply ..).measurable.comp (fullWave_meas v _))
noncomputable def rowA (i : Fin (n+1)) (x : Mom) := ∫ y : Cords n, smoothBody v k (join i (x,y)) * testedMinus t y ∂νpow n
noncomputable def rowB (i : Fin (n+1)) (x : Mom) := ∫ y : Cords n, star (smoothBody v k (join i (x,y))) * testedPlus t y ∂νpow n
omit hv in
@[fun_prop] lemma rowA_meas (i : Fin (n+1)) : StronglyMeasurable (rowA v k t i) := StronglyMeasurable.integral_prod_right' (by
     refine ((((smoothBody_meas v k).comp (join i|>.measurable)).mul ((measurable_testedMinus t).comp ((measurable_snd : Measurable (Prod.snd : Mom × Cords n→_))))).stronglyMeasurable))
omit hv in
@[fun_prop] lemma rowB_meas (i : Fin (n+1)) : StronglyMeasurable (rowB v k t i) := StronglyMeasurable.integral_prod_right' (by
     exact (((continuous_star.measurable.comp ((smoothBody_meas v k).comp (join i|>.measurable))).mul ((measurable_testedPlus t).comp ((measurable_snd : Measurable (Prod.snd : Mom × Cords n→_))))).stronglyMeasurable))
include hv in
private lemma cost_tested (r : ℕ) (hs : Integrable (fun x : Cords (n+1) => ‖fullWave v _ x‖ * weight (n+1) x * packing x r) (νpow _))
    (U : Cords n → ℂ) (hu : Measurable U) (hu' : ∃ C, ∀ x, ‖U x‖ ≤ C * packing x r) (i): Integrable (fun x:Cords (n+1)=> (weight r (x i))⁻¹ * ‖smoothBody v k x‖ * ‖U (expose i x)‖) (νpow _) := by
    obtain ⟨C,hC⟩:=hu'; let q : Cords (n+1)→ℝ := weight (n+1)
    refine (hs.mul_const C).mono' (by apply Measurable.aestronglyMeasurable; exact ((Measurable.mul ((by unfold weight; fun_prop):Measurable (fun x:Cords (n+1) => (weight r (x i))⁻¹)) ((smoothBody_meas v _).norm)).mul ((hu.comp (expose_meas ..)).norm))) (.of_forall fun x=> ?_)
    have ht : ‖smoothBody v k x‖ ≤ q x*‖fullWave v (n+1) x‖ := by
        unfold smoothBody; rw [norm_mul, norm_real,Real.norm_of_nonneg (nonnegative_mill x)]
        exact mul_le_mul (mill_le x) (PiLp.norm_apply_le ..) (norm_nonneg _) (weight_pos (n+1) x).le
    simp_rw [norm_mul,norm_norm,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (weight_pos ..|>.le)), packing_expose i x] -- args missing
    calc _ ≤ (weight r (x i))⁻¹ * (q x*‖fullWave v (n+1) x‖) * (C*packing (expose i x) r) := mul_le_mul (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (weight_pos ..|>.le))) (hC _) (norm_nonneg _) (by have h := inv_nonneg.mpr (weight_pos r (x i)|>.le); exact mul_nonneg h (mul_nonneg (weight_pos (n+1) x|>.le) (norm_nonneg _)))
         _ = _ := by dsimp [q] at *; ring
omit hv in
private lemma int_row (i : Fin (n+1)) (t : ℕ) (f : Cords (n+1)→ℂ) (hf : Measurable f) (hg : Integrable (fun x=> (weight t (x i))⁻¹ * ‖f x‖) (νpow _)) :
        Integrable (fun x => ‖∫ r, f (join i (x,r))∂νpow n‖ / (1+‖x‖)^t) ν :=
    (integrable_join_mul f i (g:=fun s=> (weight t s)⁻¹) hg (fun _=> inv_nonneg.mpr (weight_pos ..|>.le)) hf.aestronglyMeasurable (by apply Measurable.aestronglyMeasurable; unfold weight; fun_prop)).congr (Eventually.of_forall (fun x=> inv_mul_eq_div ..))

include hv in
lemma controlled_slice : ∃ N : ℕ, ∀ t : Fin n→Test4, ∀ i : Fin (n+1), Integrable (fun x=> ‖rowA v k t i x‖ / (1+‖x‖)^N) ν ∧
       Integrable (fun x=> ‖rowB v k t i x‖ / (1+‖x‖)^N) ν := by
    obtain ⟨p,hp⟩:=all_moments v hv (n+1) (n+1)
    have ht b hb := cost_tested v hv k p hp b hb
    have he (i : Fin (n+1)) (f : Cords n→ℂ) (hf : Measurable f) (hg : ∃ C, ∀ x, ‖f x‖ ≤ C * packing x p) (g : Cords (n+1)→ℂ)
        (H : Measurable g) (hh : ∀ x, ‖g x‖=‖smoothBody v k x‖ * ‖f (expose i x)‖): Integrable (fun x => ‖∫ r, g (join i (x,r))∂νpow n‖ / (1+‖x‖)^p) ν := by
         refine int_row (i:=i) p g H ?_
         simp_rw [hh,← mul_assoc]; exact ht f hf hg _
    refine ⟨p,fun t i=> ⟨?_,?_⟩⟩
    · have hA := he i (testedMinus t) (measurable_testedMinus _) ⟨locatedCost t p,by exact fun x=> bound_negative ..⟩
           (fun x=>smoothBody v k x * (testedMinus t (expose i x))) ((smoothBody_meas ..).mul ((measurable_testedMinus ..).comp (expose_meas ..))) (fun _=> norm_mul _ _)
      simpa only [rowA,expose_join] using hA
    have hB := he i (testedPlus t) (measurable_testedPlus _) ⟨locatedCost t p,by exact fun x=> bound_positive ..⟩
        (fun x=>star (smoothBody v k x) * (testedPlus t (expose i x))) ((continuous_star.measurable.comp (smoothBody_meas ..)).mul ((measurable_testedPlus ..).comp (expose_meas ..))) (by intro x; rw [norm_mul,norm_star])
    simpa only [rowB,expose_join] using hB
private lemma kernel_rowA (i : Fin (n+1)) (f : Test4) (r:Mom) : Probe.hat f (ray r) * rowA v k t i r = ∫ y:Cords n, kernelA v k (i.insertNth (α:=fun _=>Test4) f t) (join i (r,y))∂νpow n := by
    unfold rowA kernelA; rw [← MeasureTheory.integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun y => ?_); simp only [testedMinus_split,smoothBody]; ring
private lemma kernel_rowB (i : Fin (n+1)) (f : Test4) (r:Mom) : plus f (ray r) * rowB v k t i r = ∫ y:Cords n, kernelB v k (i.insertNth (α:=fun _=>Test4) f t) (join i (r,y))∂νpow n := by
    unfold rowB kernelB; rw [← MeasureTheory.integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun y => ?_); simp only [testedPlus_split,smoothBody]; push_cast; simp only [star_mul',Complex.star_def,conj_ofReal]; ring
abbrev Eligible (f : Test4) := CC f ∧ tsupport f ⊆ Mink.spacelike
include hv in
lemma sliced_match (i : Fin (n+1)) (ht : ∀ j, Eligible (t j)) (f : Test4) (hf : Eligible f) :
    (∫ r, Probe.hat f (ray r) * rowA v k t i r∂ν) = ∫ r, plus f (ray r) * rowB v k t i r∂ν := by
      let V : Fin (n+1)→Test4 := i.insertNth f t
      have hV (j) : Eligible (V j) := by
          by_cases h : j=i; subst j; simpa only [V,Fin.insertNth_apply_same] using hf
          obtain ⟨j,rfl⟩ := Fin.exists_succAbove_eq_iff.mpr h
          simpa only [V,Fin.insertNth_apply_succAbove] using ht j
      calc _ = ∫ x, kernelA v k (i.insertNth f t) x∂νpow (n+1) := integral_congr_ae (.of_forall (kernel_rowA v k t i f))|>.trans (integrate_joined (kernelA v k (i.insertNth f t)) (kernel_integrable v hv _ _ |>.1) i).symm
           _ = ∫ x, kernelB v k V x∂νpow (n+1) := kernel_match v hv V (fun j=>(hV j).1) (fun j=>(hV j).2) k
           _ = _ := (integrate_joined (kernelB v k (i.insertNth f t)) (kernel_integrable v hv _ _ |>.2) i).trans (integral_congr_ae (.of_forall fun x => kernel_rowB v k t i f x|>.symm))
end YM.Trace.Shell
