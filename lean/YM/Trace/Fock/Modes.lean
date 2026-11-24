import YM.Trace.Fock.Pure
/-! Product-form and jet-linear moment tests on shell. -/
noncomputable section
set_option maxHeartbeats 400000
set_option autoImplicit false
namespace YM.Trace.Shell
open MeasureTheory Filter Function Set Complex YM Boundary
open scoped ENNReal Topology BigOperators InnerProductSpace Pointwise

def RapidBound (g : Mom → ℂ) : Prop := (Measurable g) ∧ (∀ k : ℕ, ∃ C ≥ (0:ℝ), ∀ p, ‖g p‖ ≤ C * (weight k p)⁻¹)
def filterRapid : Submodule ℂ (Mom→ℂ) where
    carrier := {g | RapidBound g}
    zero_mem' := ⟨by exact measurable_const,fun k=>⟨0,le_rfl,fun p=>by simp only [Pi.zero_apply,norm_zero,zero_mul,le_rfl]⟩⟩
    add_mem' := fun {x y:Mom→ℂ} hx hy=> ⟨hx.1.add hy.1,fun k=>by
       obtain ⟨C,hC,hxk⟩:=hx.2 k
       obtain ⟨D,hD,hyk⟩:=hy.2 k
       exact ⟨C+D,add_nonneg hC hD,fun p=> (norm_add_le ..).trans ((add_le_add (hxk p) (hyk p)).trans_eq (by rw [add_mul]))⟩⟩
    smul_mem' := fun c g h=>⟨h.1.const_smul _,fun k=>by
       obtain ⟨C,hC,hk⟩:=h.2 k
       exact ⟨‖c‖*C,mul_nonneg (norm_nonneg _) hC,fun p=>show ‖c • g p‖ ≤ _ from by rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (hk _) (norm_nonneg _)⟩⟩
def rapidProbe (f : Probe Mom) : filterRapid := ⟨f,f.continuous.measurable,fun k=>⟨_,wavePrice_nonneg f k,weighted_test f k⟩⟩
def rapidRay (f : Test4) : filterRapid := ⟨fun p=>f (ray p),f.continuous.measurable.comp (by fun_prop),fun k=> by
   refine ⟨_, mul_nonneg (orderCost_nonneg f k) (by positivity : (0:ℝ) ≤ 2^k),fun p=> (weighted_test f k (ray p)).trans (mul_le_mul_of_nonneg_left (inv_le_inv₀ (weight_pos ..) (weight_pos k p)|>.mpr ?_) ?_)⟩
   exact pow_le_pow_left₀ (by positivity) (by exact add_le_add_right (norm_ray ..) _) _
   exact mul_nonneg (orderCost_nonneg ..) (by positivity) ⟩
abbrev momentSlot (q : ℕ) := Bool × polySlot q
def momentDegree {q : ℕ} (b : momentSlot q) := b.2.1.val + (if b.1=true then (1:ℕ) else 0)
def momentEntry {q : ℕ} (b : momentSlot q) (p : Mom) := (if b.1=true then (‖p‖:ℂ) else (1:ℂ)) * slotPolynomial b.2 p
@[fun_prop] lemma momentEntry_cont {q : ℕ} (b : momentSlot q) : Continuous (momentEntry b) := by
    unfold momentEntry; split_ifs <;> fun_prop
lemma momentEntry_smul {q : ℕ} (t : ℝ) (ht : 0 ≤ t) (b : momentSlot q) (p) : momentEntry b (t • p) = ↑(t^(momentDegree b)) * momentEntry b p := by
    unfold momentEntry momentDegree; rw [slotPolynomial_dilate]; split_ifs <;> try simp only [norm_smul,Real.norm_of_nonneg ht]
    all_goals push_cast <;> try simp <;> ring
    all_goals simp only [pow_succ]; ring
lemma momentEntry_bound {q : ℕ} (b : momentSlot q) : ∃ C ≥ (0:ℝ), ∀ p : Mom, ‖momentEntry b p‖ ≤ C * weight (momentDegree b) p := by
    let G := momentEntry b
    obtain ⟨C,h⟩:= Bornology.IsBounded.subset_closedBall ((isCompact_closedBall (0:Mom) 1).image_of_continuousOn ((momentEntry_cont _).continuousOn)|>.isBounded) 0
    have hh p (hp:‖p‖≤1) : ‖G p‖≤C := by simpa only [Metric.mem_closedBall,dist_zero_right] using h (mem_image_of_mem G (Metric.mem_closedBall.mpr (by rwa [dist_zero_right])))
    refine ⟨max C 0,le_max_right ..,fun p=> ?_⟩
    let t := max 1 ‖p‖
    have ht : 0<t := zero_lt_one.trans_le (le_max_left ..)
    let x := t⁻¹ • p
    have hx : ‖x‖ ≤ 1 := by rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_le_iff₀ ht, mul_one]; exact le_max_right ..
    have hp := smul_inv_smul₀ (α:=ℝ) ht.ne' p
    nth_rewrite 1 [← hp]; rw [momentEntry_smul t ht.le, norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_pos ht _|>.le)]
    rw [mul_comm (max C 0)]; exact mul_le_mul (pow_le_pow_left₀ ht.le (by exact max_le (by linarith [norm_nonneg p]) (by linarith)) _) (le_trans (hh x hx) (le_max_left ..)) (norm_nonneg _) (weight_pos ..|>.le)

lemma rapid_product_integrable {q : ℕ} (b : momentSlot q) (g : filterRapid) : Integrable (fun p=> (g:Mom→ℂ) p * momentEntry b p) ν := by
    let k := momentDegree b
    obtain ⟨C,hC,hE⟩:=momentEntry_bound b
    obtain ⟨D,hD,H⟩:=g.property.2 (k+3)
    have he : Measurable (fun p=> (g:Mom→ℂ) p * momentEntry b p) := g.property.1.mul (momentEntry_cont b).measurable
    refine (integrable_norm_iff he.aestronglyMeasurable).mp (integrable_shell_arbitrary_bound (fun p=> ‖(g:Mom→ℂ) p * momentEntry b p‖) he.norm (D*C) 3 (by norm_num) (fun p=> ?_)) -- position? check
    have hk : 0<1+‖p‖ := by positivity
    rw [norm_norm,norm_mul,Real.rpow_neg (x:=1+‖p‖) hk.le 3] -- likely rw bad
    refine (mul_le_mul (H p) (hE p) (norm_nonneg _) (mul_nonneg hD (by exact inv_nonneg.mpr (weight_pos ..|>.le)))).trans_eq ?_
    unfold weight; rw [pow_add]; norm_num; field_simp; unfold k; ring

def momentLM (q : ℕ) : filterRapid →ₗ[ℂ] (momentSlot q→ℂ) where
     toFun g b := ∫ p, (g:Mom→ℂ) p * momentEntry b p ∂ν
     map_add' a b := funext (fun k=> by change (∫ p, _ * momentEntry k p ∂ν)=_+_; simp only [Submodule.coe_add,Pi.add_apply] <;> simp_rw [add_mul]; exact MeasureTheory.integral_add (rapid_product_integrable k a) (rapid_product_integrable k b))
     map_smul' c x := funext (fun k=> by change (∫ p, (c*(x:Mom→ℂ) p) * momentEntry k p ∂ν)= c * (∫ p, (x:Mom→ℂ) p * momentEntry k p ∂ν); simp_rw [mul_assoc, MeasureTheory.integral_const_mul])

end YM.Trace.Shell
