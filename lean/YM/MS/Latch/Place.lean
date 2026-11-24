import YM.MS.Latch.Post
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
/-!
# Segment frames. Bound from any earlier memory and forcing, no loss of momentum power. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job
open Set Function Filter Finset Metric Real MeasureTheory
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal
open scoped Topology ContDiff Interval
variable {I E F:Type}[ NormedAddCommGroup E][ NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{x y ε d K:ℝ}
abbrev Moments (I:Type)(E:Type):= I→ℝ→ E
-- zipper clock intervals monot and costs
def Atm (I:Type):= I→ Set ℝ
abbrev FrameT (J:I→Set ℝ):= Σ i:I,J i
def plug {J:I→Set ℝ}(F:Moments I E)(z:FrameT J) := F z.1 z.2 -- Π type E maybe add classes omitted
structure Belt (I:Type) where
   slot : I→ Set ℝ
   price: Scale (FrameT slot)
   meas i: MeasurableSet (slot i)
-- use explicit class $OpenPow$ basic factor along t.L.Condition inclusive comparison
namespace Belt
abbrev time (P:Belt I):= FrameT P.slot
variable {P:Belt I}
def δf (p q:P.time):= (p.2.val-q.2.val:ℝ)
structure Walk (P:Belt I): Prop where
   length (p q:P.time) (h:p.1=q.1)(he:0 ≤ δf p q): P.price.length q ≤ P.price.length p
   cheap (p q:P.time) (h:p.1=q.1)(he:0 ≤ δf p q): P.price.basic q ≤ P.price.basic p * (1+δf p q)
structure Slide (P:Belt I)(ε:ℝ)(A B:P.time→ℝ) : Prop where
   target: nn B
   moment : ∃ K:ℝ,0<K∧∀ p q:P.time,p.1=q.1→0≤δf p q → A q≤ K* exp (-ε*δf p q)* B p
omit [NormedSpace ℝ E] in
lemma diffuse (p q:P.time)(h:Walk P)(he:p.1=q.1)(hv:0≤δf p q)(x:E) : P.price.full.cheap q x≤ P.price.full.cheap p x*(1+δf p q):= by
    let Q:=P.price; have ht:=h.length p q he hv; have hQ : Q.weight q x ≤ Q.weight p x:= by unfold Scale.weight; dsimp [Q]; gcongr; -- clamp simplification
    unfold Scale.full; dsimp only; rw [mul_right_comm]; exact mul_le_mul (h.cheap p q he hv) hQ (Q.weight_pos q x).le (mul_nonneg (Q.basic_pos p).le (by linarith))
abbrev stream (P:Belt I)(z:P.time) : Set ℝ:= P.slot z.1 ∩ Set.Iic z.2.val
lemma admit (p:P.time): MeasurableSet (P.stream p):= ( P.meas _ ).inter measurableSet_Iic
abbrev Mu (p:P.time): Measure ℝ:= volume.restrict (P.stream p)
-- alternate Expo integral.Escape cheaper than linear poly.
abbrev cloud (p:P.time)(ε:ℝ)(x:ℝ):= Real.exp (-ε*(p.2.val-x))
lemma capped (h:0<ε)(j:ℕ):∃ K:ℝ,0<K∧∀ u:ℝ, 0 ≤ u →(1+u)^j * exp (-ε*u) ≤ K*exp (-(ε/2)*u):= by
   let U u:= (1+u)^j*exp (-(ε/2)*u); have he :∀ᶠ i in atTop,U i≤1:= (LogTime.vanishes (show 0< ε/2 by positivity) j).eventually (ge_mem_nhds zero_lt_one); obtain ⟨R,hR⟩:= eventually_atTop.mp he; let C:= max R 0; let K:=(1+C)^j
   have hC:C≥0:= le_max_right ..; have hK:1≤K:= one_le_pow₀ (by linarith); refine ⟨K,lt_of_lt_of_le zero_lt_one hK,fun u hu=>?_⟩; have hU: U u≤ K:= by
       by_cases hv:R≤u; · exact (hR u hv).trans hK
       exact (mul_le_of_le_one_right (by positivity) (exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hu)))|>.trans (pow_le_pow_left₀ (by linarith) (add_le_add_right (le_max_of_le_left (le_of_not_ge hv)) (1:ℝ)) _) -- bad messenger
   apply le_trans _ (mul_le_mul_of_nonneg_right hU ( Real.exp_pos (-(ε/2)*u)).le); unfold U; rw [mul_assoc, ← exp_add, show -(ε/2)*u + -(ε/2)*u = - ε*u by ring]
lemma cloud_whole (h:0<ε)(p:P.time): IntegrableOn (cloud p ε) (Set.Iic p.2.val) := by
    let F x := exp (ε*x); let V:= exp (-ε*p.2.val); rw [show cloud p ε=(fun x=>V*F x) from funext fun i=>by unfold F V cloud; rw [ ← exp_add,show -ε*p.2.val+ε*i= _ from ?e]; case e=> ring]; exact (integrableOn_exp_mul_Iic h _).const_mul _
lemma cloudM (he:0<ε)(p:P.time): Integrable (cloud p ε) (Mu p):= (cloud_whole he p).mono_set Set.inter_subset_right
lemma price_c (he:0< ε)(p:P.time) : (∫ t,cloud p ε t∂Mu p) ≤ ε⁻¹ := by
   apply (setIntegral_mono_set (cloud_whole he p) (Filter.Eventually.of_forall fun i=>(Real.exp_pos _).le) (Filter.Eventually.of_forall (show ∀ x, _ → _ from (fun x hx=>(show x∈Set.Iic p.2.val from hx.2)))) ) |>.trans_eq;
   unfold cloud; simp_rw [show ∀ i:ℝ,-ε*(p.2.val-i)= -ε*p.2.val+ ε*i from fun i=> by ring,exp_add]; rw [integral_const_mul, integral_exp_mul_Iic he]; rw [neg_mul, exp_neg ]; field_simp -- theorem search
end Belt
end YM.MS.Latch.Job
