import YM.OPE.Compatible.Ocher.Bruin
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Real
/-! # Probability Lp book numeric. no losses in volume finite sums. Avoid a.e. choices -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {X Y E U:Type*}{s t c:ℝ}{i j k:ℕ}
open PertExtension Series Libra GaussianScore Jargon
section
variable [MeasurableSpace X][NormedAddCommGroup E] {μ:Measure X}
structure Fault (μ:Measure X)(i:ℕ)(f:X→E)(t:ℝ):Prop where
    pos : 0 ≤ t
    strong : AEStronglyMeasurable f μ
    passes : eLpNorm f i μ ≤ ENNReal.ofReal t
namespace Fault
variable {f g:X→E}
lemma rich (h: Fault μ i f t): MemLp f i μ :=⟨h.strong,h.passes.trans_lt ENNReal.ofReal_lt_top⟩
lemma add (h:Fault μ i f t)(he:Fault μ i g s)(hi:1 ≤ i):Fault μ i (f+g) (t+s):= ⟨add_nonneg h.pos he.pos,h.strong.add he.strong,(eLpNorm_add_le h.strong he.strong (by exact_mod_cast hi)).trans ((add_le_add h.passes he.passes).trans (le_of_eq (ENNReal.ofReal_add h.pos he.pos).symm))⟩
lemma sub (h:Fault μ i f t)(he:Fault μ i g s)(hi:1 ≤ i):Fault μ i (f-g) (t+s):= ⟨add_nonneg h.pos he.pos,h.strong.sub he.strong,(eLpNorm_sub_le h.strong he.strong (by exact_mod_cast hi)).trans ((add_le_add h.passes he.passes).trans (le_of_eq (ENNReal.ofReal_add h.pos he.pos).symm))⟩
lemma sum (s:Finset Y)(f:Y→X→E)(v:Y→ℝ)(h:∀ j∈s, Fault μ i (f j) (v j))(hp:1 ≤ i): Fault μ i (∑ j∈s,f j) (∑ j∈s,v j):=by
       induction s using Finset.induction_on with
       | empty=> simp only [sum_empty]; exact ⟨le_rfl,aestronglyMeasurable_zero,by simp⟩
       | insert a s ha ih=> rw[sum_insert ha,sum_insert ha]; exact (h a (mem_insert_self ..)).add (ih (fun j hj=>h j (mem_insert_of_mem hj))) hp
omit [NormedAddCommGroup E] in
lemma pair (i:ℕ)(hx:0 < i): ENNReal.HolderTriple (↑(2*i)) (↑(2*i)) (↑i):=by
       refine ⟨?_⟩; push_cast; rw [← two_mul]; have hh: (i:ℝ≥0∞) ≠0 :=Nat.cast_ne_zero.mpr hx.ne'; have hp:(i:ℝ≥0∞)≠⊤:=by simp
       rw [ENNReal.mul_inv ?_ ?_,← mul_assoc, ENNReal.mul_inv_cancel,one_mul] <;> simp [hh,hp]
omit [NormedAddCommGroup E] in
lemma double {f g:X→ℝ}(h:Fault μ (2*i) f s)(hv:Fault μ (2*i) g t)(he:0 < i):Fault μ i (f*g) (s*t):=by
      haveI := pair i he; refine ⟨mul_nonneg h.pos hv.pos,h.strong.mul hv.strong,?_⟩; apply le_trans (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm h.strong hv.strong (·*·) 1 (p:=↑(2*i)) (q:=↑(2*i)) (r:=↑i) (Eventually.of_forall (fun _=>by simp))) _; rw [ENNReal.coe_one,one_mul,ENNReal.ofReal_mul h.pos]; exact mul_le_mul' h.passes hv.passes
lemma NormT (h:Fault μ i f t): Fault μ i (fun x=>‖f x‖) t:=⟨h.pos,h.strong.norm,by rw [eLpNorm_norm]; exact h.passes⟩
lemma bound [IsProbabilityMeasure μ](ht:0≤t)(he:AEStronglyMeasurable f μ)(hp:∀ᵐ i ∂μ,‖f i‖ ≤ t): Fault μ i f t:= ⟨ht,he,by simpa using eLpNorm_le_of_ae_bound (p:=↑i) hp⟩
lemma constant [IsProbabilityMeasure μ] (v:E): Fault μ i (fun _=>v) ‖v‖:= bound (norm_nonneg _) aestronglyMeasurable_const (Eventually.of_forall fun _=>le_rfl)
lemma mono [IsProbabilityMeasure μ] (h:Fault μ i f s)(he:j ≤ i)(hp:s ≤ t): Fault μ j f t:=⟨h.pos.trans hp,h.strong,(eLpNorm_le_eLpNorm_of_exponent_le (Nat.cast_le.mpr he) h.strong).trans (h.passes.trans (ENNReal.ofReal_le_ofReal hp))⟩
lemma ofLe [NormedAddCommGroup U] {u:X→U}(h: Fault μ i f t)(he:AEStronglyMeasurable u μ)(hv:∀ᵐ x ∂μ, ‖u x‖ ≤ ‖f x‖):Fault μ i u t:=⟨h.pos,he,(eLpNorm_mono_ae hv).trans h.passes⟩
end Fault
end
end YM.OPE.Cinders
