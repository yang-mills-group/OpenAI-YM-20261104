import YM.RegulatorIR.Budget.Tariff

/-!
# Fiber summation of real component tensor networks

Only sums of absolutely summable anchored projections will be interchanged.
Budget lemmas use ENNReal so finiteness doesn't depend on arbitrary values for
non-summable real series.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget

open Finset Set Function
open scoped ENNReal NNReal Topology BigOperators Classical

variable {X Y Z W : Type}

/-- Contraction costs. -/
def quota (T : X → ℝ) (w : X → ℝ≥0∞) : ℝ≥0∞:= ∑' i, ‖T i‖ₑ * w i
lemma quota_mono (T:X→ℝ) {w u : X→ℝ≥0∞} (h : ∀ i,w i≤u i): quota T w≤quota T u :=
  ENNReal.tsum_le_tsum fun i=>mul_le_mul_right (h i) _
lemma quota_dom (T U:X→ℝ) {w : X→ℝ≥0∞} (h:∀ i,‖T i‖ₑ≤‖U i‖ₑ): quota T w≤quota U w:=
  ENNReal.tsum_le_tsum fun i=>mul_le_mul_left (h i) _
@[simp] lemma quota_base (T : X → ℝ): quota T 1=∑' i,‖T i‖ₑ := by simp [quota]
lemma quota_summable {T : X → ℝ} {w : X → ℝ≥0∞} (h:∀ i,1 ≤ w i)(hw:quota T w ≠ ⊤): Summable T := by
 apply Summable.of_norm
 apply tsum_enorm_ne_top_iff_summable_norm.mp
 rw [← quota_base]; exact ne_top_of_le_ne_top hw (quota_mono T h)
lemma quota_eq (T U:X→ℝ) (w:X→ℝ≥0∞) (h:∀ i,‖T i‖ₑ=‖U i‖ₑ): quota T w=quota U w:=
  le_antisymm (quota_dom _ _ fun i=>(h i).le) (quota_dom _ _ fun i=>(h i).ge)
@[simp] lemma quota_zero (w:X→ℝ≥0∞): quota 0 w=0:=by simp [quota]
lemma quota_add (T U:X→ℝ)(w:X→ℝ≥0∞) : quota (T+U) w ≤ quota T w+quota U w := calc
  _ ≤ ∑'x,(‖T x‖ₑ+‖U x‖ₑ)*w x := ENNReal.tsum_le_tsum fun _=>mul_le_mul_left (enorm_add_le ..) _
  _ = _ := by simp_rw [add_mul,quota,ENNReal.tsum_add]
lemma quota_neg (T:X→ℝ)(w:X→ℝ≥0∞) : quota (-T) w=quota T w:=quota_eq _ _ _ fun _=>by simp
lemma quota_sub (T U:X→ℝ)(w:X→ℝ≥0∞) : quota (T-U) w≤quota T w + quota U w := by rw [← quota_neg U,sub_eq_add_neg]; exact quota_add ..
lemma quota_times (T:X→ℝ) (w:X→ℝ≥0∞) (r:ℝ) : quota (fun x=>r*T x) w=‖r‖ₑ * quota T w := by unfold quota; simp_rw [enorm_mul,mul_assoc,ENNReal.tsum_mul_left]
lemma quota_raised (T:X→ℝ)(w:X→ℝ≥0∞)(r:ℝ≥0∞): quota T (fun x=>w x*r)=quota T w*r:= by unfold quota; simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
lemma quota_perm (f:X≃Y) (T:Y→ℝ)(w:Y→ℝ≥0∞): quota (T ∘ f) (w ∘ f)=quota T w:= f.tsum_eq (fun y=>‖T y‖ₑ*w y)
lemma quota_restrict (f:X→Y)(h:Injective f)(T:Y→ℝ)(w:Y→ℝ≥0∞): quota (T ∘ f) (w ∘ f)≤quota T w:= ENNReal.tsum_comp_le_tsum_of_injective h _
lemma term_le (T:X→ℝ)(w:X→ℝ≥0∞)(i:X): ‖T i‖ₑ * w i ≤ quota T w:= ENNReal.le_tsum i
lemma quota_sum {I:Type} (s:Finset I)(f:I→X→ℝ)(w:X→ℝ≥0∞):
   quota (∑ i∈s,f i) w≤∑ i∈s,quota (f i) w:=by
 induction s using Finset.induction_on with
 | empty=>simp
 | insert i s h ih=>rw [sum_insert h,sum_insert h]; exact (quota_add ..).trans (add_le_add_right ih _)
lemma quota_prod (T:X→Y→ℝ)(w:X→Y→ℝ≥0∞) : quota (fun p:X×Y=>T p.1 p.2) (fun p=>w p.1 p.2) = ∑'x, quota (T x) (w x) := ENNReal.tsum_prod (f:=fun x y=>‖T x y‖ₑ*w x y)
lemma inside_quota (T:X→Y→ℝ)(w:X→ℝ≥0∞) : quota (fun x=>∑'y,T x y) w ≤ ∑'x, quota (T x) (fun _=>w x) := by
 apply ENNReal.tsum_le_tsum (f:=fun x=>‖∑'y,T x y‖ₑ*w x)
 intro x; unfold quota; rw [ENNReal.tsum_mul_right]; exact mul_le_mul_left enorm_tsum_le_tsum_enorm _

abbrev Stalk (f:X→Y)(p:Y) := {x : X // f x=p}
namespace Stalk
variable (f:X→Y)

def collect (T:X→ℝ)(y:Y) := ∑' i:Stalk f y,T i.val
def scopeQ (T:X→ℝ)(w:X→ℝ≥0∞)(p:Y) : ℝ≥0∞:=quota (fun x:Stalk f p=>T x.val) (fun x=>w x.val)
lemma total (T:X→ℝ)(w:X→ℝ≥0∞): (∑' p,scopeQ f T w p)=quota T w:= ENNReal.tsum_fiberwise (fun x=>‖T x‖ₑ*w x) f
lemma over_le (T:X→ℝ)(w:X→ℝ≥0∞)(p:Y): scopeQ f T w p ≤ quota T w:= quota_restrict (Subtype.val : Stalk f p→X) Subtype.val_injective ..
lemma quota_collect (T:X→ℝ)(w:Y→ℝ≥0∞) : quota (collect f T) w≤quota T (w ∘ f):=by
 rw [← total f]; apply ENNReal.tsum_le_tsum (f:=fun y=>‖collect f T y‖ₑ*w y)
 intro y; unfold scopeQ quota collect; simp_rw [Function.comp_apply,show ∀ i:Stalk f y,f i.val=y from fun i=>i.property,ENNReal.tsum_mul_right]
 exact mul_le_mul_left enorm_tsum_le_tsum_enorm _
lemma collected_sum {T:X→ℝ}(h:Summable T): (∑' y, collect f T y) = ∑' i,T i:= (h.hasSum.tsum_fiberwise f).tsum_eq
lemma price_collect {T:X→ℝ} (h:quota T 1≠⊤): (∑'y,collect f T y) = ∑'i,T i:= collected_sum f (quota_summable (fun _=> le_rfl) h)
lemma price_comp (T:X→ℝ)(w:Y→ℝ≥0∞)(a:Y) : ‖collect f T a‖ₑ * w a ≤ scopeQ f T (w ∘ f) a := by
  unfold scopeQ quota collect; simp_rw [Function.comp_apply,show ∀ i:Stalk f a,f i.val=a from fun i=>i.property,ENNReal.tsum_mul_right]; exact mul_le_mul_left enorm_tsum_le_tsum_enorm _

end Stalk

end YM.RegulatorIR.Budget
