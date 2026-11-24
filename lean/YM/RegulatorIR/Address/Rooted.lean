import YM.RegulatorIR.Address.Count
import YM.RegulatorIR.Cluster.Width

/-! Charge on address/test atom measure before testing. Folds output in l-current
spacing. Skeleton types can vary with rank and stencil: may carry derivative,
reference shape or a finite sign type, etc. Not assuming translation invariance
post-testing. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Address
open MeasureTheory Function Lattice Budget Budget.Tuple Budget.Packet Budget.Tariff Motion Spatial Cluster Cluster.Collapsed
open scoped ENNReal NNReal BigOperators Classical Topology
variable {X Z:Type} {l d:ℝ} {r h u:ℕ}{c:ℝ≥0∞}

structure Calendar (l:ℝ)(X:Type) where
 home : X→Room
 lamp : Cover→ Equiv.Perm X
 lit : ∀ i x, home (lamp i x)=slide l i + home x
namespace Calendar
variable (A:Calendar l X) [MeasurableSpace Z]
def sends (i:Cover): Equiv.Perm (Tuple X r):= Tuple.winding (A.lamp i) r
-- z could be (derivative type × native address × sign × path meta)
structure TagList (X:Type)(Z:Type)[MeasurableSpace Z](r:ℕ) where
  rolls : Tuple X r → Measure Z
  value : Tuple X r → Z → ℝ
  placement : Z→Room
  hValue : ∀ x, Measurable (value x)
  visible : Measurable placement
variable (T:TagList X Z r)
-- test budget, typically includes normalized scaled derivatives
structure Script (Z:Type) [MeasurableSpace Z] where
  test : Z → Room → ℝ
  regular : Measurable (Function.uncurry test)
variable (B:Script Z)
def weighed {l:ℝ}(p:Cover)(v:Tuple X r) (z:Z):ℝ:= T.value v z* B.test z (slide l p+l • T.placement z)
-- A needed for l?
def spoke (p:Cover)(v:Tuple X r):ℝ := ∫ z,weighed (l:=l) T B p ((A.sends p).symm v) z ∂(T.rolls ((A.sends p).symm v))
def calyx : Packet X r:=fun v=>∑' p:Cover, spoke A T B p v

def measure_len (v : Tuple X r)(z:Z) : ℝ := (∑ i, dist (A.home (v i)) 0 / l)+‖T.placement z‖
def pennies (u:ℕ)(v:Tuple X r)(z:Z): ℝ≥0∞:= amount 1 u (measure_len A T v z)
def kme (u:ℕ):ℝ≥0∞:=∑' v:Tuple X r, ∫⁻ z, ‖T.value v z‖ₑ*pennies A T u v z ∂(T.rolls v)
lemma length_nn (hl:0<l) (v:Tuple X r)(z:Z):0 ≤ measure_len A T v z:= by unfold measure_len; positivity
lemma pays_here (v:Tuple X r)(p:Cover)(z:Z)(S:Set Room)(hl:0<l)(h:slide l p + l • T.placement z ∈ S):
     ((realm hl u S).uses A.home).width (A.sends p v) ≤ pennies A T u v z:= by
 apply highest _ u S A.home _ _ (amount_unit (by norm_num) _ (length_nn A T hl ..)); intro i
 change amount l u (Metric.infDist (A.home (A.lamp p (v i))) S) ≤ _
 rw [A.lit]; apply (amount_mono hl u (Metric.infDist_le_dist_of_mem h)).trans
 rw [dist_add_left];unfold amount measure_len
 apply pow_le_pow_left';apply ENNReal.ofReal_le_ofReal
 have ht:= dist_triangle (A.home (v i)) 0 (l • T.placement z)
 rw [dist_zero_left,norm_smul,Real.norm_of_nonneg hl.le] at ht
 rw [div_one,add_le_add_iff_left]; apply (div_le_div_of_nonneg_right ht hl.le).trans
 rw [add_div, mul_div_cancel_left₀ _ hl.ne']; exact add_le_add_left (Finset.single_le_sum (f:=fun i=>dist (A.home (v i)) 0 /l) (fun _ _=>div_nonneg dist_nonneg hl.le) (Finset.mem_univ i)) _

variable (S:Set Room)(x:Room)
structure Bills (B:Script Z)(S:Set Room)(x:Room)(d:ℝ)(c:ℝ≥0∞): Prop where
 width v : v∈S → dist v x ≤ d
 along : ∀ z v,B.test z v≠0→v∈S ∧ ‖B.test z v‖ₑ≤c
variable (H:Bills B S x d c)

include H in
lemma rootStars (hl:0<l) (hd:0≤d) (v:Tuple X r)(z:Z)(u:ℕ) :
    (∑' i:Cover, ‖weighed (l:=l) T B i v z‖ₑ * ((realm hl u S).uses A.home).width (A.sends i v)) ≤ ENNReal.ofReal ((1+2*d/l)^4) * ((‖T.value v z‖ₑ*pennies A T u v z)*c):=by
 apply stars _ (x:=x - l • T.placement z) hl hd; intro i hi
 have ht : B.test z (slide l i+l • T.placement z)≠0:=by intro hh; apply hi; rw [weighed,hh,mul_zero,enorm_zero, zero_mul]
 obtain ⟨hp,hc⟩:= H.along _ _ ht
 constructor
 · convert H.width _ hp using 1; convert (dist_add_right (slide l i) (x-l • T.placement z) (l • T.placement z)).symm using 1; simp
 rw [weighed,enorm_mul]; exact (mul_le_mul' (mul_le_mul_right hc _) (pays_here A T v i z S hl hp)).trans_eq (by ac_rfl)

lemma root_see (T:TagList X Z r)(B:Script Z) (l:ℝ)(v:Tuple X r)(p:Cover): Measurable (weighed (l:=l) T B p v):=(T.hValue _).mul (B.regular.comp (measurable_id.prodMk ((measurable_const (a:=slide l p)).add ((measurable_const (a:=l)).smul T.visible))))
lemma cost_see (u:ℕ)(v:Tuple X r): Measurable (pennies A T u v):= (((measurable_const (a:=∑ i,dist (A.home (v i)) 0 / l)).add T.visible.norm).div_const 1).const_add 1|>.ennreal_ofReal|>.pow_const u

def gridTax (u : ℕ)(B:Script Z)(S:Set Room)(hl:0<l) : ℝ≥0∞:= ∑' p:Cover, ∑' v:Tuple X r, (∫⁻ z, ‖weighed (l:=l) T B p v z‖ₑ * ((realm hl u S).uses A.home).width (A.sends p v) ∂(T.rolls v))
include H in
lemma cost_centers (u:ℕ) (hl:0<l)(hd:0≤d) : gridTax A T u B S hl≤ ENNReal.ofReal ((1+2*d/l)^4) * (kme A T u * c):=by
 unfold gridTax kme; rw [ENNReal.tsum_comm, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro v
 have hp: Measurable fun z=> ‖T.value v z‖ₑ*pennies A T u v z:= Measurable.mul ((T.hValue v).enorm) (cost_see A T u v)
 rw [← MeasureTheory.lintegral_tsum, ← MeasureTheory.lintegral_mul_const _ hp, ← MeasureTheory.lintegral_const_mul _ (hp.mul_const c)]; exact lintegral_mono fun z=> rootStars A T B S x H hl hd v z u
 exact fun p=> ((root_see T B l v p).enorm.mul_const _).aemeasurable
lemma lines (u:ℕ) (hl:0<l):
    (∑' p:Cover, markQ ((realm hl u S).uses A.home) (spoke A T B p)) ≤ gridTax A T u B S hl:=by
 let P:= (realm hl u S).uses A.home;apply ENNReal.tsum_le_tsum;intro p
 unfold markQ quota; rw [← (A.sends (r:=r) p).tsum_eq]; apply ENNReal.tsum_le_tsum;intro v
 simp_rw [spoke, Equiv.symm_apply_apply]
 rw [MeasureTheory.lintegral_mul_const _ ((root_see T B l v p).enorm)]
 exact mul_le_mul_left (MeasureTheory.enorm_integral_le_lintegral_enorm _) _
include H in
lemma wall (u:ℕ)(hl:0<l)(hd:0 ≤ d): markQ ((realm hl u S).uses A.home) (calyx A T B)≤ ENNReal.ofReal ((1+2*d/l)^4)*(kme A T u*c) :=by
 apply (inside_quota (fun v p=>spoke A T B p v) _).trans <| le_trans ?_ ((lines A T B S u hl).trans (cost_centers A T B S x H u hl hd))
 exact (ENNReal.tsum_comm (f:=fun v p=> ‖spoke A T B p v‖ₑ*((realm hl u S).uses A.home).width v)).le
end Calendar
end YM.RegulatorIR.Address
