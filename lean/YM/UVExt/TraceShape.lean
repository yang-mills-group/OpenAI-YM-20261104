import YM.UVExt.TagPrimitive
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
/-! Bounds on the half-plane for the three primitive profiles; upper envelope interpolation at positive real temperatures (constant allowed per profile, independent of coefficients). This is a magnification estimate used *before* Haag and finite Gaussian integration. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay.Traces
open RG Wilson Function Set
open scoped BigOperators Topology ComplexConjugate Classical
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]
variable (f:Ω→Primitive)
/-- Every primitive takes one of the committed kinds across the WHOLE chamber Ω. -/
def UniformForm := (∃ k,∀ w,∃ c g,f w=.thermal c g k) ∨ (∀ w,∃ b, f w=.split b)

def retrieve (r s:ℝ) (k:ℕ) (u v:ℂ) := (Real.log ‖u / (Real.sqrt r : ℂ)^k‖ - Real.log ‖v / (Real.sqrt s:ℂ)^k‖)/(r-s)
lemma retrieves {r s:ℝ} (hr:0<r) (hs:0<s) (he:r≠s) (c:ℂ) (g:ℝ) (k:ℕ) (hc:c≠0) :
 retrieve r s k ((Primitive.thermal c g k).run r) ((Primitive.thermal c g k).run s) = g := by
 have ht (t:ℝ) (ht:0<t) : Real.log ‖(Primitive.thermal c g k).run t / (Real.sqrt t:ℂ)^k‖= Real.log ‖c‖ + t*g := by
   rw [Primitive.standard c g _ _ ht]
   rw [show (c*(Real.sqrt t:ℂ)^k*(Real.exp (t*g):ℂ) / (Real.sqrt t:ℂ)^k)= c*Real.exp (t*g) from by field_simp [pow_ne_zero _ (show (Real.sqrt t:ℂ)≠0 by exact_mod_cast (Real.sqrt_pos.mpr ht).ne')]]
   rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le, Real.log_mul (by simpa using hc) (Real.exp_pos _).ne', Real.log_exp]
 rw [retrieve,ht r hr,ht s hs,div_eq_iff (sub_ne_zero.mpr he)]; ring
lemma holds {c:ℂ} {b:ℝ} {k:ℕ} (z:ℂ) {r s} (hr:0<r) (hs:0<s) (he:r≠s) : let u t := (Primitive.thermal c b k).run (t:ℝ); (Primitive.thermal c b k).run z = (u r * Complex.exp (-Complex.log (r:ℂ)*(k/2) - (r:ℂ)*(retrieve r s k (u r) (u s)))) * Complex.exp (Complex.log z*(k/2)+(z:ℂ)*(retrieve r s k (u r) (u s))) := by
 rcases eq_or_ne c 0 with h|h
 · rw [h]; simp only [Primitive.run,zero_mul]
 intro u

 have hb := retrieves hr hs he c b k h
 change retrieve r s k (u r) (u s)=b at hb
 rw [hb]; unfold u; rw [Primitive.run, Primitive.run]
 rw [mul_assoc c (Complex.exp _), ← Complex.exp_add, show Complex.exp ((Complex.log (r:ℂ)*(k/2)+(r:ℂ)*b)+(-Complex.log (r:ℂ)*(k/2)-(r:ℂ)*b)) = Complex.exp (0:ℂ) from congr_arg Complex.exp (by ring)]; simp

lemma thermal_measurable {k : ℕ} (hf:∀ w,∃ c g,f w=.thermal c g k) {r s:ℝ} (hr:0<r) (hs:0<s) (he:r≠s)
    (hR:Measurable (fun w=>(f w).run (r:ℂ))) (hS:Measurable (fun w=>(f w).run s)) (z:ℂ) : Measurable (fun w=>(f w).run z) := by
 let l w:= retrieve r s k ((f w).run r) ((f w).run s)
 let u w:ℂ := ((f w).run r) * Complex.exp (-Complex.log (r:ℂ)*(k/2)- (r:ℂ)*l w)
 let v w:ℂ := Complex.log z*(k/2) + z*l w
 have hh : (fun w=>(f w).run z)=fun w=>u w* Complex.exp (v w) := funext fun w=>by
   obtain ⟨c,b,hf⟩:= hf w; unfold u v l; rw [hf]; exact holds z hr hs he
 rw [hh]
 have hl : Measurable l := (hR.div_const _ |>.norm.log.sub (hS.div_const _ |>.norm.log)).div_const _
 unfold u v; exact hR.mul ((measurable_const.sub ((Complex.measurable_ofReal.comp hl).const_mul _)).cexp) |>.mul ((measurable_const.add ((Complex.measurable_ofReal.comp hl).const_mul _)).cexp)
lemma split_measurable (hf:∀ w,∃ g,f w=.split g) {r:ℝ} (he:r≠0) (hR: Measurable fun w=>(f w).run r) (z:ℂ) : Measurable (fun w=>(f w).run z) := by
 let u w := Real.log (((f w).run r).re+1)/r
 have hh : (fun w=>(f w).run z)=fun w=>Complex.exp (z*(u w:ℝ))-1 := by
   funext w; obtain ⟨b,hf⟩:=hf w; dsimp only [u]; rw [hf]; dsimp only [Primitive.run]; rw [←Complex.ofReal_mul,←Complex.ofReal_exp, Complex.sub_re,Complex.one_re, Complex.ofReal_re,sub_add_cancel,Real.log_exp]; congr 2; field_simp
 rw [hh]; exact (((Complex.measurable_ofReal.comp (((Complex.measurable_re.comp hR).add_const _|>.log.div_const _))).const_mul z|>.cexp).sub_const 1)
lemma UniformForm.sample (hf:UniformForm f) {r s:ℝ} (hr:0<r) (hs:0<s) (he:r≠s) (hR:Measurable (fun w=>(f w).run r)) (hS:Measurable (fun w=>(f w).run s)) (z:ℂ) : Measurable (fun w=>(f w).run z) := hf.elim (fun ⟨k,hk⟩=>thermal_measurable f hk hr hs he hR hS z) (fun h=> split_measurable f h hr.ne' hR z)

/-- `chaff` is the bounded factor remaining after taking out the growing exponential. -/
def chaff (b u:ℝ) := 1-Real.exp (u*(-|b|))
lemma chaff_nonneg (b:ℝ) {u:ℝ} (hu:0≤u) : 0≤chaff b u := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hu (by simp)))
lemma chaff_mono (b:ℝ) {u v:ℝ} (hu:u≤v) : chaff b u≤chaff b v := by unfold chaff; apply sub_le_sub_left; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_right hu; simp
lemma chaff_div (b:ℝ) {u v:ℝ} (hu:0<u) (hp:u≤v) : chaff b v ≤ (v/u)*chaff b u := by
 let w:=|b|
 have hv:=hu.trans_le hp
 let a (x:ℝ):= x • (-w)

 have h : Real.exp ((u/v) • a v + (1-u/v) • (0:ℝ))≤(u/v) • Real.exp (a v)+(1-u/v) • Real.exp 0 := by
   exact convexOn_exp.2 (show a v ∈ (Set.univ: Set ℝ) from Set.mem_univ _) (show 0∈ (Set.univ: Set ℝ) from Set.mem_univ _) (by positivity) (sub_nonneg.mpr ((div_le_one (hu.trans_le hp)).mpr hp)) (by ring)
 have hv:=hu.trans_le hp
 change Real.exp _≤_ at h; simp only [a,smul_eq_mul,mul_zero,add_zero,Real.exp_zero,mul_one] at h
 change 1-Real.exp (v*(-w)) ≤ v / u * (1-Real.exp (u*(-w)))
 rw [show u/v*(v*(-w))=u*(-w) by field_simp] at h
 field_simp at h ⊢; nlinarith
lemma split_size {u:ℝ} (hu:0<u) (b:ℝ) : ‖(Primitive.split b).run u‖ = Real.exp (u*max b 0)*chaff b u := by
  dsimp only [Primitive.run]; rw [← Complex.ofReal_mul,←Complex.ofReal_exp,show (1:ℂ)=((1:ℝ):ℂ) from rfl,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rcases le_total b 0 with h|h
  · rw [max_eq_right h,chaff,abs_of_nonpos h,neg_neg,mul_zero,Real.exp_zero,one_mul,abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hu.le h)))]; ring
  rw [chaff,max_eq_left h,abs_of_nonneg h,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hu.le h))),mul_sub,mul_one,← Real.exp_add,show u*b+u*(-b)=0 by ring,Real.exp_zero]

def price (p:Primitive) (u:ℝ) := match p with
  | .thermal c _ d=> ‖c‖*Real.sqrt u ^ d
  | .split b=>chaff b u
def growth (p:Primitive) := match p with
  | .thermal _ b _=>b
  | .split b=>max b 0
theorem exact_size {u:ℝ} (hu:0<u) (p:Primitive) : ‖p.run u‖ = Real.exp (growth p*u)* price p u := by
 rcases p with ⟨c,b,k⟩|b
 · rw [Primitive.standard _ _ _ _ hu,price,growth,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.exp_pos _).le, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; ring_nf
 rw [price,growth,mul_comm (max b 0) u]; exact split_size hu b
lemma price_nonneg {u:ℝ} (hu:0≤u) (p:Primitive) : 0 ≤ price p u := by cases p <;> dsimp only [price]; positivity; exact chaff_nonneg _ hu
lemma price_capped {u v:ℝ} (hu:0<u) (hp:u≤v) (p:Primitive) : price p v ≤ (v/u)^p.tax * price p u := by
 rcases p with ⟨c,b,k⟩|b
 · dsimp only [Primitive.tax,price]
   rw [mul_left_comm,←mul_pow]; gcongr
   rw [div_mul_eq_mul_div,le_div_iff₀ hu]
   conv => rhs; rw [← Real.sq_sqrt ((hu.trans_le hp).le)]
   conv => lhs; arg 2; rw [← Real.sq_sqrt hu.le]
   nlinarith only [mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hp) (mul_nonneg (Real.sqrt_nonneg u) (Real.sqrt_nonneg v))]
 dsimp only [Primitive.tax, price]; simpa using chaff_div b hu hp
lemma price_mono {u v:ℝ} (hp:u≤v) (p:Primitive) : price p u≤price p v := by
 rcases p with ⟨c,b,k⟩|b
 · simp only [price]; gcongr
 exact chaff_mono _ hp

open Finset
section product
variable {ι:Type*} (A:Finset ι) (g:ι→Primitive)
def bundled (z:ℂ) := ∏ i∈A,(g i).run z
def wage := ∑ i∈A,(g i).tax
def energy := ∑ i∈A, growth (g i)
def size (u:ℝ) := ∏ i∈A,price (g i) u
lemma booked (z:ℂ) (hp:0<z.re) : ‖bundled A g z‖ ≤ (‖z‖/z.re)^wage A g * ‖bundled A g z.re‖ := by
 unfold bundled wage; simp_rw [norm_prod, ← prod_pow_eq_pow_sum, ← prod_mul_distrib]; apply Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun _ _=>Primitive.angular _ _ hp)
lemma norm_paid {u:ℝ} (hu:0<u) : ‖bundled A g u‖ = Real.exp ((energy A g)*u)*size A g u := by unfold bundled energy size; simp_rw [norm_prod,Finset.sum_mul,exact_size hu,prod_mul_distrib,← Real.exp_sum]
private lemma lesser (V:ℝ→ℝ) (hV : ∀ u≥0, 0≤V u) (F E:ℝ) {u t s:ℝ} (hu:0<u) (hut:u≤t) (hts:t≤s) (hF:0≤F) (h : ∀ t≥u,t≤s→V t≤F*V u ∧ V t≤ F*V s) :
       Real.exp (E*t)*V t≤F*(Real.exp (E*u)*V u+Real.exp (E*s)*V s) := by
 rcases le_total E 0 with hh|hh
 · calc
      _ ≤ Real.exp (E*u)*(F*V u) := mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonpos_left hut hh)) (h t hut hts|>.1) (hV _ (hu.le.trans hut)) (by positivity)
      _ ≤ F*(Real.exp (E*u)*V u+Real.exp (E*s)*V s) := by nlinarith only [mul_nonneg hF (mul_nonneg (Real.exp_pos (E*s)).le (hV s (hu.le.trans (hut.trans hts))))]
 calc
      _ ≤ Real.exp (E*s)*(F*V s) := mul_le_mul (Real.exp_monotone (mul_le_mul_of_nonneg_left hts hh)) (h t hut hts|>.2) (hV _ (hu.le.trans hut)) (by positivity)
      _ ≤ F*(Real.exp (E*u)*V u+Real.exp (E*s)*V s) := by nlinarith only [mul_nonneg hF (mul_nonneg (Real.exp_pos (E*u)).le (hV u hu.le))]
lemma strip_bound {u s:ℝ} (hu:0<u) (z:ℂ) (hz:u≤z.re) (he:z.re≤s) : ‖bundled A g z‖ ≤ ((s/u)^wage A g * (‖z‖/z.re)^wage A g)*(‖bundled A g u‖ + ‖bundled A g s‖) := by
 have hp:=hu.trans_le hz; have hs:=hp.trans_le he
 rw [norm_paid A g hu,norm_paid A g hs,mul_right_comm]
 have hb := booked A g z hp
 rw [norm_paid A g hp] at hb
 refine le_trans hb ?_
 rw [mul_comm ((s/u)^wage A g* _)]
 apply mul_le_mul_of_nonneg_left _ (by positivity)
 apply lesser (size A g) (fun u hu=>Finset.prod_nonneg (fun i _=> price_nonneg hu _)) _ _ hu hz he (by positivity)
 intro t ht he
 have htt := hu.trans_le ht
 unfold size
 rw [wage,←prod_pow_eq_pow_sum, ← prod_mul_distrib,←prod_mul_distrib]
 constructor
 · apply prod_le_prod (fun i _=>price_nonneg (hu.le.trans ht) _) (fun i _=>(price_capped hu ht _).trans _)
   intro i _; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by gcongr) _) (price_nonneg hu.le _)
 apply prod_le_prod (fun i _=>price_nonneg (hu.le.trans ht) _) (fun i _=>(price_mono he _).trans _)
 intro i _; exact le_mul_of_one_le_left (price_nonneg hs.le _) (one_le_pow₀ ((one_le_div hu).mpr (ht.trans he)))
end product
end YM.UVExt.EnergyRay.Traces
