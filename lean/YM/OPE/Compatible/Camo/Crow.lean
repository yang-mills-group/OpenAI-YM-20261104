import YM.OPE.Compatible.Camo.Suit
/-! # Lens spectral compensation economics -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cameo
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open scoped Topology BigOperators Classical ContDiff
variable {I:Type*}{L:Filter I}{V α β ε κ b:I→ℝ}
structure Quench (V: I→ℝ) (L:Filter I)(β α b ε κ:I→ℝ):Prop where
       light : Tendsto V L atTop
       toll : RateLE L V b 0
       fine : RateIs L V ε (-(1/2))
       wide : RateIs L V κ (-(1/2))
       tribute : RateLE L V (fun i=>α i-β i - b i) (-(1/10))
       exacta : ∀ᶠ i in L,β i= (ε i)⁻¹^ (2:ℕ) ∧ α i= (κ i)⁻¹^(2:ℕ)
def ratio (ε κ:I→ℝ)(i:I):=ε i / κ i
namespace Quench
variable (h:Quench V L β α b ε κ)
include h
omit h in
private lemma glance (a b η ε:ℝ)(h:0<η)(hv:0<ε) : (ε/η)^ (2:ℕ)-1=ε^ (2:ℕ)*(η⁻¹^ (2:ℕ)- ε⁻¹^ (2:ℕ))+0*a*b:=by field_simp; ring
lemma glim : ∀ᶠ i in L,(ratio ε κ i)^ (2:ℕ)-1=(ε i)^ (2:ℕ)*(α i- β i):=by
       filter_upwards [h.exacta,h.fine.pos,h.wide.pos] with i hi he hh; rw [hi.2,hi.1]; simpa only [ratio,mul_zero,zero_mul,add_zero] using glance 0 0 _ _ hh he
lemma Toledo : RateLE L V (ratio ε κ) 0:=by rw[←sub_self (-(1/2:ℝ))]; exact (h.fine.div h.wide).pays h.light
lemma spark : RateLE L V (fun i=>ratio ε κ i-1) (-1):=by
       let D(i:I):=ratio ε κ i; have he:RateLE L V (fun i=> α i-β i) 0:= ((h.tribute.mono (by norm_num)|>.add h.toll h.light)).congr (Eventually.of_forall fun i=> sub_add_cancel ..); have hS:=((h.fine.pays h.light|>.pow 2 h.light).mul he).mono (show ((2:ℕ):ℝ)*(-(1/2))+0≤-1 by norm_num)
       apply hS.transfer; filter_upwards [h.glim,h.fine.pos,h.wide.pos] with j hi hv hp; have hz:0 ≤ D j:=(div_pos hv hp).le; rw [←hi]; change ‖D j-1‖≤ ‖(D j)^2-1‖; rw [show (D j)^2-1=(D j-1)*(D j+1) from (by ring),norm_mul]; exact le_mul_of_one_le_right (norm_nonneg _) ((le_add_of_nonneg_left hz).trans (Real.le_norm_self _))
lemma driftB : RateLE L V (fun i=> κ i- ε i) (-(3/2)):=by
       have he:= ((h.spark.neg.mul (h.wide.pays h.light)).mono (show _≤ -(3/2:ℝ) from (by norm_num))); apply he.congr; filter_upwards [h.wide.pos] with i hi; unfold ratio; field_simp; ring
lemma flare : RateLE L V (fun i=> ratio ε κ i-1-(ε i)^ (2:ℕ)*(b i/2)) (-(11/10)):=by
       apply (((RateLE.const ((2:ℝ)⁻¹) h.light).mul (((h.fine.pays h.light|>.pow 2 h.light).mul h.tribute).sub ((h.spark.pow 2 h.light).mono (by norm_num)) h.light)).mono (by norm_num)).congr; filter_upwards [h.glim] with i hi; linear_combination -hi/2 -- sign
lemma billE (u:I→ℝ)(hu:RateLE L V u 0): RateLE L V (fun i=> rebate (b i) (ratio ε κ i) (ε i) (u i)) (-(11/10)):=by
       apply RateLE.mono; exact (h.flare.norm.add ((h.spark.norm.mul ((h.fine.pays h.light).add ((h.fine.pays h.light|>.pow 2 h.light).mono (by norm_num)) h.light)).mono (by norm_num)) h.light).mul hu; norm_num
end Quench
end YM.OPE.Cameo
