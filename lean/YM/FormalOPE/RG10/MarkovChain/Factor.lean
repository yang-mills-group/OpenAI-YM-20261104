import YM.FormalOPE.RG10.MarkovChain.Band
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Order
/-!
 # Formal exponential multiplicativity for log-positive PS
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Finset MeasureTheory PertExtension Precision
open PowerSeries Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {R S:Type} [CommRing R][CommRing S] (Y : ℝ→+* R) {A B: PowerSeries R} (h:constantCoeff A=0)(H:constantCoeff B=0)
namespace Formal
 def press (k:ℕ)(x:PowerSeries R):= C (Y ((k.factorial:ℝ)⁻¹)) * x^k -- inv ambiguous; r doesn't Inverse
 def expander (x:PowerSeries R): PowerSeries R:= PowerSeries.mk fun k=> coeff k (∑ i∈range (k+1), press Y i x)
lemma halts (j k:ℕ)(hi:j<k){A: PowerSeries R}(ha: constantCoeff A=0): coeff j (press Y k A)=0:= by
 unfold press; rw [coeff_C_mul]; apply mul_eq_zero_of_right; exact coeff_of_lt_order _ (lt_of_lt_of_le (by exact_mod_cast hi) (le_order_pow_of_constantCoeff_eq_zero k ha))
include h in
lemma triangular (k:ℕ): Through k (expander Y A) (∑ i∈range (k+1),press Y i A):=by
 intro i hi; unfold expander; rw [coeff_mk,map_sum,map_sum]; apply Finset.sum_subset (range_mono (by omega)); intro j hj hk; simp only [mem_range, not_lt] at hk; exact halts Y i j (by omega) h -- include h
-- C-image elementary table
lemma rate (a b:PowerSeries R)(k:ℕ): press Y k (a+b)=∑ i∈ antidiagonal k, press Y i.1 a * press Y i.2 b:= by
 unfold press; rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, Finset.mul_sum]; apply Finset.sum_congr rfl fun i hi=> ?_
 dsimp only; have h: i ≤ k:=Nat.le_of_lt_succ (mem_range.mp hi)
 let z: ℝ := k.choose i; let s:=k-i
 have he: (k.factorial:ℝ)⁻¹ * (k.choose i:ℝ)= (i.factorial:ℝ)⁻¹ * (s.factorial:ℝ)⁻¹ := by field_simp; exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
 rw [← map_natCast (C.comp Y) (k.choose i)]; change _ * (_*_ * (C (Y (k.choose i:ℝ))))=_; calc
     _ = (C.comp Y) (_* (k.choose i:ℝ))*a^i*b^s:= by rw [map_mul]; dsimp; ring
     _ = _ := by rw [he,map_mul]; dsimp; ring
lemma press_zero (x:PowerSeries R): press Y 0 x=1:=by simp [press]
include h H in
lemma low (p:ℕ×ℕ)(k:ℕ)(hk:k<p.1+p.2): coeff k (press Y p.1 A * press Y p.2 B)=0:= by
 rw [coeff_mul]; apply Finset.sum_eq_zero; intro i hi
 have he:= mem_antidiagonal.mp hi
 by_cases hl:i.1<p.1
 · rw [halts Y _ _ hl h,zero_mul]
 rw [halts Y _ p.2 (by omega) H,mul_zero]
include h H in
theorem multispecies : expander Y (A+B)=expander Y A*expander Y B:= by
 apply PowerSeries.ext; intro i
 let r:= Finset.range (i+1); let f (k:ℕ):=press Y k A; let g (k:ℕ):=press Y k B
 rw [((triangular Y h i).mul (triangular Y H i)) i le_rfl]; unfold expander; rw [coeff_mk]; simp_rw [rate Y A B];
 change coeff i (∑ j∈r,∑ k∈ antidiagonal j,f k.1*g k.2)=coeff i ((∑ j∈r,f j)*(∑ j∈r,g j))
 rw [Finset.sum_mul_sum,← Finset.sum_product', ← Finset.sum_biUnion]; swap
 · intro a ha b hb hh; apply Finset.disjoint_left.mpr; intro i hi hp; exact hh ((mem_antidiagonal.mp hi).symm.trans (mem_antidiagonal.mp hp))
 rw [map_sum,map_sum]; apply Finset.sum_subset
 · intro x h; obtain ⟨t,ht,h⟩:= mem_biUnion.mp h; have hd:= mem_range.mp ht; have he:= mem_antidiagonal.mp h; exact mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩
 intro p hp ht; apply low Y h H p
 by_contra! hh; exact ht (mem_biUnion.mpr ⟨p.1+p.2,mem_range.mpr (by omega),mem_antidiagonal.mpr rfl⟩)
end Formal
end YM.FormalOPE.RG10.MarkovChain
