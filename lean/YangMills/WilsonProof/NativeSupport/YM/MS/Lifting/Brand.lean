import YM.MS.Lifting.Brand
import YangMills.WilsonProof.NativeSupport.YM.MS.Lifting.Letters
/-!
# True singlet lifting without finite normal-form choices

The real moment obtained by averaging in a fixed-rank tensor power of Ad(G)
is used on every representation of the monomial family. Depends on outputs
of all momenta and orientations, not just invariant contractions with δμν.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Lifting
open Function Filter Set Finset Plane Koszul Color Real Momentum Wire Tensor Book
open Local Local.BV Landau Detect Detect.Mark MeasureTheory
open Complex (I)
open scoped Topology ContDiff BigOperators
variable {G:Gauge}{n:ℕ}
-- Real ink
lemma wcprod (c:G.El)(r s:Grid G n):(ink c r s:ℂ)=∏ i,wc c (r i) (s i):= by simp [ink,wc]
lemma ink_group (j k:G.El)(i m:Grid G n): ink (j*k) i m =∑ l:Grid G n, ink k i l*ink j l m:= by simp only [ink,weight_group, Fintype.prod_sum,← Finset.prod_mul_distrib]

lemma paysInk (c:G.El)(r s:Grid G n) : (∑ k:Grid G n, ink c r k * group G k s)= group G r s:= by
   have hf k: Integrable (fun u=> ink c r k*ink u k s) G.probHaar:= (massInk k s).const_mul _
   simp_rw [group, ← integral_const_mul]; rw [← integral_finsetSum _ (fun i _=> hf i)] -- fix
   simp_rw [← ink_group]; exact integral_mul_right_eq_self (fun u=>ink u r s) c
variable {E R : Type*} [CommRing R][Algebra ℝ R][AddCommGroup E][Module R E] -- R=ℂ ℝ generic
lemma cash {P:E→ₗ[R] E} (F: Grid G n→ E)(u:G.El) (H:∀ (i:Grid G n), P (F i)=∑ k:Grid G n, (algebraMap ℝ R (ink u k i)) • F k)(i:Grid G n): P (∑ k:Grid G n,(algebraMap ℝ R (group G k i)) • F k)=∑ k:Grid G n, (algebraMap ℝ R (group G k i)) • F k:= by
   simp_rw [map_sum,map_smul,H,Finset.smul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun j _=>?_); simp_rw [smul_smul,←map_mul, mul_comm (group G _ _),← Finset.sum_smul,← map_sum,paysInk]
variable (R)
variable {R}
end YM.MS.Lifting
