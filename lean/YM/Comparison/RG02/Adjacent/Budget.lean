import YM.Comparison.RG02.Adjacent.Tolls
/-!
# Payment at finite OLD scale (t) through re-expression to the NEW protocol (y),
    charge in the NEW rank basis to align further density representation.

Here compute in the correct direction. `sliceFee` bound on old polynomial peval, operator
FDeriv estimates on constructor p etc. handed as price. Includes cost of measured mismatch &
Q positivity, not inferred. This exact conversion for log-ranks (and also full by records) at
same coordinates in finite regulator. Masks/reclosure remain to be supplied after conversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
local notation "φ"=> 𝓝 (0:ℝ)
variable {G:Gauge}{c:Side}
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
namespace Debited
open Caliber
open Receipts (sliceFee coin due verdict root)
variable {p:Display X} {m:ℕ→ℤ}
    (C:Caliber)(r:ℕ)(d:ℤ)(w t:ℝ)
local notation "L"=> C.back r
local notation "q"=> born p (C.back r) d r
local notation "α"=> C.direct r
local notation "z"=> t/w
variable (hp:Charge r m p) (hm : Monotone m) (hw:0<w)
include hp hm
lemma from_terms (x:X) : ages q d r t w⁻¹ x-cover p r t x=∑ i∈range (r+1),∑ k∈range ((m i).toNat+1), sliceFee C r d i k w t*Assembly.jet (q i) k x:= by
   let h:=(affordable d r hp (C.back r) hm)
   have he:cover p r t x=cover (born q (C.direct r) d r) r t x:= (sum_congr rfl fun i (hi:i∈range (r+1))=> congrArg (fun s:X→ℂ=> (t:ℂ)^i*s x) (Adjacent.reverse d r hp (C.forward_back r).symm i (mem_range_succ_iff.mp hi)).symm)
   rw [he, reference (C.direct r) d r h,quoted d r h, ← sum_sub_distrib]; simp_rw [← sum_sub_distrib, sliceFee, sub_mul]
include hw
def reprice (i k:ℕ):ℂ:= (↑(w^d):ℂ)*(w:ℂ)⁻¹^k * sliceFee C r d i k w t
lemma now (x:X): cover q r z x- ages p d r z w x= ∑ i∈range (r+1), ∑ k∈range ((m i).toNat+1), reprice C r d w t i k * Assembly.jet (q i) k x:= by
    let v:= w⁻¹ • x
    have he : cover q r z x- ages p d r z w x=(↑(w^d):ℂ)*(ages q d r t w⁻¹ v-cover p r t v):= by unfold v ages; rw [smul_smul,inv_inv,mul_inv_cancel₀ hw.ne',one_smul,inv_zpow,mul_sub,div_mul_cancel₀ t hw.ne',← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (zpow_ne_zero _ hw.ne'), Complex.ofReal_one,one_mul,div_eq_mul_inv]
    rw [he, from_terms C r d w t hp hm]; unfold v; simp_rw [Clipper.weight,mul_sum]; apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; unfold reprice; rw [Complex.real_smul]; push_cast; ring

omit hp hm
-- optional cost interpreter: caller can use exact toll instead of this high bound
section performance
include hp hm
variable (ht:0≤t)(Δβ:ℝ) (he: abs (w^2-C.tariff r t) ≤ t^2*Δβ) (hx:∀i≤r,∀k≤(m i).toNat, 0≤ (root (verdict C r (d+i-k) (r-i)) t).re)
include ht he hx
def debit (Δβ:ℝ) (i k:ℕ) := w^d*(w⁻¹)^k * (t^i * (due C r (d+i-k) t w (r-i) (t^2*Δβ) / coin w (d+i-k)))
omit hp hm in
lemma reprice_bound (i k:ℕ)(hi:i≤r)(hk:k≤ (m i).toNat): ‖reprice C r d w t i k‖ ≤ debit C r d w t Δβ i k := by
    unfold reprice debit; rw [norm_mul,norm_mul,norm_pow,norm_inv, Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hw.le, Real.norm_of_nonneg (zpow_pos hw _).le]; gcongr; exact Receipts.stipend C r d i k hi t w ht hw (hx _ hi _ hk) (t^2*Δβ) he -- fix first norm rewrites order
-- bound exact rank-angular function reset error and derivatives in all x, not ring prices
omit ht he hx in
lemma turns (x:X)(j:ℕ): iteratedFDeriv ℝ j (cover q r z - ages p d r z w) x=∑ i∈range (r+1), ∑ k∈range ((m i).toNat+1), reprice C r d w t i k • iteratedFDeriv ℝ j (Assembly.jet (q i) k) x := by
    let f (i k:ℕ)(x:X):= reprice C r d w t i k*Assembly.jet (q i) k x
    have hs (i k:ℕ) (he:i∈range (r+1)) : ContDiff ℝ ω (Assembly.jet (q i) k):= (levelJet (affordable d r hp (C.back r) hm i (mem_range_succ_iff.mp he)).smooth.contDiffAt k).smooth
    have hf i k (he:i∈range (r+1)): ContDiffAt ℝ j (f i k) x:= contDiffAt_const.mul ((hs i k he).contDiffAt.of_le le_top)
    rw [show cover q r z - _=(fun x=> ∑ i∈range (r+1),∑ k∈range ((m i).toNat+1),f i k x) from funext (now C r d w t hp hm hw),iteratedFDeriv_fun_sum_apply (fun i hi=> ContDiffAt.sum fun k _=> hf i k hi)]; apply sum_congr rfl; intro i hi; rw [iteratedFDeriv_fun_sum_apply (fun k _=> hf i k hi)]; exact sum_congr rfl fun k _=> iteratedFDeriv_const_smul_apply' (a:=reprice C r d w t i k) ((hs i k hi).contDiffAt.of_le le_top)
lemma booking (x:X)(j:ℕ) (y:Fin j→X): ‖iteratedFDeriv ℝ j (cover q r z- ages p d r z w) x y‖ ≤ ∑ i∈range (r+1), ∑ k∈range ((m i).toNat+1), debit C r d w t Δβ i k * ‖iteratedFDeriv ℝ j (Assembly.jet (q i) k) x y‖:= by
   rw [turns C r d w t hp hm hw x j]; simp_rw [_root_.sum_apply, _root_.smul_apply]; refine (norm_sum_le ..).trans (sum_le_sum fun i hi=> (norm_sum_le ..).trans (sum_le_sum fun k hk=>?_)); rw [norm_smul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact reprice_bound C r d w t hw ht Δβ he hx i k (mem_range_succ_iff.mp hi) (mem_range_succ_iff.mp hk)
-- operator norm (may cost huge if used globally)
lemma book_op (x:X)(j:ℕ): ‖iteratedFDeriv ℝ j (cover q r z- ages p d r z w) x‖ ≤ ∑ i∈range (r+1), ∑ k∈range ((m i).toNat+1), debit C r d w t Δβ i k * ‖iteratedFDeriv ℝ j (Assembly.jet (q i) k) x‖:= by
   rw [turns C r d w t hp hm hw x j]; refine (norm_sum_le ..).trans (sum_le_sum fun i hi=> (norm_sum_le ..).trans (sum_le_sum fun k hk=>?_)); rw [norm_smul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); exact reprice_bound C r d w t hw ht Δβ he hx i k (mem_range_succ_iff.mp hi) (mem_range_succ_iff.mp hk)
end performance
end Debited
end YM.Comparison.RG02.Adjacent
