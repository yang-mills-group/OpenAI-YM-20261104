import YM.Comparison.RG02.Adjacent.Entries
/-!
# Prices, actual parameter `t` positive and `u=g/g'`

Nearest-local log comparisons can use this reset with no Taylor estimates on real g-dependent
calibration and masks. Costs formula finite rank/integration; not yet paid at increasing
coupling radii & no uniform claims. No need even for real sqrt inverse radius or consistency of
Taylor polynomial scalar at actual `u` beyond the nonnegative Re condition in `Tolls`. Uses
multiply-charge so retained divisors visible, including on actual history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
local notation "φ"=> 𝓝 (0:ℝ)
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G:Gauge}{c:Side}
namespace Receipts
open Caliber
variable (C:Caliber)(r:ℕ)

section arithmetic
variable (z : ℤ)(t u : ℝ) (ht : 0≤t)(hu:0<u)(s : ℕ)
local notation "ν"=> u^2
local notation "λ₀"=> C.tariff r t
local notation "Q"=> root (verdict C r z s) t
local notation "bp"=> u^(-z)

-- resonance budget scalar from actual β uncertainty plus clock polynomial
abbrev owes (s:ℕ)(x y:ℝ): ℂ:= ∑ i∈ range s,(x:ℂ)^i*(y:ℂ)^(s-1-i)
lemma spanned (n:ℕ)(x y:ℝ): ‖(x:ℂ)^n-(y:ℂ)^n‖= |x-y| *‖owes n x y‖ := by
   rw [← (Commute.all (x:ℂ) (y:ℂ)).mul_geom_sum₂, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,Real.norm_eq_abs]
-- depends on value Δ bounding | Ω(t)−u²| (later take t²*Δ_{ β}); ∣ρ∣ actual ratio.
def due (Δ:ℝ):= t^(s+1)*upper t s (residual C r z s)+ Δ*(‖Q‖^2*‖owes z.toNat (u^2) λ₀‖ + ‖owes (-z).toNat (u^2) λ₀‖)
local notation "P"=> Q^2

def coin (u:ℝ)(z:ℤ): ℝ:= u^(-z)*(u^2)^z.toNat
include ht hu
lemma pay0 (h:0≤ (Q).re)(Δ:ℝ)(H: |u^2-(C.tariff r t)| ≤ Δ): ‖(↑(u^(-z)):ℂ)-Q‖*coin u z ≤ due C r z t u s Δ:= by
    let L:ℝ:= bp; let p:ℂ:= Q; let m:= z.toNat; let n:= (-z).toNat
    let a:ℝ:= ν; let b:ℝ:= λ₀
    have hx:0<L:= by unfold L; exact zpow_pos hu _
    have ha:0≤a:= by unfold a; positivity
    have he : ‖(L:ℂ)-p‖*coin u z ≤ ‖p^2*(a:ℂ)^m - (a:ℂ)^n‖ := by
       have hh : L ≤ ‖(L:ℂ)+p‖ := (show L ≤ ((L:ℂ)+p).re from le_add_of_nonneg_right h).trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
       have hu' : (a:ℂ)^n=(L:ℂ)^2*(a:ℂ)^m := by exact_mod_cast (theoremTor z u hu.ne').symm
       rw [hu',← sub_mul,norm_mul,norm_pow,Complex.norm_real, Real.norm_of_nonneg ha]
       calc
         _ ≤ ‖(L:ℂ)-p‖*(‖(L:ℂ)+p‖*a^m) := by exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (pow_nonneg ha _)) (norm_nonneg _)
         _ = _ := by rw [← mul_assoc,← norm_mul, show ((L:ℂ)-p)*((L:ℂ)+p)=( (L:ℂ)^2-p^2) by ring, norm_sub_rev]
    change ‖(↑L:ℂ)-p‖*coin u z≤_
    apply he.trans
    calc _ ≤ ‖p^2*(a:ℂ)^m-p^2*(b:ℂ)^m‖+‖p^2*(b:ℂ)^m-(b:ℂ)^n‖+‖(a:ℂ)^n-(b:ℂ)^n‖ := by
          rw [norm_sub_rev ((a:ℂ)^n)]; exact (norm_sub_le_norm_sub_add_norm_sub _ ((b:ℂ)^n) _).trans (add_le_add_left (norm_sub_le_norm_sub_add_norm_sub _ _ _) _)
         _ ≤ _ := by
              rw [← mul_sub,norm_mul,norm_pow, ← show root (residual C r z s) t=p^2*(b:ℂ)^m-(b:ℂ)^n from drawn .., spanned m, spanned n]; unfold due
              -- charge positives
              let x:= |a-b|; have h':x≤ Δ:=H
              have y:= upper_cost t s (residual C r z s) ht (clot C r z s)
              change ‖p‖^2*(x*_)+_+x*_≤ _+ Δ*(‖p‖^2*‖owes m a b‖+‖owes n a b‖)
              nlinarith [mul_nonneg (sub_nonneg.mpr h') (norm_nonneg (owes m a b)),mul_nonneg (sub_nonneg.mpr h') (norm_nonneg (owes n a b)), mul_nonneg (mul_nonneg (sq_nonneg ‖p‖) (sub_nonneg.mpr h')) (norm_nonneg (owes m a b))]
end arithmetic
section performance
variable (d:ℤ)(i k:ℕ)
local notation "z"=> d+i-k
local notation "T"=> C.direct r
-- expand monomials explicitly
lemma localValue : money T d i k=ᶠ[φ] fun x:ℝ=> (x:ℂ)^i*task C r (d+i-k) x := (T).bright.mono fun x hx=>by
   unfold money task; rw [exchange d i k hx.ne']; push_cast; rfl
lemma narrow (t:ℝ)(h:i≤r): peval (motion (money T d i k)) r t= (t:ℂ)^i*peval (motion (task C r z)) (r-i) t:= by
   have ht (k':ℕ) : motion (money T d i k) k'=if i≤ k' then motion (task C r z) (k'-i) else 0:= (mgerm (localValue C r d i k)).trans (mono_price (task_ready C r z))
   unfold peval Zone.eval; rw [show r+1=i+(r-i+1) by omega, sum_range_add]
   rw [sum_eq_zero fun j hj=>?_,zero_add]; swap
   · dsimp only; rw [ht j,if_neg ((mem_range.mp hj).not_ge),smul_zero]
   rw [show (t:ℂ)^i * _= _ from Finset.mul_sum ..]; apply sum_congr rfl; intro j hj
   change t^(i+j) • motion (money (C.direct r) d i k) (i+j)=_
   rw [ht,if_pos (by omega),show i+j-i=j by omega]; simp_rw [Complex.real_smul, Complex.ofReal_pow]; rw [pow_add,mul_assoc]
def sliceFee (v t:ℝ) := (t:ℂ)^i*(tags d i k (v⁻¹):ℂ) - peval (motion (money (C.direct r) d i k)) r t
lemma calibrated_value (u t:ℝ) (H:u≠0)(h:i≤r): sliceFee C r d i k u t=(t:ℂ)^i*((↑(u^(- (d+i-k))):ℂ)- root (verdict C r (d+i-k) (r-i)) t) := by
    unfold sliceFee; rw [exchange d i k (inv_ne_zero H), narrow C r d i k t h, inv_zpow,zpow_neg, owner,mul_sub]
lemma stipend (i k:ℕ)(h:i≤r)(t u:ℝ)(ht:0≤t)(hu:0<u) (J:0≤ (root (verdict C r (d+i-k) (r-i)) t).re)(Δ)(hΔ: |u^2-C.tariff r t| ≤ Δ):
    ‖sliceFee C r d i k u t‖ ≤ t^i * (due C r (d+i-k) t u (r-i) Δ / coin u (d+i-k)):= by
    rw [calibrated_value C r d i k u t hu.ne' h, norm_mul,norm_pow, Complex.norm_real, Real.norm_of_nonneg ht]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht _); exact (le_div_iff₀ (by unfold coin; positivity)).2 (pay0 C r _ t u ht hu _ J Δ hΔ)
end performance
end Receipts
end YM.Comparison.RG02.Adjacent
