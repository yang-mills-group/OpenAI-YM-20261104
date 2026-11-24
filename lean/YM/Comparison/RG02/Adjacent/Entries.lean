import YM.Comparison.RG02.Adjacent.Attached
/-!
# Scalar clock prices without applying a real-program derivative on a beta disk

Forward regular program at prescribed powers uses ω/reset from same formal convention. To
pay its rank basis truncation error at the ENTRY value, it suffices to fund these finite-order
polynomial coefficients, the actual ratio bounds, and kinetic uncertainty (NO radius of `back`
inverse function or `sqrt` assertion ANYWHERE except for identifying the prescription germ).
Analytic torch isn't marched from a halo into sampled histories to justify it as real β.
Restrictions all at fixed `t`, `C`, `L` and reserves yet to be bound for volume/scale costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G:Gauge}{c:Side}
namespace Receipts
open Caliber Polynomial
local notation "φ"=> 𝓝 (0:ℝ)
variable (C:Caliber)(r:ℕ)(z:ℤ)

abbrev tall (z:ℤ):= z.toNat
abbrev short (z:ℤ):= (-z).toNat
abbrev task (t:ℝ): ℂ:= ((C.direct r).rating t:ℂ)^z
lemma task_ready : ContDiffAt ℝ ω (task C r z) 0:= by unfold task; simp_rw [← Complex.ofReal_zpow]; exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((C.direct r).spin z)
lemma theoremTor (u :ℝ) (h : u ≠0) : ((u^(-z))^2) * (u^2)^z.toNat=(u^2)^(-z).toNat:= by
   cases z with
   | ofNat n => rw [Int.ofNat_eq_natCast,zpow_neg,zpow_natCast]; simp only [Int.toNat_natCast,Int.toNat_neg_natCast,pow_zero]; rw [pow_right_comm u 2 n, inv_pow,inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ h))]
   | negSucc n => simp only [Int.neg_negSucc,zpow_natCast,Int.toNat_natCast,Int.toNat_negSucc,pow_zero,mul_one]; exact pow_right_comm u (n+1) 2
lemma sentry : (fun t:ℝ=> task C r z t ^ 2 * (C.tariff r t:ℂ)^z.toNat)=ᶠ[φ] fun t=> (C.tariff r t:ℂ)^(-z).toNat:= by
   filter_upwards [C.rates r,(C.direct r).bright] with t ht he
   have hh:= theoremTor z _ (inv_ne_zero he.ne'); rw [C.income r t ht.le, inv_zpow, zpow_neg, inv_inv] at hh
   exact_mod_cast hh

-- keep the polynomial residual with known low cancellations, compare REAL side separately
private lemma begged {f g:ℝ→ℂ} {r:ℕ} (h:Shadow r f g) (k:ℕ) : Shadow r (fun t=> f t^k) (fun t=> g t^k):= by induction k with
  | zero=> simp_rw [pow_zero]; exact Shadow.refl contDiffAt_const
  | succ k ih=> simp_rw [pow_succ]; exact ih.product h

def vault (s:ℕ)(p:ℕ→ℂ): Polynomial ℂ := PowerSeries.trunc (s+1) (PowerSeries.mk p)
def tithes:= vault r (fun i=> (C.measure i:ℂ))
def verdict (s:ℕ): Polynomial ℂ:= vault s (motion (task C r z))
def residual (s:ℕ): Polynomial ℂ:= (verdict C r z s)^2 * (tithes C r)^z.toNat - (tithes C r)^(-z).toNat
variable (t:ℝ)
local notation "q"=> ((t:ℝ):ℂ)
def root (p : Polynomial ℂ)(t:ℝ) := p.eval (t:ℂ)
lemma atomic (s:ℕ) (p:ℕ→ℂ): root (vault s p) t= peval p s t:= by
   unfold root Polynomial.eval vault peval Zone.eval; rw [PowerSeries.eval₂_trunc_eq_sum_range]; simp_rw [RingHom.id_apply,PowerSeries.coeff_mk,Complex.real_smul,Complex.ofReal_pow]; apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _
lemma talks : root (tithes C r) t=C.tariff r t := by rw [tithes,atomic]; unfold tariff peval Zone.eval; simp only [Complex.real_smul,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_pow]
lemma owner (s:ℕ) : root (verdict C r z s) t=peval (motion (task C r z)) s t:= atomic ..
lemma drawn (s:ℕ) : root (residual C r z s) t = root (verdict C r z s) t^2 * (C.tariff r t:ℂ)^z.toNat - (C.tariff r t:ℂ)^(-z).toNat:= by simp_rw [← talks,root,residual, Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow]

lemma poly_known (p:Polynomial ℂ)(i:ℕ): motion (root p) i=p.coeff i:= by
   classical
   rw [show root p=(fun t:ℝ=> ∑ j∈p.support, (t:ℂ)^j * p.coeff j) from funext fun t=> by unfold root; rw [Polynomial.eval_eq_sum]; unfold Polynomial.sum; exact Finset.sum_congr rfl fun i _=> mul_comm ..]
   let f j (t:ℝ) := (t:ℂ)^j*p.coeff j; have hu(j:ℕ):ContDiffAt ℝ ω (f j) 0:= (Complex.ofRealCLM.contDiff.contDiffAt.pow _).mul contDiffAt_const
   rw [msum _ f fun i _=> hu i,sum_eq_single i]
   · unfold f; rw [MotionMon p i]
   · intro b hb he; unfold f; change motion (f b) i=0
     exact (recipeMon p b i).trans (if_neg he)
   intro hi; rw [recipeMon p,if_pos rfl]; exact notMem_support_iff.mp hi
where
 recipeMon (p:Polynomial ℂ) (i j:ℕ): motion (fun t:ℝ=> (t:ℂ)^i * p.coeff i) j=if i=j then p.coeff i else 0 := by rw [mono_price (f:=fun _=>p.coeff i) contDiffAt_const, mconst]; split_ifs<;> first|rfl|omega
 MotionMon (p:Polynomial ℂ) (i:ℕ): motion (fun t:ℝ=> (t:ℂ)^i * p.coeff i) i=p.coeff i := (recipeMon p i i).trans (if_pos rfl)
lemma clot (s i:ℕ)(h:i≤ s): Polynomial.coeff (residual C r z s) i=0:= by
   let p := task C r z; let Q:= root (verdict C r z s); let f (x:ℝ):= (C.tariff r x:ℂ)
   have hc : Shadow s p Q:= by unfold Q; rw [funext (fun t=> owner C r z t s)]; exact Shadow.truncate s (task_ready C r z)
   have hF:ContDiffAt ℝ ω f 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((C.smooth r).contDiffAt)
   let L(x:ℝ):= p x^2*f x^z.toNat; let V(x:ℝ):= f x^(-z).toNat
   have he: Shadow s L (fun x=> Q x^2*f x^z.toNat):=(begged hc 2).product (begged (Shadow.refl hF) _)
   have S: Shadow s L V:= Shadow.same (sentry C r z) he.left
   rw [← poly_known, funext (fun x=> drawn C r z x s)]
   change motion (fun x=> Q x^2*f x^z.toNat-V x) i=0; simp_rw [sub_eq_add_neg]
   rw [show motion (fun x=> Q x^2*f x^z.toNat + -V x) i= _ from madd he.right (S.right.neg), show motion (fun x=> -V x) i= -motion V i from by rw [show (fun x=> -V x)=(fun x=> (-1:ℂ)*V x) from by funext x; rw [neg_one_mul], mscale _ S.right,neg_one_mul], ← he.aligns i h, S.aligns i h,add_neg_cancel]

def upper (s:ℕ)(p:Polynomial ℂ) := ∑ i∈p.support,t^(i-(s+1))*‖p.coeff i‖
lemma upper_cost (s:ℕ)(p:Polynomial ℂ) (hh:0≤t)(hv:∀i≤ s,p.coeff i=0): ‖root p t‖ ≤ t^(s+1)*upper t s p:= by
   unfold root upper; rw [Polynomial.eval_eq_sum, Finset.mul_sum]; unfold Polynomial.sum
   refine (norm_sum_le ..).trans (le_of_eq (sum_congr rfl fun i hi=>?_))
   have hi' : s+1≤ i:= Nat.lt_of_not_ge (fun hx=> mem_support_iff.mp hi (hv i hx))
   rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hh,mul_comm ‖_‖,← mul_assoc,← pow_add, show s+1 + (i-(s+1))=i by omega]
end Receipts
end YM.Comparison.RG02.Adjacent
