import YM.XSpace.Compat.Native
import YM.XSpace.Spume

/-!
# Rectangular analog rank: integrate the modulation before paying quadrature

Controls even reflected far images at distance comparable with the *side*, where ordinary
`O((1+|x|)/n)` is not small. Directional cube transform, no Poisson interchange.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Sail
open YM.XSpace.Compat.KP
open Filter Set Metric Function Lattice Bloch Laurent Complex MeasureTheory Further.FreeCovariance.KP
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable (A:List Axis) (n:Side)
lemma room_at (x:Cover)(p:E4): p∈room n x ↔ ∀ i:Axis,p i∈YM.XSpace.Compat.KP.slab n (x i) := by
  change ( (fun i:Axis=> ⌊p i/leap n⌋)= x ) ↔ _; simp only [funext_iff, Int.floor_eq_iff,le_div_iff₀ (leap_pos _),div_lt_iff₀ (leap_pos _),YM.XSpace.Compat.KP.slab,mem_Ico,mul_comm (leap n)]

def pure (k:ℝ) (p:ℝ):= Complex.exp (↑(p*k)*Complex.I)
lemma pure_add (k p q:ℝ): Sail.pure k (p+q)= Sail.pure k p*Sail.pure k q:=by simp only [Sail.pure,add_mul,Complex.ofReal_add,Complex.exp_add]
lemma chorus (k p:E4): song k p=∏ i, Sail.pure (k i) (p i):=by
  unfold song Sail.pure; rw [london_at,PiLp.inner_apply,← Complex.exp_sum, Complex.ofReal_sum, ← Finset.sum_mul, mul_comm, Finset.sum_mul]; simp_rw [Finset.sum_mul]; rfl

lemma width (a t k:ℝ) (ht:0<t):
    ∫ p in Ico a (a+t), Sail.pure k p= Sail.pure k a*(t * Sail.pure k (t/2)*Real.sinc (t/2*k)):=by
  let d:=t/2
  have he (r k:ℝ) : (∫ p in -r..r,Sail.pure k p)= 2*(r:ℂ)*Real.sinc (r*k):=by
    by_cases h:k=0; simp [h,Sail.pure]; ring
    unfold Sail.pure; rw [intervalIntegral.integral_comp_mul_right (fun t : ℝ=>Complex.exp ((t:ℂ)*Complex.I)) h, neg_mul,integral_exp_mul_I_eq_sinc]; have ht:(k:ℂ)≠0:=ofReal_ne_zero.mpr h; simp only [Complex.real_smul,Complex.ofReal_mul, Complex.ofReal_inv]; field_simp
  have ht' := intervalIntegral.integral_comp_add_right (a:=-d) (b:=d) (Sail.pure k) (a+d)
  rw [show -d+(a+d) = a by ring, show d+(a+d)=a+t by unfold d; ring] at ht'
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (show a≤a+t by linarith), ← ht']; simp_rw [pure_add]; rw [intervalIntegral.integral_mul_const,he]; unfold d; push_cast; ring

private def oneRank (k:ℝ):ℂ:=Sail.pure k (leap n/2)*(Real.sinc (leap n/2*k):ℂ)
def spanRank (k:E4):ℂ:= ∏ i:Axis, oneRank n (k i)
lemma light_cost (v: E4) (x: Cover): ∫ p in room n x, song v p = spanRank n v * ((leap n:ℂ)^4*song v (lit n x)):=by
  let a i := YM.XSpace.Compat.KP.slab n (x i)
  let f i:= (a i).indicator (Sail.pure (v i)); let F (p:Axis→ℝ):=∏ i:Axis, f i (p i)
  let G:= (room n x).indicator (song v)
  have hv : G=F ∘ WithLp.ofLp:=by
    funext k; by_cases h:k∈room n x
    · rw [show G k=_ from indicator_of_mem h _, chorus]; unfold F; dsimp only [comp_apply]; apply Finset.prod_congr rfl; intro i _; exact (indicator_of_mem ((room_at n x k).1 h i) _).symm
    rw [show G k=0 from indicator_of_notMem h _]; symm; obtain ⟨i,hi⟩:= not_forall.mp (mt (room_at n x k).2 h); apply Finset.prod_eq_zero (Finset.mem_univ i); exact indicator_of_notMem hi _
  have he i : ∫ p, f i p = oneRank n (v i)*((leap n:ℂ)*Sail.pure (v i) ((lit n x) i)):=by
    unfold f a YM.XSpace.Compat.KP.slab; rw [integral_indicator measurableSet_Ico,mul_add,mul_one,width _ _ _ (leap_pos n)]; unfold oneRank lit rcast; simp only [PiLp.smul_apply,smul_eq_mul]; ring
  rw [← integral_indicator (room_paid n x).1]; change (∫ p,G p)=_; rw [hv, show (∫ p:E4, (F ∘ WithLp.ofLp) p)=_ from (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp Axis).integral_comp' F, chorus]; unfold F; rw [MeasureTheory.integral_fintype_prod_volume_eq_prod f]; simp_rw [he,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl

lemma curtain_size : ∃ b:ℝ,0<b∧∀ n:Side,∀ x:E4,(∀ i:Axis, |leap n*x i|≤Real.pi) → b≤‖spanRank n x‖:=by
  obtain ⟨b,hb,H⟩:= sinc_bound; refine ⟨b^4,by positivity, fun n x hx=>?_⟩
  have he (i:Axis) : b≤‖oneRank n (x i)‖:=by
    unfold oneRank Sail.pure; rw [Complex.norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]; rw [norm_real,Real.norm_eq_abs]; refine le_trans (H _ ?_) (le_abs_self _)
    unfold earth; rw [div_mul_eq_mul_div,abs_div,abs_of_pos (show (0:ℝ)<2 from two_pos)]; linarith [hx i,Real.pi_pos]
  rw [spanRank, Complex.norm_prod, show b^4=∏ i:Axis,b by simp]; exact Finset.prod_le_prod (fun i _=> hb.le) fun i _=> he i
end YM.XSpace.Sail
