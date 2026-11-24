import YM.Comparison.RG02.Assembly.Mixed
/-!
# Exponential identification in the actual coupler-marker ring

The ungraded marked letter may already carry coupling powers from field coordinates. Commute the
real Taylor exponent calculation from `Radial` into the combined marker (at its requested
truncation) adding exactly the stipulated factorial ratios, including for exponents with a mark
of coupling grade zero. The unmarked leading stationary scalar and Hessian are not exponentiated
here (degree zero, outside the nilpotent ideal).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly
open Function Finset Filter MeasureTheory
open YM.Marker YM.Multi
open YM.Comparison.RG02.Order
open YM.PertExtension.Series
open scoped Topology BigOperators Classical ContDiff

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {U : Type*} {r : ℕ}

-- the unmarked varying scalar (log starts inside the nilpotent coupler ideal).
def realCurve (R : Census V) (u : ℕ→ℝ) : PTable R :=
    PowerSeries.map ((Poly.bead R).comp Complex.ofRealHom) (PowerSeries.mk u)
omit [Fintype V] in lemma realCoeff (u : ℕ→ℝ) (i : ℕ) :
    PowerSeries.coeff i (realCurve R u)= Poly.bead R ↑(u i) := by simp only [realCurve, PowerSeries.coeff_map,PowerSeries.coeff_mk]; rfl
omit [Fintype V] in lemma beads (x : ℂ) (s : R.Mode) : (Poly.bead R x).part s=if s=R.quiet then x else 0 := Poly.part_send ..
omit [Fintype V] in lemma real_pow_coeff (u : ℕ→U→ℝ) (x : U) (n j : ℕ) :
    PowerSeries.coeff j ((realCurve R (fun i=> u i x))^n) = Poly.bead R ↑(Zone.TaylorPow u n j x) := by
  induction n generalizing j with
  | zero=> simp only [pow_zero,PowerSeries.coeff_one,Zone.TaylorPow]; split_ifs <;> simp
  | succ n ih=>
    unfold Zone.TaylorPow Zone.mul
    rw [pow_succ,PowerSeries.coeff_mul]; simp_rw [ih, realCoeff]
    simp only [← map_mul, ← Complex.ofReal_mul,Complex.ofReal_sum,map_sum]

omit [Fintype V] in lemma real_exp_coeff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℕ→E→ℝ) (x : E) (n j : ℕ) :
    Poly.bead R ↑(Radial.expsum u n j x) = PowerSeries.coeff j (∑ i∈ range (n+1),
      (i.factorial:ℂ)⁻¹ • (realCurve R (fun i=>u i x))^i) := by
   unfold Radial.expsum; simp only [Complex.ofReal_sum,map_sum,PowerSeries.coeff_smul, real_pow_coeff,
     Complex.ofReal_mul,map_mul,Complex.ofReal_inv,Complex.ofReal_natCast,Poly.product_bead]

def scalarLog (R : Census V) (r : ℕ) (f : ℕ→ℝ) : Grade R r := series R r (realCurve R f)

theorem real_pass {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (u : ℕ→E→ℝ) (h : u 0=0) (x : E) :
    series R r (realCurve R (fun i=>Radial.expsum u i i x)) = Poly.pass (scalarLog R r (fun i=>u i x)) := by
  let n := Fintype.card (V ⊕ Fin r)
  have he (v : Index r) := (order_limit r v).trans (show r≤n by simp [n])
  suffices hp : series R r (realCurve R (fun i => Radial.expsum u i i x))=
    series R r (∑ i∈range (n+1),(i.factorial:ℂ)⁻¹ • (realCurve R (fun i=>u i x))^i) by
    unfold Poly.pass scalarLog; rw [hp,map_sum]; simp_rw [series_smul,map_pow]; rfl
  apply Join.both_parts; intro i v; rw [polarization,polarization,realCoeff,
    Radial.expsum_limit (a:=u) h (he v),real_exp_coeff]

-- Marked exponent in the ring. Use the physical marker birthday bound. Another way would
-- be `PowerSeries.subst` having nonvanishing but nilpotent constant coefficient.
def markExp (x : PTable R) := ∑ i∈range (Fintype.card V+1), (i.factorial:ℂ)⁻¹ • x^i
private lemma mark_power {x : Grade R r} (h : bottom R r x=0) (n : ℕ) (s : R.Mode) (t : Index r) (hs : s.val.card < n) :
    (x^n).part (Join.pair s t)=0 := by
  induction n generalizing s t with
  | zero => omega
  | succ n ih=>
    rw [pow_succ,Join.pair_product]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    split
    next hm=>
       by_cases h₀ : k.val.Nonempty
       · have hp : s.val.card=i.val.card + k.val.card := by rw [← hm.1.2,card_union_of_disjoint hm.1.1]
         rw [ih i j (by have hh:= Finset.card_pos.mpr h₀; omega),zero_mul]
       replace h₀ := of_not_not (mt (Cumulants.hot_iff_ne k).2 h₀)
       have he : x.part (Join.pair k l)=0 := by subst k; rw [← show _ = x.part (Join.pair R.quiet l) from (bottom_value x R.quiet l).trans (if_pos rfl),h,Poly.part_nil]
       rw [he,mul_zero]
    next=> rfl
lemma pass_horizon {x : Grade R r} (h : bottom R r x=0) :
    Poly.pass x=∑ i∈range (Fintype.card V+1), (i.factorial:ℂ)⁻¹ • x^i := by
  unfold Poly.pass; symm; refine sum_subset (range_mono ?_) (fun i _ hi=>?_)
  · simp
  simp only [mem_range, not_lt] at hi
  rw [show x^i=0 from Join.both_parts fun a b=> mark_power h i a b (by have := card_le_univ a.val; omega),smul_zero]
lemma mark_exp {x : PTable R} (h : ∀ n,(PowerSeries.coeff n x).part R.quiet=0) :
    series R r (markExp x)=Poly.pass (series R r x) := by
  unfold markExp; rw [map_sum,pass_horizon]; simp_rw [series_smul,map_pow]
  rw [bottom_map]
  rw [show PowerSeries.map (blanked R) x=0 by ext n s; simp [PowerSeries.coeff_map,pure_marks,h]]
  exact map_zero _

variable {Z : Zone U} {W : U→ℝ}
omit [Fintype V] in
lemma from_real {x : ℕ→U→ℝ} {f : ℝ→U→ℝ} (h : Z.Built W f x) :
    Zonal Z W (fun t u=>Poly.bead R ↑(f t u)) (fun u=>realCurve R (fun n=> x n u)) := by
  intro t; by_cases ht : t=R.quiet
  all_goals unfold rows; simp_rw [realCoeff, beads]
  · subst t; simpa only [if_true,↓reduceIte,Complex.ofRealCLM_apply] using built_map _ _ h Complex.ofRealCLM
  simp_rw [if_neg ht]; simpa using! Zone.Built.const (V:=W) (Z:=Z) (0:ℂ) (h.fits 0).envelope

lemma power_zonal {x : U→PTable R} {f : ℝ→U→Poly R} (h : Zonal Z 1 f x) :
    Zonal Z 1 (fun a u=>Poly.pass (f a u)) (fun u=>markExp (x u)) := by
  convert Zonal.sum (Z:=Z) (fun _=>le_rfl) (range (Fintype.card V+1)) (fun i _=> (h.pow1 i).scale (i.factorial:ℂ)⁻¹) using 1
  · rfl
  · funext t u; simp_rw [Poly.pass,Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
  exact funext fun u=> by simp_rw [markExp,Finset.sum_apply,Pi.smul_apply,Pi.pow_apply]
end YM.Comparison.RG02.Assembly
