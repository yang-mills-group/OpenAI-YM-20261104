import YM.FormalBulk08.Series.Level

/-!
Exponential and inverse exponential. Only used with appropriate initial coefficients.
Domain commutative ℚ algebras. Identity `shaft_expan` detects linked graphs even
with nonhomogeneous interactions depending on coarse parameters.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Series
open PowerSeries
open scoped BigOperators
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]

def expan (p : PowerSeries R) : PowerSeries R := (exp R).subst p
lemma expan_zero {p : PowerSeries R} (h : coeff 0 p=0) : coeff 0 (expan p)=1 := by simp [expan, peep h]
lemma expan_unit {p : PowerSeries R} (h : coeff 0 p=0) : IsUnit (expan p) := isUnit_iff_constantCoeff.mpr (by rw [← coeff_zero_eq_constantCoeff_apply, expan_zero h]; exact isUnit_one)
lemma map_expan (φ : R →+* S) {p : PowerSeries R} (h : coeff 0 p=0) : PowerSeries.map φ (expan p)=expan (PowerSeries.map φ p) := by
   unfold expan; simp [show PowerSeries.map φ ((exp R).subst p) = ((exp R).map φ).subst (PowerSeries.map φ p) from map_subst (h:=φ) (tribe h) _]
lemma Through.expan_congr {f g : PowerSeries R} {n : ℕ} (ht : Through n f g) (h : coeff 0 f=0) : Through n (expan f) (expan g) := (Through.exact_eq _ n).compose ht h

def tray (p : PowerSeries R) (n : ℕ) := ∑ i ∈ Finset.range (n+1), C (coeff i (exp R)) * p^i
lemma til_expan {p : PowerSeries R} (h : coeff 0 p =0) {n m : ℕ} (hm : n≤m) : Through n (expan p) (tray p m) := fun i hi => by
  unfold tray expan; simp_rw [subst_coeff h _ m i (hi.trans hm),map_sum,coeff_C_mul]

@[simp] lemma root_expan : expan (0 : PowerSeries R)=1 := by
  ext1 n
  rw [(til_expan (by simp) (le_refl n)).apex]
  simp [tray,zero_pow_eq]
lemma diff_expan_g {p : PowerSeries R} (h : coeff 0 p=0) : derivative R (expan p)= expan p * derivative R p := by unfold expan; rw [derivative_subst R (tribe h), derivative_exp]
lemma drip {p f g : PowerSeries R} (hc : coeff 0 f= coeff 0 g) (hf : derivative R f= p*f) (hg : derivative R g= p*g) : f=g := by
   ext1 i
   induction i using Nat.strong_induction_on with
   | h i ih=>
     cases i with
     | zero=> exact hc
     | succ i=>
       have he : coeff i (p*f)=coeff i (p*g) := ((Through.exact_eq p i).mul (fun k hk=> ih k (by omega))).apex
       rw [←hf,←hg,coeff_derivative,coeff_derivative,←Nat.cast_succ] at he
       refine IsUnit.mul_left_inj ?_ |>.mp he
       simpa only [map_natCast] using (((isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero i)) : IsUnit (↑(Nat.succ i):ℚ)).map (algebraMap ℚ R))
lemma expan_mul {p q : PowerSeries R} (hp : coeff 0 p=0) (hq : coeff 0 q=0) : expan p * expan q=expan (p+q) := by
   have hh : coeff 0 (p+q)=0 := by rw [map_add,hp,hq,zero_add]
   refine drip (p:= derivative R (p+q)) ?_ ?_ ?_
   · rw [expan_zero hh, coeff_zero_eq_constantCoeff_apply, map_mul,← coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply,expan_zero hp,expan_zero hq,one_mul]
   · rw [Derivation.leibniz, smul_eq_mul,smul_eq_mul,diff_expan_g hp,diff_expan_g hq,map_add]; ring
   rw [diff_expan_g hh]; ring
lemma root_one (R : Type*) [CommRing R] [Algebra ℚ R] : IsUnit (coeff 1 (exp R - 1)) := by simp

def stem (R : Type*) [CommRing R] [Algebra ℚ R] := PowerSeries.substInvOfIsUnit (exp R - 1) (root_one R)
def covelog (p : PowerSeries R) : PowerSeries R := (stem R).subst (p-1)
lemma stem_rank : coeff 0 (stem R)=0 := by rw [coeff_zero_eq_constantCoeff_apply]; simp [stem]
lemma covelog_rank {p : PowerSeries R} (hp : coeff 0 p=1) : coeff 0 (covelog p)=0 := (peep (by rw [map_sub,hp]; simp) (stem R)).trans stem_rank
lemma kick : ((exp R-1).subst (stem R))=X := PowerSeries.subst_substInvOfIsUnit_right (exp R - 1) (by simp) _
lemma slope : (stem R).subst (exp R-1)= X := PowerSeries.subst_substInvOfIsUnit_left (exp R - 1) (by simp) _
private lemma subtract_stem (p : PowerSeries R) (hp : HasSubst p) : expan p - 1 = (exp R-1).subst p := by
   unfold expan; rw [←coe_substAlgHom hp,map_sub,map_one]
lemma covelog_after {p : PowerSeries R} (hp : coeff 0 p=0) : covelog (expan p)=p := by
   unfold covelog; rw [subtract_stem p (tribe hp)]
   rw [←subst_comp_subst_apply (tribe (by simp)) (tribe hp),slope, subst_X (tribe hp)]
lemma expan_after {p : PowerSeries R} (hp : coeff 0 p=1) : expan (covelog p) = p := by
   refine sub_left_inj.mp (show expan (covelog p) - 1 = p - 1 from ?_)
   have hh : HasSubst (p-1) := tribe (by rw [map_sub,hp]; simp)
   rw [subtract_stem _ (tribe (covelog_rank hp)),covelog,←subst_comp_subst_apply (tribe stem_rank) hh,kick,subst_X hh]
lemma expan_inj {p q : PowerSeries R} (hp : coeff 0 p=0) (hq : coeff 0 q=0) : expan p = expan q ↔ p = q := ⟨fun h=> by simpa [covelog_after hp,covelog_after hq] using! (congrArg covelog h),congrArg _⟩
lemma map_covelog (φ : R →+* S) {p : PowerSeries R} (h : coeff 0 p=1) : PowerSeries.map φ (covelog p)=covelog (PowerSeries.map φ p) := by
   apply (expan_inj (by simp [covelog_rank h]) (covelog_rank (by simp [h]))).mp
   rw [←map_expan φ (covelog_rank h),expan_after h,expan_after (by simp [h])]
lemma Through.cove_congr {p q : PowerSeries R} {n : ℕ} (h : Through n p q) (hp : coeff 0 p=1) : Through n (covelog p) (covelog q) := (exact_eq _ n).compose (h.sub (exact_eq _ n)) (by rw [map_sub,hp]; simp)

section
-- Leibniz commutation for formal perturbative exp under auxiliary parameter-derivatives.
private lemma lift_factor (n : ℕ) : C (coeff (n+1) (exp R)) * ((n+1:ℕ) : PowerSeries R) = C (coeff n (exp R)) := by
   have he := congr_arg (coeff n) (derivative_exp R); rw [coeff_derivative,← Nat.cast_succ] at he
   rw [← map_natCast C, ← map_mul, he]
lemma shaft_tray (d : Derivation ℚ R R) (p : PowerSeries R) (n : ℕ) : shaft d (tray p (n+1))=tray p n * shaft d p := by
   unfold tray
   simp_rw [map_sum,Derivation.leibniz,shaft_C,show ∀ i, d (coeff i (exp R))=0 from fun i=> by rw [coeff_exp,d.map_algebraMap],map_zero, smul_zero, add_zero, Derivation.leibniz_pow, smul_eq_mul,nsmul_eq_mul]
   rw [Finset.sum_range_succ',Finset.sum_mul]; simp only [Nat.cast_zero,zero_mul,mul_zero,add_zero, Nat.add_sub_cancel]
   apply Finset.sum_congr rfl; intro i hi; rw [← lift_factor (R:=R) i]; ring
lemma shaft_expan (d : Derivation ℚ R R) (p : PowerSeries R) (hp : coeff 0 p=0) : shaft d (expan p)=expan p * shaft d p := by
   apply Through.top; intro n
   have h : Through n (shaft d (expan p)) (shaft d (tray p (n+1))) := beam_through d.toLinearMap (til_expan hp (by omega))
   rw [shaft_tray] at h; exact h.trans ((til_expan hp (le_refl n)).symm.mul (Through.exact_eq _ _))
-- apply also to MvPolynomial pderiv over coefficients via restriction
lemma shaft_expan_over {A : Type*} [CommRing A] [Algebra A R] [Algebra ℚ A] [IsScalarTower ℚ A R]
      (d : Derivation A R R) (p : PowerSeries R) (hp : coeff 0 p=0) : shaft d (expan p)=expan p * shaft d p := shaft_expan (d.restrictScalars ℚ) p hp
end
end YM.FormalBulk08.Series
