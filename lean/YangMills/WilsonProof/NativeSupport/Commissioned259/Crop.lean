import YangMills.WilsonProof.NativeSupport.Commissioned259.Row

/-! # Crop versus evaluation of separately cropped series at the **measured t**.

All terms with total degree higher than the crop are factored BEFORE taking any estimate,
so no division (in particular none by the measured coupling or by T-dependent norms). This
calculation deals with t varying, even though the original definition of the operation on
series has T fixed. Inputs: the bounds *at each of the same orders*, t in unit interval.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries
open scoped Topology BigOperators Classical
open FVA2.Scale O.Score O.Enh

section Triangle
variable (p : ℕ) (t : ℝ) (f g : PowerSeries ℂ)

def excess (p : ℕ) : Finset (ℕ×ℕ) := ((Finset.range (p+1)) ×ˢ (Finset.range (p+1))).filter fun z => p < z.1+z.2

def debt : ℂ := ∑ z ∈ excess p,
    (t:ℂ)^(z.1+z.2-(p+1)) * (coeff z.1 f * coeff z.2 g)

/-- Rectangle minus triangle in the crop. -/
lemma triangle : crop p t f * crop p t g = crop p t (f*g) + (t:ℂ)^(p+1) * debt p t f g := by
  let R := Finset.range (p+1)
  let pay (z : ℕ×ℕ) := (t:ℂ)^(z.1+z.2) * (coeff z.1 f * coeff z.2 g)
  let low : Finset (ℕ×ℕ) := (R ×ˢ R).filter (fun z=> ¬ p < z.1+z.2)
  have hits : low = R.biUnion Finset.HasAntidiagonal.antidiagonal := by
    ext ⟨i,j⟩
    simp only [R,low,Finset.mem_range,Finset.mem_filter,Finset.mem_product,
      Finset.mem_biUnion,Finset.HasAntidiagonal.mem_antidiagonal]
    constructor
    · intro h; exact ⟨i+j,by omega,rfl⟩
    · rintro ⟨k,h,rfl⟩; omega
  have dis : (R : Set ℕ).PairwiseDisjoint (fun k => Finset.HasAntidiagonal.antidiagonal k) := by
    rintro i _ j _ h; exact Finset.disjoint_left.mpr (fun z hi hj =>
      h ((Finset.HasAntidiagonal.mem_antidiagonal.mp hi).symm.trans (Finset.HasAntidiagonal.mem_antidiagonal.mp hj)))
  have lower : crop p t (f*g) = ∑ z ∈ low, pay z := by
    rw [hits, Finset.sum_biUnion dis,crop_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl fun z hz=> by dsimp only [pay]; rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hz]
  have abs : crop p t f * crop p t g = ∑ z ∈ R ×ˢ R, pay z := by
    rw [crop_apply,crop_apply,Finset.sum_mul_sum,Finset.sum_product]
    exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by dsimp only [pay]; rw [pow_add]; ring
  have higher : (t:ℂ)^(p+1) * debt p t f g = ∑ z ∈ excess p,pay z := by
    rw [debt,Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz=>?_ ; replace hz : p < z.1+z.2 := (Finset.mem_filter.mp hz).2
    dsimp only [pay]; rw [←mul_assoc,←pow_add,show p+1+(z.1+z.2-(p+1)) = z.1+z.2 by omega]
  rw [lower,abs,higher,add_comm]
  exact Eq.symm (Finset.sum_filter_add_sum_filter_not ..)
end Triangle

section Price
variable {I : Type} {F Q : I → ℝ → PowerSeries ℂ} {w : ℝ} (p : ℕ)
    {t : I → ℝ} (ht : ∀ i, |t i| ≤ 1)
include ht

lemma rain_crop (hf : ChargeP (p+1) w F) : Rain w (fun i s => crop p (t i) (F i s)) := by
  have h0 : Rain 0 (fun (i : I) (_ : ℝ) => ((t i):ℂ)) := Rain.cash ⟨1,fun i=>
    (Complex.norm_real (t i)).trans_le ((Real.norm_eq_abs (t i)).trans_le (ht i))⟩
  simp_rw [crop_apply]
  exact Rain.sum _ fun i hi => Rain.cover (h0.powers i) (hf i (Finset.mem_range.mp hi))

lemma rain_debt (hf : ∀ j ≤ p, ∃ C : ℝ, ∀ i s, ‖coeff j (F i s)‖ ≤ C) (hq : ChargeP (p+1) w Q) :
    Rain w (fun i s => debt p (t i) (F i s) (Q i s)) := by
  unfold debt
  refine Rain.sum _ fun z (hz : z ∈ excess p) => ?_
  have h0 : Rain 0 (fun (i : I) (_ : ℝ) => ((t i):ℂ)) := Rain.cash ⟨1,fun i=>
    (Complex.norm_real (t i)).trans_le ((Real.norm_eq_abs (t i)).trans_le (ht i))⟩
  obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hz).1
  refine Rain.cover (h0.powers _) (Rain.cover ?_ (hq z.2 (Finset.mem_range.mp hz2)))
  obtain ⟨D,h⟩ := hf z.1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hz1))
  exact ⟨ max D 1, lt_max_of_lt_right zero_lt_one, 0, Eventually.of_forall fun s i=> by
    simp only [post,neg_zero,zero_mul,Real.exp_zero,pow_zero,mul_one]
    exact (h i s).trans (le_max_left ..) ⟩
end Price
end YM.FVA2.GradedFar259
