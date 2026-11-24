import YM.Integration.OPETreeSupport

/-! The normalized MS tree remainder after smearing the complete cluster
with a complex compactly supported smooth function of all its relative
coordinates. The weight functions are the individual derivatives of the
same normalized Gaussian, and so are integrable on the entire test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OPETreeTests
open Function Set Filter Asymptotics MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open FVA2 Pert.Position RG11.Fields RG11.Neighborhood MSbar.OPE OPETreeRemainder OPETreeKernel OPETreeSupport
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} {n m i d : ℕ}

theorem on_support (f : Test n) {a b : Points n → ℂ} (h : ∀ x ∈ tsupport f, a x = b x) :
    f.applyTo a = f.applyTo b := by
  apply integral_congr_ae
  apply ae_of_all
  intro x
  change f x * a x = f x * b x
  by_cases hx : x ∈ tsupport f
  · rw [h x hx]
  rw [image_eq_zero_of_notMem_tsupport hx,zero_mul,zero_mul]

theorem integrable (f : Test n) {a : Points n → ℂ}
    (ha : ∀ x ∈ tsupport f, ContinuousAt a x) :
    Integrable (fun x => f x*a x) := by
  refine Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.mpr
    (fun x => ?_)) f.hasCompactSupport.mul_right
  by_cases hx : x ∈ tsupport f
  · exact f.continuous.continuousAt.mul (ha x hx)
  apply continuousAt_const.congr (f := fun _ : Points n => (0:ℂ))
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with z hz
  simp [hz]

theorem scalar (f : Test n) (c : ℂ) (a : Points n → ℂ) :
    f.applyTo (fun x => c*a x) = c*f.applyTo a := by
  unfold Test.applyTo
  simp_rw [mul_left_comm _ c,integral_const_mul]

theorem sum (f : Test n) {ι : Type*} (s : Finset ι) (a : ι → Points n → ℂ)
    (ha : ∀ j ∈ s, ∀ x ∈ tsupport f, ContinuousAt (a j) x) :
    f.applyTo (fun x => ∑ j ∈ s,a j x) = ∑ j ∈ s,f.applyTo (a j) := by
  unfold Test.applyTo
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s (fun j hj => integrable f (ha j hj))

theorem difference (f : Test n) (a b : Points n → ℂ)
    (ha : ∀ x ∈ tsupport f, ContinuousAt a x) (hb : ∀ x ∈ tsupport f, ContinuousAt b x) :
    f.applyTo (fun x => a x-b x) = f.applyTo a-f.applyTo b := by
  unfold Test.applyTo
  simp_rw [mul_sub]
  exact integral_sub (integrable f ha) (integrable f hb)

theorem bound (f : Test n) (a : Points n → ℂ) (B : ℝ)
    (h : ∀ x ∈ tsupport f, ‖a x‖ ≤ B) : ‖f.applyTo a‖ ≤ (∫ x,‖f x‖)*B := by
  unfold Test.applyTo
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le
    ((f.continuous.norm.integrable_of_hasCompactSupport f.hasCompactSupport.norm).mul_const _)
    (ae_of_all _ fun x => ?_)
  by_cases hx : f x = 0
  · simp [hx]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h x (subset_closure (Function.mem_support.mpr hx))) (norm_nonneg _)

variable (V : Warehouse G) {Q : MS.Land.Booked (FVA2.ColorCode.wings G)}
    (M : MS.Land.MS_Data G Q) (μ : ℝ) (v : Fin n → E V.F i) (w : Fin m → E V.F d)
    (weights : Fin n → ℕ) (hv : ∀ a, pureW scaleW (weights a) (polynomials V.F i v a))
include hv

theorem integrated_remainder (f : Test n) (y : Tail m) (H : ℕ) :
    (fun r : ℝ => (r:ℂ)^(∑ a,weights a) * f.applyTo (fun x => paired V M μ 0 (driven r x y) v w) -
      ∑ k ∈ Finset.range (H+1), (r:ℂ)^k *
        f.applyTo (tested y (polynomials V.F i v) (polynomials V.F d w) k))
      =O[𝓝[>] 0] (fun r : ℝ => r^(H+1)) := by
  let p := polynomials V.F i v
  let q := polynomials V.F d w
  let a := kernel y p q
  let b := tested y p q
  obtain ⟨B,_,hB⟩ := kernel_bound (tsupport f) f.hasCompactSupport f.tsupport_subset y p q H
  apply IsBigO.of_bound ((∫ x, ‖f x‖)*B)
  filter_upwards [hB,self_mem_nhdsWithin] with r hr hp
  have hp' : 0 < r := hp
  have hfront : (r:ℂ)^(∑ j,weights j) * f.applyTo (fun x => paired V M μ 0 (driven r x y) v w) =
      f.applyTo (fun x => a (r,x)) := by
    rw [← scalar]
    apply on_support f
    intro x hx
    exact normalized V M μ ⟨x,f.tsupport_subset hx⟩ y v w weights hv r hp' (hr x hx).1.2
  have hb (k : ℕ) (x : Points n) (hx : x ∈ tsupport f) : ContinuousAt (b k) x :=
    (tested_smooth y p q k (f.tsupport_subset hx)).continuousAt
  let term := fun k x => (r:ℂ)^k*b k x
  have ht (k : ℕ) (x : Points n) (hx : x ∈ tsupport f) : ContinuousAt (term k) x :=
    continuousAt_const.mul (hb k x hx)
  let total := fun x => ∑ k ∈ Finset.range (H+1), term k x
  have hsum : f.applyTo total = ∑ k ∈ Finset.range (H+1), (r:ℂ)^k*f.applyTo (b k) := by
    rw [sum f _ term (fun k _ => ht k)]
    simp only [term,scalar]
  have hd : f.applyTo (fun x => a (r,x)-total x) =
      f.applyTo (fun x => a (r,x))-f.applyTo total := by
    apply difference f
    · intro x hx
      exact ((smooth_at y p q (r,x) (f.tsupport_subset hx) (hr x hx).1.2).continuousAt).comp
        (continuousAt_const.prodMk continuousAt_id)
    intro x hx
    have smooth (k : ℕ) : ContDiffAt ℝ ∞ (term k) x :=
      contDiffAt_const.mul (tested_smooth y p q k (f.tsupport_subset hx))
    exact (ContDiffAt.sum (s := Finset.range (H+1)) (fun k _ => smooth k)).continuousAt
  change ‖(r:ℂ)^_ * f.applyTo _ - ∑ k ∈ Finset.range (H+1), (r:ℂ)^k*f.applyTo (b k)‖ ≤ _
  rw [hfront,← hsum,← hd,Real.norm_of_nonneg (pow_nonneg hp'.le _)]
  have he := bound f (fun x => a (r,x)-total x) (B*r^(H+1)) (fun x hx => (hr x hx).2)
  simpa only [mul_assoc] using he

end YM.Integration.OPETreeTests
