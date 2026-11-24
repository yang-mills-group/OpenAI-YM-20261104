import YM.Integration.FVA1Physical.Wilson.MovingSources

/-! Exceptional-tag and large-link contributions for inverse couplings
which vary freely above a fixed fraction of the natural scale. Uniform
over the whole clock family and every test of the given sup norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set MeasureTheory Lattice RG YM.Wilson Tree Precision RGComparison.Core16 RGComparison.Core16.Descent
open PertExtension PertExtension.Chart PertExtension.Series.Tested
open scoped Topology Classical
variable {G : Gauge} {n c : Side} (d : Descent n c)

def clockRegion (g : ℝ) (β : ℕ → ℝ) (t : d.Tags) (J : Config G c → Fields G d → ℝ)
    (V : Config G c) (U : Set (Fields G d)) : ℝ :=
  (g^Module.finrank ℝ (Coordinates G d))⁻¹ * ∫ x in U, pathAmplitude d β t J V x ∂d.measure G

theorem clock_exterior (h : d.Room G) (Z : ChartRatio G) (hZ : LocalRatio Z) {r : ℝ}
    (hr : 0 < r) (hs : r ≤ small G Z) (B : ℝ) (hB : 0 ≤ B) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : ℝ, 0 < g →
      ∀ β : ℕ → ℝ, (∀ i ≤ d.depth, (2*g)⁻¹^2 ≤ β i) → ∀ V : Config G c, QuietLinks V ε →
      ∀ (t : d.Tags) (J : Config G c → Fields G d → ℝ), (∀ x, ‖J V x‖ ≤ B) →
        ‖clockRegion d g β t J V (chamber G d.Links r)ᶜ‖ ≤ C*g^k := by
  obtain ⟨ε,hε,H⟩ := path_exterior d h Z hZ hr hs 0 B hB
  refine ⟨ε,hε,fun k => ?_⟩
  obtain ⟨C,hC,est⟩ := H k
  let D := Module.finrank ℝ (Coordinates G d)
  refine ⟨2^(D+k)*C,by positivity,?_⟩
  intro g hg β high V quiet t J hb
  let U := (chamber G d.Links r)ᶜ
  let b := offset (0:ℕ→ℝ) (2*g)
  have ord (x : Fields G d) : d.account b t V x ≤ d.account β t V x := by
    have H' : 0 ≤ d.account (β-b) t V x := account_nonnegative d (fun i hi =>
      sub_nonneg.mpr (by simpa [b,offset] using high i hi)) t V x
    rw [account_sub] at H'
    exact sub_nonneg.mp H'
  let f := pathAmplitude d b t (fun _ _ => B) V
  have same : f = d.integrand b t (fun _ => B) V := rfl
  have total : ‖∫ x in U, pathAmplitude d β t J V x ∂d.measure G‖ ≤
      ∫ x in U, f x ∂d.measure G :=
    norm_integral_le_of_norm_le ((same.symm ▸ path_integrable (room_ok d h) b t (fun _ => B)
      continuous_const V).integrableOn) (Eventually.of_forall fun x =>
        (pathAmplitude_le d β t J V B hb x).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (ord x))) (probability_nonneg d t x)) hB))
  have rate := est (2*g) (by positivity) 0 (fun _ _ => by simp) V quiet t (fun _ _ => B)
    (fun _ => (Real.norm_of_nonneg hB).le)
  have factor : (g^D)⁻¹ = 2^D * ((2*g)^D)⁻¹ := by rw [mul_pow,mul_inv]; field_simp
  calc
    _ ≤ (g^D)⁻¹ * ∫ x in U, f x ∂d.measure G := by
      unfold clockRegion
      rw [norm_mul,Real.norm_of_nonneg (inv_nonneg.mpr (pow_nonneg hg.le _))]
      exact mul_le_mul_of_nonneg_left total (inv_nonneg.mpr (pow_nonneg hg.le _))
    _ = 2^D * pathRegion d (2*g) 0 t (fun _ _ => B) V U := by rw [factor,mul_assoc]; rfl
    _ ≤ 2^D * (C*(2*g)^k) := mul_le_mul_of_nonneg_left ((le_abs_self _).trans rate) (by positivity)
    _ = _ := by simp only [mul_pow,pow_add]; ring

end YM.Integration.FVA1Physical.Wilson
