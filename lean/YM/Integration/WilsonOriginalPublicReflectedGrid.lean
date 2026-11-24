import YM.Integration.WilsonOriginalPublicReflectedTrace

/-! A finite complex profile on the measuring grid with the uncentered
Wilson reflected form. The stochastic pullback uses the original label
at each site, including each term of the scalar source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicReflectedGrid
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Labels Cells
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {K N p : ℕ}
local notation "X" k:max => Config G (R.family.side k p)
local notation "H" => R.family.path

def pairing (K N p : ℕ) (σ : Signed) (seam : Site (R.family.side K p)) (P Q : Config G (R.family.side K p) → ℂ) :=
  ∫ U, P U * star (Q (pull σ seam U)) ∂scene (H) N p K

def wave {ι B : Type*} [Fintype ι] (w : ι → ℂ) (P : ι → B → ℂ) (U : B) :=
  ∑ i, w i * P i U

theorem matrix {ι : Type*} [Fintype ι] (live : K ≤ N) (σ : Signed)
    (seam : Site (R.family.side K p)) (w : ι → ℂ) (P : ι → X K → ℂ)
    (h : ∀i, Envelope (P i)) :
    pairing R K N p σ seam (wave w P) (wave w P) =
      ∑ i, ∑ j, (w i * star (w j)) * pairing R K N p σ seam (P i) (P j) := by
  let μ := scene (H) N p K
  letI : IsProbabilityMeasure μ := probability R.makes.wilson live
  let Q (i j : ι) (U : X K) := P i U * star (P j (pull σ seam U))
  have integrable i j : Integrable (Q i j) μ :=
    ((h i).mulC (((h j).comp_env (continuous_pull σ seam).measurable).starC)).integrableC _
  have written (U : X K) :
      wave w P U * star (wave w P (pull σ seam U)) =
        ∑ i, ∑ j, (w i * star (w j)) * Q i j U := by
    simp only [wave,star_sum,star_mul',Finset.sum_mul,Finset.mul_sum,Q]
    rw [Finset.sum_comm]
    congr 1; funext i
    apply Finset.sum_congr rfl
    intro j _; ring
  change (∫ U,wave w P U * star (wave w P (pull σ seam U)) ∂μ) =
    ∑ i, ∑ j, (w i * star (w j)) * ∫ U,Q i j U ∂μ
  simp_rw [written]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (integrable i j).const_mul _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => (integrable i j).const_mul _)]
  simp_rw [integral_const_mul]

/-- Every entry has its own site on the original K-grid. Clearance at K is
independent of the cutoff. Only the positive supports enter the actual
fine positive half. -/
theorem original {ι : Type*} [Fintype ι] (live : K ≤ N)
    (cut : Cut (R.family.side N p)) (seam : Site (R.family.side K p))
    (matched : anchor R.family.S p live seam = cut.slide) (r : ℕ)
    (x : ι → Site (R.family.side K p)) (P : ι → X K → ℂ)
    (localP : ∀ i, Interior (window (x i) r) (P i))
    (far : ∀ i j, 2*muzzle (H).levels K r < separation (x i) (affine cut.flip seam (x j)))
    (half : ∀i, window (anchor R.family.S p live (x i)) (grows (H).levels K r live) ⊆ cut.sector)
    (w : ι → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (self : ∀i, ‖pairing R K N p cut.flip seam (P i) (P i)‖ ≤ b) :
    ‖pairing R K N p cut.flip seam (wave w P) (wave w P)‖ ≤ (∑i, ‖w i‖)^2 * b := by
  let T (i : ι) := backTo (H) N p live (P i)
  let β := R.family.beta N p
  have hot : 0 < β := Overlay.beta_positive R.makes.wilson (m:=N) (N:=N) (p:=p) le_rfl
  have earned i : Interior cut.sector (T i) :=
    (OPE.Strobe.locale (A:=H) (N:=N) (p:=p) (x i) r (localP i) live).enlarges (half i)
  have read i j : pairing R K N p cut.flip seam (P i) (P j) = Cells.form β cut (T i) (T j) :=
    WilsonOriginalPublicReflectedTrace.original R live cut seam (x i) (x j) matched r (localP i) (localP j) (far i j)
  have cross i j : ‖pairing R K N p cut.flip seam (P i) (P j)‖ ≤ b := by
    have cs := Cells.cauchy (Slice.reflected_positive cut β hot.le) (earned i) (earned j)
    rw [← read i j,← read i i,← read j j] at cs
    apply (sq_le_sq₀ (norm_nonneg _) hb).mp
    exact cs.trans (by rw [sq]; exact mul_le_mul (self i) (self j) (norm_nonneg _) hb)
  rw [matrix R live cut.flip seam w P (fun i => cylinder_env (localP i))]
  calc
    _ ≤ ∑ i, ∑ j, ‖(w i * star (w j)) * pairing R K N p cut.flip seam (P i) (P j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, (‖w i‖ * ‖w j‖) * b := by
      apply Finset.sum_le_sum; intro i _
      apply Finset.sum_le_sum; intro j _
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul_of_nonneg_left (cross i j) (by positivity)
    _ = _ := by simp_rw [← Finset.sum_mul,← Finset.mul_sum]; rw [← Finset.sum_mul,pow_two]

end YM.Integration.WilsonOriginalPublicReflectedGrid

