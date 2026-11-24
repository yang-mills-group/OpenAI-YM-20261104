import YM.RGComparison.Core16.Grade
import YM.PertExtension.GaussianIBP

/-!
# Conditional diagrams at the finite lattice (actual RG kernel)

Use for computing/comparing the coefficients. *All* links of the finite chain and
*full* quadratic including normalized Wilson Markov kernel's quadratic. The gauge-tree picks can
be arbitrary here, one and the same across the operations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Precision Push.BetaTransport
open Function Filter MeasureTheory Set Metric
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial GaussianScore
variable {G : Gauge} {n c : Side} (d : Descent n c) (t u : d.Tags) (P : ChartRatio G)
local notation "E" => Coordinates G d

/-- No choice of a translation-invariant Gaussian assumed -- read the true quadratic jet at flat.
Expansion coefficients have chosen to assemble a single joint Gaussian rather than distributing
on the individual intermediate steps. This definition ignores no intermediate Hessians. -/
def quadratic (G : Gauge) (d : Descent n c) (t : d.Tags) : Coordinates G d →ₗ[ℝ] Module.Dual ℝ (Coordinates G d) where
  toFun x := ((fderiv ℝ (fderiv ℝ (d.phase G t)) 0 x)).toLinearMap
  map_add' x y := by simp
  map_smul' r x := by simp

lemma half (x : E) : jet (d.phase G t) 2 x = quadratic G d t x x / 2 := by
  unfold jet quadratic; rw [iteratedFDeriv_two_apply]; dsimp; ring

variable {d}

def ambient (h : d.Room G) : Law E where
  P := quadratic G d t
  turns x y := ((account_smooth (room_ok d h) t 1)).isSymmSndFDerivAt_of_omega.eq ..
  slope := by simp_rw [← half]; exact ⟨(1+d.edgeBill G)⁻¹^2, by have := edgeBill_nonneg G d; positivity,coercive_charge t h⟩
  smooth := by
    have hp : Continuous (fun x => quadratic G d t x x / 2) := by simp_rw [← half]; exact Smooth.continuousJet ..
    have hf (x : E) : 2*(quadratic G d t x x/2) = quadratic G d t x x := by ring
    change Continuous (fun x : E => quadratic G d t x x)
    convert! hp.const_mul (2:ℝ) using 1; exact (funext hf).symm

lemma kern_is (h : d.Room G) : Radial.kernel (d.phase G t) = (ambient t h).kern := by
  ext x; unfold ambient Law.kern Radial.kernel; dsimp; rw [half]; ring_nf

lemma quadratic_independent (h : d.Room G) : quadratic G d t=quadratic G d u := by
  -- symmetric bilinear from same jets
  apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
  let Q := quadratic G d t; let R := quadratic G d u
  have he (z) : Q z z = R z z := by
    have ht := congr_fun (phase_jet (room_ok d h) t u 2) z
    rw [half,half] at ht; apply mul_right_cancel₀ (show (2:ℝ)⁻¹ ≠ 0 by norm_num); exact ht
  have ha := he (x+y); rw [map_add,map_add] at ha; simp only [LinearMap.add_apply,map_add,(show R y x=R x y from (ambient u h).turns ..), (show Q y x= Q x y from (ambient t h).turns ..),he] at ha; linarith

-- allows evaluating the gaussian integral in ANY finite linear-functionals basis chosen
lemma moment_diagram (h : d.Room G) (Y : Fields G d → ℝ) (k : ℕ) :
    gaussianTerm P t Y k = (ambient t h).average (Chart.tangent G d.Links)
      (Radial.integrandSeries (d.phase G t) (nearFee P t Y) k) *
        ∫ x, Radial.kernel (d.phase G t) x ∂Chart.tangent G d.Links := by
  unfold Law.average gaussianTerm Radial.moment Radial.normTerm; rw [← kern_is]
  rw [div_mul_cancel₀ _ (show (∫ x, Radial.kernel (d.phase G t) x ∂Chart.tangent G d.Links) ≠ 0 from (integral_exp_pos (kernel_integrable t h)).ne')]; rfl

theorem wick_pay (h : d.Room G) {I : Type*} [DecidableEq I] (ℓ₀ : Module.Dual ℝ E)
    (ℓ : I → Module.Dual ℝ E) (L : Finset I) :
    let φ := d.phase G t
    let Γ := Chart.tangent G d.Links
    (∫ x, (∏ i ∈ L, ℓ i x) * ℓ₀ x * Radial.kernel φ x ∂Γ) /
      (∫ x, Radial.kernel φ x ∂Γ) = ∑ i ∈ L, (ambient t h).average Γ (Law.product ℓ (L.erase i)) *
        (ℓ i) ((ambient t h).inverse ℓ₀) := by
  dsimp only
  simp_rw [kern_is t h]; exact (ambient t h).recursion ..
end YM.RGComparison.Core16.Descent
