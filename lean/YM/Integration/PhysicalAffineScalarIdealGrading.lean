import YM.Integration.PhysicalAffineScalarFieldContraction
import YM.Next.FOUNDATIONS.LinkBounds

/-! The fourth-order beginning of a stationary residual square in the
original weak-coupling field coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarIdealGrading
open Filter Function FreeResolvent FreeResolvent.TestD
open scoped Topology ContDiff BigOperators Classical

variable {τ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- This applies to a genuine normalized stationary residual on the whole
ordered coarse direction space. -/
theorem derivative_zero {f : E→ℝ} (hf : DifferentiableAt ℝ f 0) (h₀ : f 0=0)
    (rate : ∀ v : E, Tendsto (fun t : ℝ => t⁻¹*f (t • v)) (𝓝[≠] 0) (𝓝 0)) :
    fderiv ℝ f 0=0 := by
  ext v
  have hv : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq,one_smul] using (hasDerivAt_id (0:ℝ)).smul_const v
  have h : HasFDerivAt f (fderiv ℝ f 0) ((0:ℝ) • v) := by simpa only [zero_smul] using hf.hasFDerivAt
  have hh := hasDerivAt_iff_tendsto_slope_zero.mp (h.comp_hasDerivAt 0 hv)
  have limit : Tendsto (fun t : ℝ => t⁻¹*f (t • v)) (𝓝[≠] 0) (𝓝 (fderiv ℝ f 0 v)) := by
    simpa [Function.comp_def,h₀] using hh
  exact tendsto_nhds_unique limit (rate v)

theorem short (v : τ→E) {f : E→ℝ} (h : ContDiffAt ℝ 1 f 0) (h₀ : f 0=0) (h₁ : fderiv ℝ f 0=0)
    (l : List τ) (hl : l.length≤1) : jet v f l 0=0 := by
  cases l with
  | nil => exact (zeroth v f 0).trans h₀
  | cons i t =>
    cases t with
    | nil =>
      rw [jet_step v i [] h,show jet v f []=f from funext (zeroth v f),h₁]
      simp
    | cons k t => simp at hl

/-- Each ordered field bipartition of at most three occurrences has a
factor with at most one occurrence, even with repeated external directions. -/
theorem square_short (v : τ→E) {f : E→ℝ} {n : ℕ} (h : ContDiffAt ℝ n f 0) (H : ContDiffAt ℝ 1 f 0)
    (h₀ : f 0=0) (h₁ : fderiv ℝ f 0=0) (l : List τ) (hl : l.length≤n) (hj : l.length≤3) :
    jet v (fun x => f x*f x) l 0=0 := by
  have hp := leibniz v (ContinuousLinearMap.mul ℝ ℝ) l (A:=f) (B:=f) (smooth_of_le h hl) (smooth_of_le h hl)
  change jet v (fun x => f x*f x) l 0=∑ m : Masks l,jet v f (lo l m) 0*jet v f (hi l m) 0 at hp
  rw [hp]; apply Finset.sum_eq_zero; intro m _
  have hm := lengths l m
  by_cases loSmall : (lo l m).length≤1
  · rw [short v H h₀ h₁ _ loSmall,zero_mul]
  · rw [short v H h₀ h₁ (hi l m) (by omega),mul_zero]

def scaled (g : ℝ) (f : E→ℝ) (B : E) := -(2*g^2)⁻¹*f (g • B)

/-- Each external coarse field receives exactly one copy of the physical
scalar when pulled back by the original Gaussian field rescaling. -/
theorem pulled_jet (g : ℝ) (v : τ→E) (f : E→ℝ) (l : List τ) (hf : ContDiffAt ℝ l.length f 0) :
    jet v (fun B => f (g • B)) l 0=g^l.length*jet v f l 0 := by
  let A : E→L[ℝ] E := g • ContinuousLinearMap.id ℝ E
  change iteratedFDeriv ℝ l.length (f ∘ A) 0 (v ∘ l.get)=_
  rw [Next.Foundations.jets_linear A hf,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ l.length f 0 (fun j => g • (v (l.get j)))=_
  have h := (iteratedFDeriv ℝ l.length f 0).map_smul_univ (fun _ => g) (v ∘ l.get)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Function.comp_apply,jet] using h

/-- Put back the true fine physical g before any derivative is evaluated.
The exponent belongs to the full order and does not depend on coincidences. -/
theorem scaled_jet (g : ℝ) (v : τ→E) (f : E→ℝ) (l : List τ) (hf : ContDiffAt ℝ l.length f 0) :
    jet v (scaled g f) l 0=(-(2*g^2)⁻¹*g^l.length)*jet v f l 0 := by
  let L : ℝ→L[ℝ] ℝ := (-(2*g^2)⁻¹) • ContinuousLinearMap.id ℝ ℝ
  have h : ContDiffAt ℝ l.length f (g • (0:E)) := by simpa only [smul_zero] using hf
  have hc : ContDiffAt ℝ l.length (fun b : E => f (g • b)) 0 := h.comp 0 (contDiffAt_const.smul contDiffAt_id)
  rw [show scaled g f = (fun b => L (f (g • b))) from rfl,jet_linear v l L hc,pulled_jet g v f l hf]
  exact (mul_assoc _ _ _).symm

theorem coefficient {g : ℝ} (hg : 0<g) {j : ℕ} (hj : 2≤j) :
    |-(2*g^2)⁻¹*g^j|=g^(j-2)/2 := by
  have hp : g^j=g^2*g^(j-2) := by rw [←pow_add]; congr 1; omega
  have e : -(2*g^2)⁻¹*g^j=-(g^(j-2)/2) := by
    rw [hp]
    field_simp [hg.ne']
  rw [e,abs_neg,abs_of_nonneg (by positivity)]

end YM.Integration.PhysicalAffineScalarIdealGrading
