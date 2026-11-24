import YM.XSpace.VertexTaylor
import YM.LocalH.Haar
import YM.Next.RANK.Gaussian

/-!
# Orbit Wilson bare LPT, all orders at fixed regulator (prior to field conditions)

These coefficients are defined by the Gaussian Taylor/Wick rules at the trivial
saddle, NOT by any asymptotic calculation on exact correlations. This file is at fixed
cutoff, lattice units, `g` the formal BARE coupling, no regulator limit. Inputs
(possibly products) are polynomials in tangent fields at each order; assembling the
arrays with the operator weights, field conditions and profile sums is separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Bare
open Function Set Filter Lattice Wilson Precision
open PowerSeries
open scoped Topology BigOperators ENNReal ContDiff
variable {G : Gauge} {R : Period} (T : R.Tree)

/-- Chart fixed once, on each link. -/
def chart (G : Gauge) := (LocalH.actual G).choose
lemma chart_ratio (G : Gauge) : LocalRatio (chart G) := (LocalH.actual G).choose_spec
lemma probability_change (G : Gauge) :
    MeasureTheory.Measure.map G.lieExp ((MeasureTheory.volume.restrict (Metric.ball 0 (chart G).radius)).withDensity
      (fun x : G.Color => ENNReal.ofReal ((chart G).scale*(chart G).J x))) =
    G.probHaar.restrict (G.lieExp '' (Metric.ball 0 (chart G).radius)) := (chart_ratio G).actual

abbrev Vertices (G : Gauge) := MvPolynomial (T.Key G) ℂ
abbrev Series (G : Gauge) := PowerSeries (Vertices T G)

def relative (v : T.Field G) : ℝ := ∏ e : T.Free, (chart G).J (v e)
lemma relative_one (G : Gauge) : relative (G:=G) T 0=1 := by simp [relative,(chart_ratio G).anchored]
lemma relative_smooth (G : Gauge) : ContDiffAt ℝ ω (relative (G:=G) T) 0 := by
  unfold relative
  refine contDiffAt_prod ?_
  intro i _; exact ((chart_ratio G).germ 0 (Metric.mem_ball_self (chart_ratio G).patch)).comp (0:T.Field G) (contDiffAt_apply _ _ _ _)

/-- Chart origin = log zero; include product Jacobian normalized to its value there.
The divided Hessian term of the Wilson action is accounted in the Gaussian, not here. -/
def haar (G : Gauge) : Series T G := Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘ relative T)

def interaction (G : Gauge) : Series T G := PowerSeries.mk fun n=> if n=0 then 0 else
  -Taylor.divided (T.basis G) (n+2) (Complex.ofRealCLM ∘ T.action)

lemma haar_initial (G : Gauge) : constantCoeff (haar T G)=1:=by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp only [haar,Taylor.expandTaylor,coeff_mk,Taylor.divided_zero,Function.comp_apply]; rw [relative_one]; simp
lemma interaction_initial (G : Gauge) : constantCoeff (interaction T G)=0:=by rw [← coeff_zero_eq_constantCoeff_apply]; simp [interaction]

theorem interaction_coeff (v : T.Field G) {n : ℕ} (h : n≠0) :
    Taylor.evalAt (T.basis G) v (coeff n (interaction T G)) =
    - ↑(((n+2).factorial:ℝ)⁻¹ * iteratedFDeriv ℝ (n+2) T.action 0 (fun _=> v)) := by
  rw [interaction, coeff_mk, if_neg h,map_neg, Taylor.divided_realEval _ _ _ ((T.continuousJet G).of_le le_top)]

theorem haar_coeff (v : T.Field G) (n : ℕ) :
    Taylor.evalAt (T.basis G) v (coeff n (haar T G)) =
    ↑((n.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ n (relative T) 0 (fun _=> v)) := by
  rw [haar,Taylor.expandTaylor,coeff_mk,Taylor.divided_realEval _ _ _ ((relative_smooth T G).of_le le_top)]

def interactionExp (G : Gauge) : Series T G := subst (interaction T G) (PowerSeries.exp (Vertices T G))
lemma exponential_formula (G : Gauge) (n : ℕ) :
    coeff n (interactionExp T G)=∑ m∈Finset.range (n+1),
      algebraMap ℚ (Vertices T G) (1/m.factorial:ℚ)*coeff n (interaction T G^m):= by
  rw [interactionExp,FPS.coeff_substituted _ (interaction_initial T G)]; simp
lemma exp_starts (G : Gauge) : constantCoeff (interactionExp T G)=1:=by rw [← coeff_zero_eq_constantCoeff_apply,exponential_formula]; norm_num

def weight (G : Gauge) : Series T G := haar T G * interactionExp T G
lemma weight_one (G : Gauge) : constantCoeff (weight T G)=1:=by rw [weight,map_mul,haar_initial,exp_starts,one_mul]

open Next.Rank.Normal
/-- Real covariance (then records as complex), exactly inverse Hessian. `Next.Rank.Normal.blend Q 0`
implements Wick pairing via the polynomial Gaussian rule. -/
def Q (G : Gauge) : Next.Rank.Normal.Symmetric (T.Key G) where
  cov i j:= T.covariance G i j
  symm i j:= by
    congr 1
    exact (show T.covariance G j i=T.covariance G i j from by simpa using (T.covariance_posDef G).1.apply i j).symm

-- expose Wick equation
lemma pairs (G : Gauge) (i : T.Key G) (p : Vertices T G) :
    blend (Q T G) 0 (MvPolynomial.X i*p)=blend (Q T G) 0 (slit (fun j=> (T.covariance G i j:ℂ)) p) := by rw [blended]; simp; rfl

/-- Gaussian normalization fixed to give one on the empty graph. -/
def diagrams (G : Gauge) : Series T G →ₗ[ℂ] PowerSeries ℂ :=
  FPS.extending (blend (Q T G) 0) ∘ₗ LinearMap.mulLeft ℂ (weight T G)
lemma diagram_coeff (F : Series T G) (n : ℕ) : coeff n (diagrams T G F)=blend (Q T G) 0 (coeff n (weight T G* F)) := by
  unfold diagrams; rw [LinearMap.comp_apply, FPS.coeff_extending]; rfl

def vacuum (G : Gauge) := diagrams T G 1
@[simp] lemma vacuum_start (G : Gauge) : constantCoeff (vacuum T G) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, vacuum, diagram_coeff, mul_one, coeff_zero_eq_constantCoeff_apply, weight_one, Next.Rank.Normal.fresh]
lemma invertible_vacuum (G : Gauge) : IsUnit (vacuum T G) := isUnit_iff_constantCoeff.mpr (by simp)

def normalized (G : Gauge) : Series T G →ₗ[ℂ] PowerSeries ℂ :=
    LinearMap.mulLeft ℂ (vacuum T G)⁻¹ ∘ₗ diagrams T G
lemma normalize_denominator (G : Gauge) (F : Series T G) : normalized T G F * vacuum T G = diagrams T G F := by
  change (vacuum T G)⁻¹ * _ * _ = _; rw [mul_right_comm,PowerSeries.inv_mul_cancel _ (by simp),one_mul]
lemma denominator_determines (G : Gauge) (F : Series T G) (Z : PowerSeries ℂ)
    (h : Z*vacuum T G=diagrams T G F) : Z=normalized T G F :=
  (invertible_vacuum T G).mul_left_inj.mp (h.trans (normalize_denominator T G F).symm)
@[simp] lemma normalize_unit (G : Gauge) : normalized T G 1=1 :=
    (denominator_determines T G 1 _ (one_mul (vacuum T G))).symm
lemma leading (F : Series T G) : constantCoeff (normalized T G F) = blend (Q T G) 0 (constantCoeff F) := by
  have ht := congr_arg constantCoeff (normalize_denominator T G F)
  rw [map_mul,vacuum_start,mul_one,← coeff_zero_eq_constantCoeff_apply (diagrams T G F),diagram_coeff,coeff_zero_eq_constantCoeff_apply,map_mul,weight_one,one_mul] at ht
  exact ht

-- Formal-ℂ-multilinearity in sources; doesn't factorize `normalized` of a product.
def scalar (F : PowerSeries ℂ) : Series T G := PowerSeries.map (algebraMap ℂ (Vertices T G)) F
lemma normalized_scalar (F : PowerSeries ℂ) (Y : Series T G) :
    normalized T G (scalar T F*Y) = F*normalized T G Y:=by
  change (vacuum _ _)⁻¹ * FPS.extending _ (_ * (_*Y)) = F * ((vacuum _ _)⁻¹ * FPS.extending _ (_ * Y))
  unfold scalar; rw [mul_left_comm (weight T G),FPS.extending_mul_self,mul_left_comm]
end YM.XSpace.Bare
