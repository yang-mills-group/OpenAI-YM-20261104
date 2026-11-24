import YM.Integration.WilsonCapturedPrimaryAperture
import YM.Next.STATIONARY.Lift.Pathways
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Rod
import YM.Comparison.RG02.Integral.Bill

/-! Express every clipped finite-coordinate test as the actual potential
of the same finite Wilson enrollment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryPotential
open Function Filter Finset Set Labels Lattice Wilson RG Source Push.Local
open Next.Foundations Planned.AtomRegular WilsonCapturedPrimaryAngles WilsonCapturedPrimaryAperture
open ConnectedActivityE6.SliceRows Stationary Comparison.RG02
open scoped Classical ContDiff
variable {G : Gauge} {n : Side} {d : ℕ}

def potential (g : ℝ) (v : Directions G n) : Stationary.Link G n :=
  (Stationary.arm G n 1).symm (toLog (g⁻¹ • v))

def lifted (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    (g t : ℝ) : Stationary.Link G n :=
  potential g (limitAmp (WilsonCapturedPrimaryRough.quadratic P) o (active o r) (angular A P o r p t))

private def logMap (g : ℝ) : Directions G n →ₗ[ℝ] Stationary.Link G n where
  toFun := potential g
  map_add' a b := by
    apply (Stationary.arm G n 1).injective
    simp only [map_add,potential,ContinuousLinearEquiv.apply_symm_apply]
    funext i;change g⁻¹ • (a _ + b _)=_;rw [smul_add];rfl
  map_smul' s a := by
    apply (Stationary.arm G n 1).injective
    simp only [map_smul,potential,ContinuousLinearEquiv.apply_symm_apply,RingHom.id_apply]
    funext i;change g⁻¹ • s • a _ =s • g⁻¹ • a _;rw [smul_comm]

/-- The filed independent operator sees one explicit polynomial in the real
argument, with the same incidence map and logarithm branch at every node. -/
theorem polynomial (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    (g t : ℝ) : lifted A P o r p g t =
      ∑ j∈range (d+1), t^j • potential g (limitAmp (WilsonCapturedPrimaryRough.quadratic P) o
        (active o r) (coeff A P o r p j)) := by
  let L := (logMap (G:=G) (n:=n) g).comp (limitAmp (WilsonCapturedPrimaryRough.quadratic P) o (active o r)).toLinearMap
  change L _ = _
  rw [angular,map_sum];simp only [map_smul];rfl

theorem scaled (g : ℝ) (v : Directions G n) :
    Exterior.collect G (Stationary.arm G n 1 (potential g v)) = g⁻¹ • v := by
  rw [potential,ContinuousLinearEquiv.apply_symm_apply,collects]

theorem sampled {g : ℝ} (hg : 0<g) (v : Directions G n) :
    Integral.sample g (Stationary.arm G n 1 (potential g v)) = increment 1 v := by
  rw [potential,ContinuousLinearEquiv.apply_symm_apply,Integral.sample]
  have physical : g • toLog (g⁻¹ • v) = toLog v := by
    funext i; change g • g⁻¹ • v _ = _;rw [smul_smul,mul_inv_cancel₀ hg.ne',one_smul];rfl
  rw [physical,edits]

def bound (G : Gauge) (P : BudgetPoint) (g cap : ℝ) := aperture G*P.threshold/g/cap

theorem window (G : Gauge) (P : BudgetPoint) {g cap : ℝ} (hg : 0<g) (hc : 1≤cap) :
    |bound G P g cap| ≤ (P.B:ℝ)^2*P.threshold/g := by
  have pos : 0≤aperture G*P.threshold/g :=
    div_nonneg (mul_nonneg (positive G).le P.threshold_pos.le) hg.le
  have one : (1:ℝ)≤(P.B:ℝ) := by exact_mod_cast P.B_pos
  rw [bound,abs_of_nonneg (div_nonneg pos (zero_le_one.trans hc))]
  exact (div_le_self pos hc).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((atMostOne G).trans (one_le_pow₀ one)) P.threshold_pos.le) hg.le)

/-- One real wallet works for the entire tiny interval, including its flat
node. The native comparison tests precisely these potentials at every
admitted finite period. -/
theorem resolved (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    {g cap : ℝ} (hg : 0<g) (hc : 0<cap) {t : ℝ} (one : |t|≤1)
    (paid : P.threshold*(1+(r:ℝ))^2≤1) (small : |t| * wallet A p r ≤ aperture G*P.threshold) :
    let V := lifted A P o r p g t
    Integral.sample g (Stationary.arm G n 1 V) = WilsonCapturedPrimaryRays.field A P o r p t ∧
      flags P.threshold (Integral.sample g (Stationary.arm G n 1 V))=∅ ∧
      (∀ e, ‖Exterior.collect G (Stationary.arm G n 1 V) e‖ ≤ cap*|bound G P g cap|) := by
  intro V
  let v := limitAmp (WilsonCapturedPrimaryRough.quadratic P) o (active o r) (angular A P o r p t)
  obtain ⟨hv,_,hz⟩ := chart A P o r p one paid small
  have eqv : Integral.sample g (Stationary.arm G n 1 (potential g v)) =
      WilsonCapturedPrimaryRays.field A P o r p t := by rw [sampled hg,physical];rfl
  refine ⟨eqv,eqv ▸ hz,?_⟩
  have positive : 0 ≤ bound G P g cap := div_nonneg
    (div_nonneg (mul_nonneg (WilsonCapturedPrimaryAperture.positive G).le P.threshold_pos.le) hg.le) hc.le
  intro e
  change ‖Exterior.collect G (Stationary.arm G n 1 (potential g v)) e‖ ≤ _
  rw [scaled,Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hg),abs_of_nonneg positive]
  calc
    _ ≤ g⁻¹*(aperture G*P.threshold) :=
      mul_le_mul_of_nonneg_left ((norm_le_pi_norm v e).trans hv) (inv_nonneg.mpr hg.le)
    _ = cap*bound G P g cap := by unfold bound;field_simp

theorem original (A : Hol G) (P : BudgetPoint) (o : Site n) (r : ℕ) (p : Probe G d)
    {g cap : ℝ} (hg : 0<g) (hc : 0<cap) {t : ℝ} (one : |t|≤1)
    (paid : P.threshold*(1+(r:ℝ))^2≤1) (small : |t| * wallet A p r ≤ aperture G*P.threshold) :
    ∃ V : Stationary.Link G n,
      Integral.sample g (Stationary.arm G n 1 V) = WilsonCapturedPrimaryRays.field A P o r p t ∧
      flags P.threshold (Integral.sample g (Stationary.arm G n 1 V))=∅ ∧
      (∀ e, ‖Exterior.collect G (Stationary.arm G n 1 V) e‖ ≤ cap*|bound G P g cap|) :=
  ⟨lifted A P o r p g t,resolved A P o r p hg hc one paid small⟩

end YM.Integration.WilsonCapturedPrimaryPotential
