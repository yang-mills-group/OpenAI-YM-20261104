import YM.Integration.WilsonThermometerOwnOffsetField
import YM.Integration.WilsonCoherentTerminalFrame

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonAddressedReportedColumns
open Function Filter MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical ProjectorNext.Equivariance
open RGComparison.Core16 RGComparison.Core16.Spool
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G)

/-- The physical threshold exponent is fixed on the entire addressed alphabet. -/
def toll (C : Family G) (d : ℕ) : ℕ :=
  Finset.univ.sup fun j : Mark C d => ((C.labels.level (kept j.1)).grades j.2).2

def weightsAt {C : Family G} {d : ℕ} (θ : ℝ) (x : Palette C d) : Palette C d :=
  fun t => (C.labels.level (kept t)).scaled θ⁻¹ ((C.labels.level (kept t)).core (x t))

theorem tariff {C : Family G} {d : ℕ} {θ : ℝ} (hθ : 0 < θ) (x : Palette C d) :
    size (weightsAt θ x) ≤ max 1 θ⁻¹ ^ toll C d * size x := by
  classical
  rw [size, size, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let F := C.labels.level (kept j.1)
  have hle : (F.grades j.2).2 ≤ toll C d :=
    Finset.le_sup (f:=fun k : Mark C d => ((C.labels.level (kept k.1)).grades k.2).2)
      (Finset.mem_univ j)
  have core : ‖F.core (x j.1) j.2‖ ≤ ‖x j.1 j.2‖ := by
    by_cases hj : j.2=0 <;> simp [Frame.core,Function.update,hj]
  have hp : θ⁻¹ ^ (F.grades j.2).2 ≤ max 1 θ⁻¹ ^ toll C d :=
    (pow_le_pow_left₀ (inv_nonneg.mpr hθ.le) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hle)
  change ‖F.scaled θ⁻¹ (F.core (x j.1)) j.2‖ ≤ _ * ‖x j.1 j.2‖
  rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
    (pow_nonneg (inv_nonneg.mpr hθ.le) _)]
  exact mul_le_mul hp core (norm_nonneg _) (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)

/-- The true covered local Wilson field on every configuration uses the original
    basis sources, with unit and failed operands still credited separately. -/
theorem fields {n : Side} {d : ℕ} (v : R.family.label d) (o : Site n) (A : Config G n) :
    (R.family.localSection d).places v o A =
      ∑ a,v a * Light (WilsonCoherentTerminalFrame.lamp R d a) n o A := by
  classical
  let E : R.family.label d →ₗ[ℂ] ℂ :=
    (MvPolynomial.aeval (entry (expandAt o A))).toLinearMap.comp (R.family.localSection d).evalC
  have total : v=∑ a,v a • Pi.single a (1:ℂ) := by
    ext i
    simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
  change E v = _
  conv_lhs => rw [total,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_smul]
  rfl

/-- The test of an actual post keeps the same mask on every summand and its
    original residual slots. Its explicit scalar is independent of that mask. -/
theorem exponential {n : Side} {d : ℕ} (P : Rep G n)
    (X : Coefficient (R.family.labels.level d) n) (o : Site n) (A : Config G n) :
    X.exponentialEntry o (R.family.localSection d) P A = X.x 0 +
      masked P.p.threshold ((R.family.localSection d).footprint o)
        (fun T => ∑ a,(R.family.labels.level d).scaled P.p.threshold⁻¹
          ((R.family.labels.level d).core X.x) a *
          Light (WilsonCoherentTerminalFrame.lamp R d a) n o T) A +
        ∑' i,X.maskedTerm P i A := by
  have read : (R.family.localSection d).places ((R.family.labels.level d).scaled P.p.threshold⁻¹
      ((R.family.labels.level d).core X.x)) o = _ := funext (fun T => fields R _ o T)
  rw [Coefficient.exponentialEntry,read]

/-- The actual post, all derivative letters and its original tail before selecting
    any coefficients for the independent program. -/
theorem original {base N p m d : ℕ} {D : Rail R.family} {B : ℕ → ℕ → ℝ}
    {V : Sight R.family d p} {r : Emblems R.family d} (z : Site (R.family.side N p))
    (H : Enrolled R.makes D B base N p d (digits R N p z) V r)
    (entered : base ≤ m) (live : m ≤ N) (y : Palette R.family d)
    (order : d ≤ (R.family.path.rep N p m).p.order)
    (power : d ≤ (R.family.path.rep N p m).p.power)
    (positive : 0 < (R.family.path.rep N p m).p.threshold) :
    let P := R.family.path.rep N p m
    let M := (1 + wrap_price d R.family * Germ.wraps P.p (R.family.side m p) * B d m) * size y
    ∃ x : Palette R.family d,
      Printed R.family d P 0 (kappa R.family.path m) (V m y) x y (B d m * size y) ∧
      size x ≤ M ∧ size (weightsAt P.p.threshold x) ≤ max 1 P.p.threshold⁻¹ ^ toll R.family d * M := by
  intro P M
  obtain ⟨raw,placed⟩ := (H.legal m entered live).capacity0 y
  let x : Palette R.family d := raw
  change Printed R.family d P 0 (kappa R.family.path m) (V m y) x y (B d m * size y) at placed
  have w := wraps_paid d R.family placed order power
  have same : size (x-y) = size (y-x) := by rw [← size_neg (y-x)]; simp
  have bill : size x ≤ M := calc
    size x ≤ size y + size (x-y) := size_compare x y
    _ = size y + size (y-x) := by rw [same]
    _ ≤ size y + wrap_price d R.family * Germ.wraps P.p (R.family.side m p) * (B d m * size y) :=
      add_le_add_right w _
    _ = M := by dsimp [M]; ring
  exact ⟨x,placed,bill,(tariff positive x).trans (mul_le_mul_of_nonneg_left bill
    (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))⟩

end YM.Integration.WilsonAddressedReportedColumns
