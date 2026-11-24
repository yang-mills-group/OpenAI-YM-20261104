import YM.Integration.WilsonMatrixTicketLanesReportedCredit
import YM.Integration.WilsonMatrixTicketLanesReportedAdmission

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedPlating
open Filter FVA2 OPE RG12 RG17 Extraction Spec Wilson Table RG Lattice Labels
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Astage
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesReportedPivot
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : RG17.Layout F)

/-- The angular coefficients of the freshly registered physical field at its actual
reporting date, fixed independently of the later cutoff and torus. -/
def column (d : ℕ) (r : ℝ) (w : R.family.label d) : R.family.label d :=
  (R.family.labels.level d).scaled (R.family.path.levels.clock.threshold (L.level r))⁻¹
    (L.shift d r w)

theorem coordinates (d : ℕ) (r : ℝ) (w : R.family.label d) (N p : ℕ)
    (age : R.family.ref d ≤ L.level r) (future : L.level r ≤ N) :
    WilsonCoherentTerminalFrame.coordinates R (L.level r) p
      (center R (L.level r) N p (atRef L d r (N,p) w)) = column R F L d r w := by
  let m := L.level r
  let T := R.family.factory d N p
  let A := RG12.charts R.family F.room.cutoff d m (N,p)
  have row (v : R.family.label d) : A v = (T.entries m (T.terminal.symm v)).x := by
    unfold A
    rw [RG12.charts,dif_pos ⟨age,future⟩]
    rfl
  have deposited : (T.entries m (T.terminal.symm (atRef L d r (N,p) w))).x =
      ((R.family.S.a m^d:ℝ):ℂ) • L.shift d r w := by
    rw [←row]
    change A (((R.family.S.a m^d:ℝ):ℂ) • A.symm (L.shift d r w)) = _
    rw [map_smul,LinearEquiv.apply_symm_apply]
  change (R.family.labels.level d).scaled _ (((R.family.S.a m:ℂ)^d)⁻¹ •
    (R.family.factory d m p).terminal.symm ((R.family.factory d m p).terminal
      ((T.entries m (T.terminal.symm (atRef L d r (N,p) w))).x))) = _
  rw [LinearEquiv.symm_apply_apply,deposited,Complex.ofReal_pow,smul_smul,
    inv_mul_cancel₀ (pow_ne_zero d (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne')),one_smul]
  rfl

/-- Every filed future label gives exactly the same fixed finite printed row inside
the original nonlinear group field at the reporting date. -/
theorem measured (d : ℕ) (r : ℝ) (w : R.family.label d) (N p : ℕ)
    (age : R.family.ref d ≤ L.level r) (future : L.level r ≤ N)
    (o : Site (R.family.side (L.level r) p)) (U : Config G (R.family.side (L.level r) p)) :
    R.family.O (L.level r) p (center R (L.level r) N p (atRef L d r (N,p) w)) o U =
      ∑ j,column R F L d r w j * Light (WilsonCoherentTerminalFrame.lamp R d j)
        (R.family.side (L.level r) p) o U := by
  rw [WilsonCoherentTerminalFrame.row,coordinates R F L d r w N p age future]

/-- The full absolute coefficient charge retains the stipulated engineering
grade and uses the genuine running temperature. -/
theorem price (d : ℕ) (r : ℝ) (w : R.family.label d) :
    mass R.family d (column R F L d r w) ≤ R.family.path.levels.clock.hatBeta (L.level r)^d
      * mass R.family d (L.shift d r w) := by
  let m := L.level r
  let A := R.family.path.levels
  let B := A.clock.hatBeta m
  have one : 1 ≤ B := (A.fits.delayed m).le
  have monitor : 1 ≤ A.clock.monitor m := Real.one_le_exp (sq_nonneg _)
  have root : Real.sqrt B ≤ B := by
    have fromOne := Real.sqrt_le_sqrt one
    rw [Real.sqrt_one] at fromOne
    nlinarith only [mul_le_mul_of_nonneg_left fromOne (Real.sqrt_nonneg B),
      Real.sq_sqrt (zero_le_one.trans one)]
  have upper : (A.clock.threshold m)⁻¹ ≤ B := by
    change ((_ : ℝ)⁻¹ * A.clock.monitor m)⁻¹ ≤ B
    rw [mul_inv_rev,inv_inv]
    exact (mul_le_mul_of_nonneg_right ((inv_le_one₀ (zero_lt_one.trans_le monitor)).mpr monitor)
      (Real.sqrt_nonneg _)).trans ((one_mul _).le.trans root)
  have pos : 0 ≤ (A.clock.threshold m)⁻¹ := (inv_pos.mpr (A.budget m).threshold_pos).le
  unfold mass Labels.Frame.coeffSize
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  change ‖(R.family.labels.level d).scaled (A.clock.threshold m)⁻¹ (L.shift d r w) i‖ ≤
    B^d * ‖L.shift d r w i‖
  rw [Labels.Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg pos _)]
  exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ pos upper _).trans
    (pow_le_pow_right₀ one (Planned.PrimaryIntegral295.Film.second_fits (R.family.labels.level d) i)))
    (norm_nonneg _)

end YM.Integration.WilsonMatrixTicketLanesReportedPlating
