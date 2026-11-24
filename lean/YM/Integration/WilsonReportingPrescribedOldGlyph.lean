import YM.Integration.WilsonReportingPrescribedOldGrade
import YM.Integration.WilsonPositionSeparatedProfilePosteriorRegistered

/-! The finite Gaussian contractions on a real nonbare reporting field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldGlyph

open Lattice Wilson Source Labels Extraction Table Spec RG17
open PhysicalNext.Repeat.Legato MS MS.Menus MS.Local.Physical
open WilsonReportingPrescribedOldGrade WilsonMatrixTicketLanesReportedPivot
open scoped Classical

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (L : Layout F) {B : Deck G} {h : ℕ} (v : Glyph B h)

abbrev scale (h : ℕ) (r : ℝ) : ℂ := (((r / R.family.S.a (L.level r))^h : ℝ) : ℂ)

/-- The native reported input of one glyph with its signed original fee. -/
def filed (r : ℝ) (z : ℂ) : R.family.label v.size :=
  scale R F L h r • (L.shift v.size r).symm
    ((R.family.labels.level v.size).scaled (R.family.path.levels.clock.monitor (L.level r))
      (z • thermal R v))

abbrev observed (r : ℝ) (z : ℂ) (N per : ℕ)
    (o : Site (R.family.side (L.level r) per)) (U : Config G (R.family.side (L.level r) per)) :=
  R.family.O (L.level r) per (center R (L.level r) N per
    (atRef L v.size r (N,per) (filed R F L v r z))) o U

private theorem places_smul {d : ℕ} {n : Side} (o : Site n) (U : Config G n)
    (c : ℂ) (y : R.family.label d) :
    (R.family.localSection d).places (c • y) o U =
      c * (R.family.localSection d).places y o U :=
  congrFun ((R.family.localSection d).eval_linear.map_smul c y) (expandAt o U)

private theorem places_add {d : ℕ} {n : Side} (o : Site n) (U : Config G n)
    (x y : R.family.label d) :
    (R.family.localSection d).places (x+y) o U =
      (R.family.localSection d).places x o U + (R.family.localSection d).places y o U :=
  congrFun ((R.family.localSection d).eval_linear.map_add x y) (expandAt o U)

/-- At every original cutoff and every field the discrepancy from the raw
independent column is a section involving only strictly lower field degrees. -/
theorem original (r : ℝ) (z : ℂ) (N per : ℕ) (age : R.family.ref v.size ≤ L.level r)
    (future : L.level r ≤ N) (o : Site (R.family.side (L.level r) per))
    (U : Config G (R.family.side (L.level r) per)) :
    let g := R.family.path.levels.clock.hatCoupling (L.level r)
    ((g^v.grade : ℝ) : ℂ) * observed R F L v r z N per o U =
      scale R F L h r * z * ((R.family.localSection v.size).places (raw R v) o U +
        (R.family.localSection v.size).places (lower R v g) o U) := by
  let m := L.level r
  let g := R.family.path.levels.clock.hatCoupling m
  let η := R.family.path.levels.clock.monitor m
  have gp : 0 < g := inv_pos.mpr (Real.sqrt_pos.mpr
    (zero_lt_one.trans (R.family.path.levels.fits.delayed m)))
  have ep : 0 < η := Real.exp_pos _
  have ht : (R.family.path.rep N per m).p.threshold = g * η := by
    have rep : (R.family.path.rep N per m).p = R.family.path.levels.budget m :=
      (R.makes.wilson.represents N per m future).vac
    rw [rep]
    rfl
  have occ := WilsonPositionSeparatedProfilePosteriorRegistered.row R F L v.size r
    (filed R F L v r z) N per age future o U
  have ex : (R.family.labels.level v.size).scaled (g*η)⁻¹
      ((R.family.labels.level v.size).scaled η (thermal R v)) =
      (R.family.labels.level v.size).scaled g⁻¹ (thermal R v) := by
    ext1 j
    simp only [Frame.scaled_apply, ← mul_assoc, ← Complex.ofReal_mul, ← mul_pow]
    rw [show (g * η)⁻¹ * η = g⁻¹ by field_simp]
  change ((g^v.grade : ℝ) : ℂ) * observed R F L v r z N per o U = _
  rw [observed, ← occ]
  change _ * (R.family.localSection v.size).places ((R.family.labels.level v.size).scaled
    (R.family.path.rep N per m).p.threshold⁻¹ (L.shift v.size r (filed R F L v r z))) o U = _
  rw [filed, map_smul, LinearEquiv.apply_symm_apply, ht, map_smul, map_smul, map_smul, ex]
  rw [places_smul, places_smul]
  have identity := congrArg (fun y => (R.family.localSection v.size).places y o U)
    (WilsonReportingPrescribedOldGrade.original R v g gp.ne')
  change (R.family.localSection v.size).places _ o U =
    (R.family.localSection v.size).places _ o U at identity
  rw [places_smul, places_add] at identity
  rw [← identity]
  ring

end YM.Integration.WilsonReportingPrescribedOldGlyph
