import YM.Integration.WilsonMatrixTicketLanesReportedPivot
import YM.Integration.WilsonOffsetIntervalDensity

/-! Identity-output credit of a nonlinear inverse-transported mark, including every signed part. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedCredit
open Filter Function Labels Wilson Lattice RG Source RG16.Literal Extraction Push.GridApprox
open PhysicalNext.Repeat.Legato RGComparison.Core16.Astage
open WilsonTranslatedFactory WilsonMatrixTicketLanesReportedPivot
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G) {d m N p : ℕ}

private theorem primary (t : ℝ) (z : R.family.label d) (y : Site (R.family.side m p))
    (U : Config G (R.family.side m p)) :
    (R.family.localSection d).places ((R.family.labels.level d).scaled t z) y U =
      z 0 + (R.family.localSection d).places ((R.family.labels.level d).scaled t
        ((R.family.labels.level d).core z)) y U := by
  let F := R.family.labels.level d
  let S := R.family.localSection d
  have split : z = z 0 • F.e0 + F.core z := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [F, Frame.e0, Frame.core]
    · simp [F, Frame.e0, Frame.core, hi]
  calc
    S.places (F.scaled t z) y U = S.places (F.scaled t (z 0 • F.e0 + F.core z)) y U :=
      congrArg (fun a => S.places (F.scaled t a) y U) split
    _ = _ := by
      simp only [map_add, map_smul, Frame.scaled_unit, SectionData.places,
        S.eval_linear.map_add, S.eval_linear.map_smul, Pi.add_apply, Pi.smul_apply,
        show S.evaluate F.e0 = 1 from (R.makes.sections d).unit, Pi.one_apply, smul_eq_mul, mul_one]
      rfl

/-- The three original signed entries left after the unmasked registered primary. -/
def remainder (Q : Coefficient (R.family.labels.level d) (R.family.side m p))
    (Y : Rep G (R.family.side m p)) (y : Site (R.family.side m p)) (U : Config G (R.family.side m p)) : ℂ :=
  let S := R.family.localSection d
  let z := S.places ((R.family.labels.level d).scaled Y.p.threshold⁻¹
    ((R.family.labels.level d).core Q.x)) y
  (masked Y.p.threshold (S.footprint y) z U - z U) + (∑' i, Q.maskedTerm Y i U) +
    ((Real.exp (Y.exponent U) : ℂ) / (Y.eval U : ℂ)) * ∑' b, Q.marked Y b U

private theorem balance (Q : Coefficient (R.family.labels.level d) (R.family.side m p))
    (Y : Rep G (R.family.side m p)) (y : Site (R.family.side m p)) (U : Config G (R.family.side m p))
    (pos : (Y.eval U : ℂ) ≠ 0) :
    Q.density y (R.family.localSection d) Y U / (Y.eval U : ℂ) =
      (R.family.localSection d).places ((R.family.labels.level d).scaled Y.p.threshold⁻¹ Q.x) y U +
        remainder R Q Y y U := by
  rw [primary R Y.p.threshold⁻¹ Q.x y U]
  unfold Coefficient.density Coefficient.exponentialEntry remainder
  dsimp only
  field_simp
  ring

private theorem head {m N : ℕ} (hN : m ≤ N) (y : Site (R.family.side m p)) (x : R.family.label d)
    (U : Config G (R.family.side m p)) :
    let Q := entry R.makes hN y ((R.family.factory d N p).terminal.symm x)
    R.family.O m p (center R m N p x) y U = ((R.family.S.a m : ℂ)^d)⁻¹ *
      (R.family.localSection d).places ((R.family.labels.level d).scaled
        (R.family.path.rep N p m).p.threshold⁻¹ Q.x) y U := by
  dsimp only
  have ht : (R.family.path.rep N p m).p.threshold = R.family.path.levels.clock.threshold m := by
    have eq : (R.family.path.rep N p m).p = R.family.path.levels.budget m :=
      (R.makes.wilson.represents N p m hN).vac
    rw [eq]
    rfl
  rw [WilsonTranslatedFactory.coordinate, ht]
  change ((R.family.S.a m : ℂ)^d)⁻¹ * (R.family.localSection d).places
    ((R.family.labels.level d).scaled (R.family.path.levels.clock.threshold m)⁻¹
      ((R.family.factory d m p).terminal.symm ((R.family.factory d m p).terminal
        (((R.family.factory d N p).entries m ((R.family.factory d N p).terminal.symm x)).x)))) y U = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

private theorem unit_credit (f : Cut R.family N p) (hN : m ≤ N) (U : Config G (R.family.side m p)) :
    credit R.family N p 0 f m hN U = ((R.family.S.a m : ℂ)^d)⁻¹ * credit R.family N p d f m hN U := by
  have ha : ((R.family.S.a m : ℂ)^d) ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos m).ne')
  simp only [credit, pow_zero, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ha,
    one_mul]

/-- The full original lower conditional of a marked upper field at the physical unit output. -/
theorem held (hm : R.family.ref d ≤ m) (hN : m ≤ N) (y : Site (R.family.side m p))
    (v : R.family.label d) (U : Config G (R.family.side m p)) :
    let x := Axle.root R.makes d m N p v
    let Q := entry R.makes hN y ((R.family.factory d N p).terminal.symm x)
    let Y := R.family.path.rep N p m
    credit R.family N p 0 (R.family.O N p x (anchor R.family.S p hN y)) m hN U / (Y.eval U : ℂ) =
      R.family.O m p (center R m N p x) y U + ((R.family.S.a m : ℂ)^d)⁻¹ * remainder R Q Y y U := by
  intro x Q Y
  have pos : (Y.eval U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Multi.AxisShift.chosen_positive R.makes.wilson hN U).ne'
  have transferred := congrFun (WilsonOffsetIntervalDensity.aligned R.makes hm hN y x) U
  change Q.density y (R.family.localSection d) Y U =
    credit R.family N p d (R.family.O N p x (anchor R.family.S p hN y)) m hN U at transferred
  let a := ((R.family.S.a m : ℂ)^d)⁻¹
  calc
    _ = a * (Q.density y (R.family.localSection d) Y U / (Y.eval U : ℂ)) := by
      rw [unit_credit R (d:=d), ← transferred]
      exact mul_div_assoc _ _ _
    _ = a * ((R.family.localSection d).places ((R.family.labels.level d).scaled
        Y.p.threshold⁻¹ Q.x) y U + remainder R Q Y y U) :=
      congrArg (fun n : ℂ => a * n) (balance R Q Y y U pos)
    _ = _ := by
      rw [mul_add]
      exact congrArg (fun n : ℂ => n + a * remainder R Q Y y U) (head R hN y x U).symm

end YM.Integration.WilsonMatrixTicketLanesReportedCredit
