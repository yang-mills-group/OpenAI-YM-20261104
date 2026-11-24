import YM.Integration.ActualOriginalDictionary
import YM.FVAAlt2.Rocket.Export

/-! Strictly lower Gaussian terms in an independently prescribed marked column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldGrade

open Lattice Wilson Source MS MS.Menus MS.Local.Physical FVAAlt2
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge
open scoped Classical

variable {G : Gauge} (R : Run G) {B : Deck G} {h : ℕ} (v : Glyph B h)

abbrev raw : R.family.label v.size :=
  ActualOriginalDictionary.coordinates R B v.size v.grade v.2.2

abbrev thermal : R.family.label v.size := Lobby.γ (basisR R) (Lobby.owner v)

/-- Every retained term has strictly smaller original field degree. -/
def lower (g : ℝ) : R.family.label v.size := fun j =>
  if ((R.family.labels.level v.size).grades j).2 < v.grade then
    ((g^(v.grade - ((R.family.labels.level v.size).grades j).2) : ℝ) : ℂ) * thermal R v j
  else 0

theorem current (j : (R.family.labels.level v.size).Index)
    (hj : v.grade ≤ ((R.family.labels.level v.size).grades j).2) :
    thermal R v j = raw R v j := by
  exact Shop.current_p B (R.family.localSection v.size) (R.makes.sections v.size)
    ((basisR R).bid v.size) j v.2.2 hj

/-- The calibrated column at physical coupling, including all angular components. -/
theorem original (g : ℝ) (hg : g ≠ 0) :
    ((g^v.grade : ℝ) : ℂ) • (R.family.labels.level v.size).scaled g⁻¹ (thermal R v) =
      raw R v + lower R v g := by
  ext1 j
  let l := ((R.family.labels.level v.size).grades j).2
  have off (hi : l ≠ v.grade) : raw R v j = 0 :=
    ActualOriginalDictionary.off_grade R B v.size v.grade v.2.2 j
      (fun he => hi (congrArg Prod.snd he))
  change ((g^v.grade : ℝ) : ℂ) * (((g⁻¹^l : ℝ) : ℂ) * thermal R v j) =
    raw R v j + if l < v.grade then ((g^(v.grade-l) : ℝ) : ℂ) * thermal R v j else 0
  by_cases hl : l < v.grade
  · rw [if_pos hl, off hl.ne, zero_add]
    have h : g^v.grade * g⁻¹^l = g^(v.grade-l) := by
      nth_rw 1 [← Nat.sub_add_cancel hl.le]
      rw [pow_add, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hg), mul_one]
    rw [← mul_assoc, ← Complex.ofReal_mul, h]
  · rw [if_neg hl, add_zero, current R v j (Nat.le_of_not_gt hl)]
    by_cases eq : l = v.grade
    · rw [eq, ← mul_assoc, ← Complex.ofReal_mul, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hg)]
      simp
    · rw [off eq, mul_zero, mul_zero]

end YM.Integration.WilsonReportingPrescribedOldGrade
