import MSPositionScreens
import MSPositionLabels

/-! The same finite position measurements and the same calibrated triangle
are used at every perturbative order and every physical scale. -/

set_option autoImplicit false
namespace YangMills.MSbar

variable {g : GaugeGroup}

structure PositionPrescription (B : Maxwell.Reference g) where
  screen (d : ℕ) : Position.Screen B d
  triangle : Position.Triangle B

/-- Admissibility involves only the free Maxwell sectors and the explicit cubic
diagram. The same profiles test every raw MS coefficient family under comparison. -/
structure Admissible {B : Maxwell.Reference g} (P : PositionPrescription B)
    : Prop extends Position.Prepared P.screen where
  calibration : P.triangle.Admissible
  screenClearance (i : Fin (P.screen 6).size) :
    let w := (P.screen 6).window i
    ∀ x ∈ tsupport w.profile, ∀ a b : Fin w.arity, a ≠ b →
      5 * P.triangle.cut.rOut < ‖x a - x b‖

/-- Choose one admissible menu before the Wilson run. Proof irrelevance fixes
the result across existence proofs. Admissibility alone does not specify the profiles. -/
noncomputable def nominatedMenu {B : Maxwell.Reference g}
    (menus : Nonempty {P : PositionPrescription B // Admissible P}) :
    {P : PositionPrescription B // Admissible P} := Classical.choice menus

end YangMills.MSbar
