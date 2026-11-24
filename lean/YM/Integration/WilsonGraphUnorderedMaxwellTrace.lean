import YM.Integration.WilsonGraphMaxwellPanels
import YM.XSpace.Twins

/-! The double trace and the six plane squares on the filed Maxwell shell. -/
set_option autoImplicit false
noncomputable section

namespace YM.UVNext.FreeStress.PublicPanels
open Maxwell Labels Climb Table Work.A01 Next.UVStress
open XSpace.Normalize (Index left right)
open scoped BigOperators
variable {G : Gauge} (F : Frames G)

theorem totalPlanes : total F = (2 : ℂ) • ∑ k : Index,
    flat F (left k) (right k) (left k) (right k) := by
  let q (a b : Axis) := flat F a b a b
  have diagonal (a : Axis) : q a a = 0 := by simp [q, flat]
  have swap (a b : Axis) : q a b = q b a := by
    dsimp only [q, flat]
    rw [left_link F _ b a, right_link F _ b a b a, neg_neg]
  have six : (∑ k : Index, q (left k) (right k)) =
      q 0 1 + (q 0 2 + (q 0 3 + (q 1 2 + (q 1 3 + q 2 3)))) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    rfl
  change (∑ a : Axis, ∑ b : Axis, q a b) = (2 : ℂ) • ∑ k : Index, q (left k) (right k)
  rw [six]
  simp only [Fin.sum_univ_four, diagonal, two_smul]
  rw [swap 1 0, swap 2 0, swap 3 0, swap 2 1, swap 3 1, swap 3 2]
  abel

theorem cellLeg (c : G.ColorIndex) (a b : Axis) :
    Free.flavor (G := G) 0 c (Free.cell a b) = Free.omegaLeg c a b := by
  ext1 x
  rfl

theorem planeLabel (k : Index) :
    Free.phi (G := G) (left k) (left k) (right k) (right k) =
      XSpace.Normalize.label G k k := by
  simp only [XSpace.Normalize.label, Free.team, Free.bit, Free.phi, cellLeg]

include F in
theorem publicTrace : (∑ a : Axis, Free.sheetEnergy (G := G) a a) =
    (2 : ℂ) • ∑ k : Index, XSpace.Normalize.label G k k := by
  rw [← totalAddress F, totalPlanes]
  simp only [map_smul, map_sum, flatAddress, planeLabel]

end YM.UVNext.FreeStress.PublicPanels

