import YM.Integration.WilsonSurveyedColorVacuumKernel
import YM.XSpace.OrthoActor
import YM.XSpace.Clan

/-! The actual orthogonal color convention of the free stabilizer, on each
component of its Taylor tower and its chamber polynomials. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumKnight
open Function Finset Next.Rank Normal Maxwell Maxwell.Free XSpace XSpace.Stab OJoint
open scoped BigOperators Classical
variable {G : Gauge} (c : Knight G)

def isometry : G.Color ≃ₗᵢ[ℝ] G.Color where
  toLinearEquiv := {
    toLinearMap := Spin c
    invFun := Spin c⁻¹
    left_inv := fun x => by
      change Spin c⁻¹ (Spin c x) = _
      rw [←spin_mul,inv_mul_cancel,spin_one]
    right_inv := fun x => by
      change Spin c (Spin c⁻¹ x) = _
      rw [←spin_mul,mul_inv_cancel,spin_one] }
  norm_map' := spin_norm c

def shell (x : TaylorTower G) : TaylorTower G := fun j =>
  faceMap j (isometry c).toContinuousLinearEquiv.toContinuousLinearMap (x j)

theorem channel (j : ℕ) (i : G.ColorIndex) (x : TaylorTower G) :
    faceMap j (cp (G:=G) i) (shell c x j) =
      ∑ b : G.ColorIndex, c.val i b • faceMap j (cp (G:=G) b) (x j) := by
  apply Subtype.ext
  funext a b
  ext1 y
  simp only [Submodule.coe_sum,Submodule.coe_smul_of_tower,Finset.sum_apply,
    _root_.sum_apply,Pi.smul_apply,_root_.smul_apply,
    smul_eq_mul]
  rfl

theorem coordinates (x : TaylorTower G) (d : ℕ) :
    chord (shell c x) d = swept c (chord x d) := by
  apply PiLp.ext
  intro i
  change pieces i.1.1.val i.1.2 (faceMap _ (cp (G:=G) i.2) (shell c x _)) =
    ∑ b : G.ColorIndex, c.val i.2 b *
      pieces i.1.1.val i.1.2 (faceMap _ (cp (G:=G) b) (x _))
  rw [channel,map_sum]
  apply sum_congr rfl
  intro b _
  exact map_smul (pieces i.1.1.val i.1.2) (c.val i.2 b) _

theorem observed {d : ℕ} (p : Chamber G d) (x : TaylorTower G) :
    probe x (appears G d (changing c p)) = probe (shell c x) (appears G d p) := by
  rw [appears_read,appears_read,changing_value,coordinates]

theorem recorded {d : ℕ} (p : HFields G d) (x : TaylorTower G) :
    probe x (appears G d (changing c (records G d p))) = probe (shell c x) p.val := by
  rw [observed,opensR]

end YM.Integration.WilsonSurveyedColorVacuumKnight
end
