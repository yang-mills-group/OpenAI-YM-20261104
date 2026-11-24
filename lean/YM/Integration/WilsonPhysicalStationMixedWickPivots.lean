import YM.Integration.WilsonPhysicalNamedVaneBasis
import YM.Integration.WilsonPhysicalStationGradedLowerPanel
import YM.Integration.WilsonPhysicalThermalWickProbe
import YM.Integration.WilsonPhysicalStationThermalBasisOffice

/-! The reflected lower Gram inputs are measured at their own Wick rank,
including the original unit and every nonzero coordinate of the fitted lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPivots
open Function Lattice Wilson RG Source Cells Labels Maxwell Maxwell.Free
open PhysicalNext.Repeat.Legato MS MS.Land MS.Theater MS.Menus XSpace.Structure1
open Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named)
open Further.CorrectedLift (ladder)
open WilsonPhysicalThermalWickRankSupport (Counted support)
open WilsonPhysicalThermalWickProbe (mirrored conjugated)
open WilsonPhysicalStationThermalBasisOffice (rank)
open scoped Classical
variable {G:Gauge}(R:Run G)(B:Deck G){e:ℕ}(a:Axis)(i:Glyph B e)
local notation "C₀" => Cells.standard R.family
local notation "F₀" => R.family.labels.level e

def reflected:(C₀).Field e:=(C₀).adj (spin_free R.family.labels) e a (named R B e i)

theorem counted:Counted (F₀) (ladder R.family e (named R B e i)) i.2.1.val:=by
  let x:=ladder R.family e (named R B e i)
  intro t
  funext j
  change ((t ^ ((F₀).grades j).2:ℝ):ℂ)*x j=((t^i.2.1.val:ℝ):ℂ)*x j
  by_cases empty:x j=0
  · rw [empty,mul_zero,mul_zero]
  · have exactGrade:=WilsonPhysicalNamedVaneBasis.original R B i j empty
    rw [exactGrade]

theorem original (j:(F₀).Index)(active:ladder R.family e (reflected R B a i) j≠0):
    rank R.family e j=i.2.1.val:=by
  apply support (F₀) _ _ _ j active
  exact mirrored R.family _ _ (conjugated R.family _ _ (counted R B i)) (Signed.mirror a)

end YM.Integration.WilsonPhysicalStationMixedWickPivots
end
