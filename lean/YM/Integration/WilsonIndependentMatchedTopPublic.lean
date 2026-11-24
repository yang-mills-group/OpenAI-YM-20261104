import YM.Integration.WilsonIndependentMatchedTopBasis

/-! The actual independent public insertion at its appointed horizon. Its
finite coefficient array includes the survey's full negative Wick operator
after the signed on-shell lift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopPublic
open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb XSpace
open XSpace.Rose XSpace.Cirrus PhysicalNext.Repeat.Legato
open WilsonIndependentMatchedTopBasis (source)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(W:Initialize G)(Y:Sample 2)
variable (d:Fin 2→ℕ)(v:(i:Fin 2)→On.Grade G (d i))
local notation "F" i:max => R.family.labels.level (d i)
local notation "T" => W.tree Y.F.p

def coefficients (i:Fin 2) : (F i).Coeff :=
  (F i).coords ((W.surveys (d i)).insertW (-1) (On.sectionMap (d i) ⟨(v i).val,(v i).property.1⟩))

theorem original (i:Fin 2) :
    W.atSite Y.F (d i) (chartV Y i) (v i) =
      (((Y.F.spacing:ℂ)^(d i))⁻¹) • source R W Y d (coefficients R W d v) true i := by
  change (((Y.F.spacing:ℂ)^(d i))⁻¹) • Bare.column T (W.surveys (d i)) (chartV Y i)
    (On.sectionMap (d i) ⟨(v i).val,(v i).property.1⟩)=_
  rw [Bare.column_formula,←WilsonIndependentMatchedTopBasis.raw]
  unfold WilsonOriginalPublicPivotFaces.raw coefficients
  rw [LinearEquiv.symm_apply_apply]

theorem face (S:Finset (Fin 2)):
    Bare.normalized T G (∏i∈S,W.atSite Y.F (d i) (chartV Y i) (v i)) =
      Bare.normalized T G (∏i∈S,(((Y.F.spacing:ℂ)^(d i))⁻¹) •
        source R W Y d (coefficients R W d v) true i) := by
  simp only [original R W Y d v]

end YM.Integration.WilsonIndependentMatchedTopPublic
