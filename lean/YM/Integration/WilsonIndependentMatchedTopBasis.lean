import YM.Integration.WilsonIndependentMatchedTopFilm
import YM.Integration.WilsonOriginalPublicPlantedPair
import YM.Integration.WilsonOriginalPublicFigureWickFaces

/-! The literal measured and bare arms of the three proper residuals, on the
same sample as the fitted top. Both real and imaginary signed raw coefficients
are retained by complex linearity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedTopBasis
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato XSpace XSpace.Cirrus XSpace.Rose
open WilsonIndependentMatchedNamedPair (sectionAt placed printed)
open PertExtension PertExtension.Orb.SlotEvaluation PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G)(Y:Sample 2)
variable (d:Fin 2→ℕ)(v:(i:Fin 2)→(R.family.labels.level (d i)).Coeff)
local notation "F" i:max => R.family.labels.level (d i)
local notation "T" => W.tree Y.F.p

def source (survey:Bool)(i:Fin 2) : Bare.Series T G :=
  ∑j:(F i).Index,v i j • printed R W Y survey (d i) (Y.layout i) j

theorem physical (i:Fin 2) :
    WilsonOriginalPublicPlantedFaces.field R W d v Y i = source R W Y d v false i := rfl

theorem raw (i:Fin 2) :
    WilsonOriginalPublicPivotFaces.raw R W d v Y i = source R W Y d v true i :=
  WilsonOriginalPublicFigureWickFaces.letters R W d v Y i

/-- The scalar channel is the actual constant group function on this same
sample, before and after reflection. -/
theorem unit (survey:Bool)(i:Fin 2)(h:ℕ) :
    placed R W Y survey h (Y.layout i) 0 = 1 := by
  let sec:=sectionAt R W survey h
  have atUnit:sec.evaluate (R.family.labels.level h).e0=1 := by
    cases survey with
    | false => exact (R.makes.sections h).unit
    | true => exact (WilsonOriginalPivotWardSurvey.issued R W h).1.unit
  funext U
  change (sec.evaluate (R.family.labels.level h).e0 (expandAt (chartV Y i) U)).re=1
  rw [atUnit]
  rfl

/-- Both exact finite deposited responses on their actual original faces.
The price of a fitted comparison or crossed Ward row is external to this
algebraic grouping, and its amplitude is kept on the native complex bank. -/
theorem faces (P:(x:Sample 2)→Fin 2→Bare.Series (W.tree x.F.p) G)(S B:Finset (Fin 2)) :
    WilsonOriginalPublicPlantedFaces.occupied R W d v P Y S B =
      Bare.normalized T G ((∏i∈B,(source R W Y d v false i-P Y i))*(∏i∈S\B,P Y i)) ∧
    WilsonOriginalPublicPivotFaces.part R W d v P Y S B =
      Bare.normalized T G ((∏i∈B,(source R W Y d v true i-P Y i))*(∏i∈S\B,P Y i)) := by
  constructor
  · rfl
  · change Bare.normalized T G ((∏i∈B,(WilsonOriginalPublicPivotFaces.raw R W d v Y i-P Y i))*
      (∏i∈S\B,P Y i)) = _
    simp only [raw]

end YM.Integration.WilsonIndependentMatchedTopBasis
