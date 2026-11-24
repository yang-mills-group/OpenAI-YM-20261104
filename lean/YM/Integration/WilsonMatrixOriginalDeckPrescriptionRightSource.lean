import YM.Integration.WilsonMatrixOriginalDeckPrescriptionDecoder
import YM.Integration.WilsonMatrixOriginalDeckPrescriptionMarginals

/-! The complete right physical change on the same original upper configuration, with the other physical input fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightSource
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 MS MS.Land MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm Lattice Wilson
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckRawAssay WilsonMatrixOriginalDeckPrescriptionSeries
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) {D:Deck G} (Q:MS.Land.Prescription D) {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (L:Layout F) (h:ℕ)
local notation "I"=>Glyph D h
local notation "prescribed"=>WilsonMatrixOriginalDeckPrescriptionFields.field R Q h
local notation "upper"=>deposited R F L h

/-- The independently prescribed complete two-clock change with both original upper deposits retained. -/
def contrast (μ ν r s:ℝ)(w v:I→R.family.label h)(N p:ℕ)(j:I):SiteField R N p:=fun o U=>
  (upper s (v j) N p o U-prescribed ν 0 N p o U j)-
  ∑b,(upper r (w b) N p o U-prescribed μ 0 N p o U b)*trial Q h μ ν 0 b j

theorem measured (μ ν r s:ℝ)(w v:I→R.family.label h)(N p:ℕ)(j:I):
    contrast R Q F L h μ ν r s w v N p j=
      (fun o U=> upper s (v j) N p o U-∑b,upper r (w b) N p o U*trial Q h μ ν 0 b j):=by
  funext o U
  have actual:=congrFun (WilsonMatrixOriginalDeckPrescriptionReturn.born R Q h μ ν N p o U) j
  simp only [Matrix.vecMul_apply_eq_sum] at actual
  simp only [contrast,actual,sub_mul,Finset.sum_sub_distrib];abel

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightSource
