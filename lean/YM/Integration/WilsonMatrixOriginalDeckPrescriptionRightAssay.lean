import YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightCharge

/-! The entry left in the physical inverse is the Wilson joint of one unchanged and one changed field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightAssay
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 Lattice Wilson RG MS MS.Land MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckRawAssay WilsonMatrixOriginalDeckFiledDebit
open WilsonMatrixOriginalDeckPrescriptionSeries WilsonMatrixOriginalDeckPrescriptionRightSource
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) {D:Deck G} (Q:MS.Land.Prescription D){f:Extraction.Order}{S:Table R.family.book}
variable (F:Spec.Final R.family f S)(L:Layout F)(h:ℕ)
local notation "I"=>Glyph D h
local notation "roster"=>WilsonMatrixOriginalDeckPrescriptionPairing.basis (B:=D) h

theorem original (g:Test 2){r:ℝ}(hr:0<r)(s μ ν:ℝ)(w v:I→R.family.label h)(z:ℕ×ℕ)(i j:I):
    let T:=dilate hr g
    let a:=roster μ 0
    let b:=roster ν 0
    let τ:=trial Q h μ ν 0
    let E:=signed R F L Q h T z r s w v a b
    let H:=signed R F L Q h T z r r w w a a
    (E-H*τ) i j=joint R T z.1 z.2 (scene R.family.path z.1 z.2 z.1)
      (deposited R F L h r (w i) z.1 z.2) (contrast R Q F L h μ ν r s w v z.1 z.2 j):=by
  intro T a b τ E H
  let ρ:=scene R.family.path z.1 z.2 z.1
  letI:IsProbabilityMeasure ρ:=probability R.makes.wilson le_rfl
  let X:=deposited R F L h r (w i) z.1 z.2
  have cx(o):Continuous (X o):=R.family.continuousO ..
  have qq:=WilsonMatrixOriginalDeckPrescriptionGram.born R Q h T z a μ ν
  have mixed:=fields R F L Q h g hr s w v a b z
  have self:=fields R F L Q h g hr r w w a a z
  have balance:field R D F L h g hr s w v z-field R D F L h g hr r w w z*τ=E-H*τ:=by
    rw [mixed,self,Matrix.add_mul]
    change matrix R Q h T z a b+E-(matrix R Q h T z a a*τ+H*τ)=E-H*τ
    rw [qq];abel
  rw [←balance,Matrix.sub_apply,Matrix.mul_apply]
  change WilsonMatrixOriginalDeckFiled.operand R F L h g hr s (w i) (v j) z-
    ∑b,WilsonMatrixOriginalDeckFiled.operand R F L h g hr r (w i) (w b) z*τ b j=_
  simp_rw [WilsonMatrixOriginalDeckRawMoment.original R F L h]
  exact (WilsonMatrixOriginalDeckPrescriptionRightCharge.charged R Q F L h T z.1 z.2 ρ X cx μ ν r s w v j).1.symm

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightAssay
