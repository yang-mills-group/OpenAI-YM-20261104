import YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightSource

/-! One changed upper Wilson field under any genuine finite law, including its two proper conditional means. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightCharge
open Filter Set Finset MeasureTheory Spec Table Ward PhysMS RG17 MS MS.Land MS.Menus MS.Local.Physical
open Extraction Extraction.Order PhysicalNext.Repeat.Legato Next.UVStress Push.GridApprox OPE OPE.Therm Lattice Wilson
open WilsonMatrixOriginalDeckRawMoment WilsonMatrixOriginalDeckPrescriptionSeries WilsonMatrixOriginalDeckPrescriptionRightSource
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G)

theorem subtract (T:Test 2)(N p:ℕ)(ρ:Measure (Config G (R.family.side N p))) [IsFiniteMeasure ρ]
    (X Y Z:SiteField R N p)(cx:∀o,Continuous (X o))(cy:∀o,Continuous (Y o))(cz:∀o,Continuous (Z o)):
    joint R T N p ρ X (fun o U=>Y o U-Z o U)=joint R T N p ρ X Y-joint R T N p ρ X Z ∧
    separatedMeans R T N p ρ X (fun o U=>Y o U-Z o U)=separatedMeans R T N p ρ X Y-separatedMeans R T N p ρ X Z:=by
  constructor
  · unfold joint;rw [←Finset.sum_sub_distrib];apply sum_congr rfl;intro x _
    have y:Integrable (fun U=>X (x 0) U*Y (x 1) U) ρ:=((cx (x 0)).mul (cy (x 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have z:Integrable (fun U=>X (x 0) U*Z (x 1) U) ρ:=((cx (x 0)).mul (cz (x 1))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [←mul_sub];apply congrArg (fun t=>WilsonExternalMeshMass.charge R.family T x*t)
    calc _=(∫U,(X (x 0) U*Y (x 1) U-X (x 0) U*Z (x 1) U) ∂ρ):=by
            apply integral_congr_ae;filter_upwards with U;exact mul_sub _ _ _
         _=_:=integral_sub y z
  · unfold separatedMeans;rw [←Finset.sum_sub_distrib];apply sum_congr rfl;intro x _
    have y:Integrable (Y (x 1)) ρ:=(cy (x 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have z:Integrable (Z (x 1)) ρ:=(cz (x 1)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_sub y z];ring

variable {D:Deck G} (Q:MS.Land.Prescription D) {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S)(L:Layout F)(h:ℕ)
local notation "I"=>Glyph D h
local notation "upper"=>deposited R F L h

theorem charged (T:Test 2)(N p:ℕ)(ρ:Measure (Config G (R.family.side N p))) [IsFiniteMeasure ρ]
    (X:SiteField R N p)(cx:∀o,Continuous (X o))(μ ν r s:ℝ)(w v:I→R.family.label h)(j:I):
    let high:=upper s (v j) N p
    let low:=fun b:I=>upper r (w b) N p
    let c:=fun b:I=>trial Q h μ ν 0 b j
    let Y:=contrast R Q F L h μ ν r s w v N p j
    joint R T N p ρ X Y=joint R T N p ρ X high-∑b,joint R T N p ρ X (low b)*c b ∧
    separatedMeans R T N p ρ X Y=separatedMeans R T N p ρ X high-∑b,separatedMeans R T N p ρ X (low b)*c b:=by
  intro high low c Y
  let sumLow:=fun o U=>∑b,low b o U*c b
  have ch(o):Continuous (high o):=R.family.continuousO ..
  have cl(b:I)(o):Continuous (low b o):=R.family.continuousO ..
  have cs(o):Continuous (sumLow o):=continuous_finsetSum _ (fun b _=>(cl b o).mul continuous_const)
  have paid:=subtract R T N p ρ X high sumLow cx ch cs
  have jointLow:joint R T N p ρ X sumLow=∑b,joint R T N p ρ X (low b)*c b:=
    WilsonMatrixOriginalDeckPrescriptionPairing.linear R T N p ρ X low c cx cl
  have meansLow:separatedMeans R T N p ρ X sumLow=∑b,separatedMeans R T N p ρ X (low b)*c b:=
    WilsonMatrixOriginalDeckPrescriptionMarginals.proper R T N p ρ X low c cl
  have present:Y=(fun o U=>high o U-sumLow o U):=WilsonMatrixOriginalDeckPrescriptionRightSource.measured R Q F L h μ ν r s w v N p j
  rw [present];simpa only [jointLow,meansLow] using paid

end YM.Integration.WilsonMatrixOriginalDeckPrescriptionRightCharge
