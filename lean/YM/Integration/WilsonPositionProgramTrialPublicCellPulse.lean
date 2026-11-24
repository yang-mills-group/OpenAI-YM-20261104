import YM.Integration.WilsonPositionProgramTrialPublicCensus
import YM.Integration.WilsonIndependentMovingRosterOuterSupport
import YM.Integration.WilsonOriginalPublicNodalMeasuredSensor
import YM.Integration.WilsonViewerAffineCells

/-! A separate translation of each measured test realizes the genuine
fractional position in its physical cell on one common independent clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellPulse
open Function Filter Finset Set MeasureTheory Lattice Extraction RG
open Wilson Source Extra.Histories Spec PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonIndependentFittedExteriorProfile (home)
open WilsonOriginalPublicNodalPlainSensor (sensor)
open scoped Classical BigOperators
variable {G:Gauge}{D n:ℕ}

def placed (T:Rarity D)(x y σ:ℝ)(sp:0<σ)(o:CellR)(ξ:Point4):Rarity D:=
  home T σ sp (-(y • o.val)-x • ξ)

theorem value (T:Rarity D)(x y σ:ℝ)(sp:0<σ)(o:CellR)(z:Cover)(ξ:Point4):
    sensor D (wheelC x y z (placed T x y σ sp o ξ).ψ o)=
      σ⁻¹^4*T.ψ.val ((x/σ) • (actualW z+ξ)):=by
  rw [WilsonOriginalPublicNodalMeasuredSensor.wheel]
  unfold placed
  rw [WilsonIndependentMovingRosterOuterSupport.relative]
  congr 2
  apply congr_arg T.ψ.val
  funext a
  change σ⁻¹*(-(-(y*o.val a)-x*ξ a)+(x*actualW z a-y*o.val a+x*0))=
    (x/σ)*(actualW z a+ξ a)
  ring

theorem physical (R:Run G)(T:Rarity D){r:ℝ}(rp:0<r)(m K:ℕ)(y:ℝ)(o:CellR)
    (z:Fin n → Cover)(ξ:Points n)(i:Fin n):
    let x:=R.family.S.a K/R.family.S.a m
    let σ:=r/R.family.S.a m
    let shift:Point4:=fun a=>ξ i a
    σ^4*sensor D (wheelC x y (z i) (placed T x y σ (div_pos rp (R.family.S.a_pos m)) o shift).ψ o)=
      T.ψ.val (fun a=>WilsonViewerAffineCells.pull (R:=R) r K z ξ i a):=by
  intro x σ shift
  have sp:0<σ:=div_pos rp (R.family.S.a_pos m)
  rw [value,←mul_assoc,←mul_pow,mul_inv_cancel₀ sp.ne',one_pow,one_mul]
  apply congr_arg T.ψ.val
  funext a
  change ((R.family.S.a K/R.family.S.a m)/(r/R.family.S.a m))*((z i a:ℝ)+ξ i a)=
    r⁻¹*(R.family.S.a K*(z i a:ℝ))+(R.family.S.a K/r)*ξ i a
  field_simp [rp.ne',(R.family.S.a_pos m).ne']

end YM.Integration.WilsonPositionProgramTrialPublicCellPulse
end
