import YM.Integration.WilsonPositionProgramTrialPublicCellMass
import YM.Integration.WilsonPositionProgramTrialPublicCellPulse

/-! The genuine covered mass of a smooth product test equals the integral
of the enrolled Rarity values, with every engineering factor restored. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellProduct
open Function Filter Finset Set MeasureTheory Lattice Extraction RG
open Wilson Source Extra.Histories Spec PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonOriginalPublicNodalPlainSensor (sensor)
open WilsonPositionProgramTrialPublicCellPulse (placed)
open WilsonMeasuredPublicEntranceCoverCells (cube mass)
open scoped Classical BigOperators
variable {G:Gauge}{n D:ℕ}

def price (R:Run G)(T:Rarity D)(d:ℕ){r:ℝ}(rp:0<r)(m K:ℕ)(y:ℝ)(o:CellR)(z:Cover)(ξ:Point4):ℝ:=
  let x:=R.family.S.a K/R.family.S.a m
  let σ:=r/R.family.S.a m
  x^d*drumB d x*sensor D (wheelC x y z (placed T x y σ (div_pos rp (R.family.S.a_pos m)) o ξ).ψ o)

theorem leg (R:Run G)(T:Rarity D)(d:ℕ){r:ℝ}(rp:0<r)(m K:ℕ)(y:ℝ)(o:CellR)
    (z:Fin n → Cover)(ξ:Points n)(i:Fin n):
    price R T d rp m K y o (z i) (fun a=>ξ i a)=(R.family.S.a K/r)^4*
      T.ψ.val (fun a=>WilsonViewerAffineCells.pull (R:=R) r K z ξ i a):=by
  let x:=R.family.S.a K/R.family.S.a m
  let σ:=r/R.family.S.a m
  have xp:0<x:=div_pos (R.family.S.a_pos K) (R.family.S.a_pos m)
  have scale:(R.family.S.a K/r)*σ=x:=by dsimp [x,σ];field_simp [rp.ne']
  have eng:x^d*drumB d x=x^4:=by rw [mul_comm];simp [drumB,xp.ne']
  rw [←WilsonPositionProgramTrialPublicCellPulse.physical R T rp m K y o z ξ i]
  change (x^d*drumB d x)*_= (R.family.S.a K/r)^4*(σ^4*_)
  rw [eng,←mul_assoc,←mul_pow,scale]

theorem original (R:Run G)(D d:Fin n→ℕ)(T:(i:Fin n)→Rarity (D i)){r:ℝ}(rp:0<r)
    (m K:ℕ)(y:ℝ)(o:CellR)(z:Fin n → Cover)(Φ:Test n)
    (product:∀t:Points n,Φ t=((∏i,(T i).ψ.val (fun a=>t i a):ℝ):ℂ)):
    mass Φ (R.family.S.a K) r z=
      ∫ξ in cube 1 1 (0:Fin n → Cover),((∏i,price R (T i) (d i) rp m K y o (z i) (fun a=>ξ i a):ℝ):ℂ):=by
  rw [WilsonPositionProgramTrialPublicCellMass.original R rp K z Φ,←integral_smul]
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  simp_rw [leg R _ _ rp m K y o z ξ]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,
    product (WilsonViewerAffineCells.pull (R:=R) r K z ξ),Complex.real_smul,Complex.ofReal_mul]

end YM.Integration.WilsonPositionProgramTrialPublicCellProduct
end
