import YM.Integration.WilsonPositionProgramTrialPublicCellProduct
import YM.Integration.WilsonPositionProgramTrialPublicCellVisits

/-! Exact engineering factors for the physical unit-cell integral on any selected registered face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicCellPhase
open Function Filter Finset Set MeasureTheory Lattice Extraction RG
open Wilson Source Extra.Histories Spec PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Layout WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonOriginalPublicNodalPlainSensor (sensor)
open WilsonPositionProgramTrialPublicCellPulse (placed)
open WilsonMeasuredPublicEntranceCoverCells (cube mass)
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I]{n:ℕ}
open WilsonPositionProgramTrialPublicCellProduct (price)
open WilsonPositionProgramTrialPublicCellVisits (weight)
open WilsonPositionProgramTrialPublicSpatialSum (held)

def layout (S:Finset I)(idx:Fin n≃S):(Fin n → Cover)≃(S → Cover) where
  toFun z i:=z (idx.symm i)
  invFun z i:=z (idx i)
  left_inv _:=by funext i;simp
  right_inv _:=by funext i;simp

def moved (D:I→ℕ)(S:Finset I)(idx:Fin n≃S)(T:(i:I)→Rarity (D i))
    (x y σ:ℝ)(sp:0<σ)(o:CellR)(ξ:Points n)(i:I):Rarity (D i):=
  placed (T i) x y σ sp o (fun e=>if h:i∈S then ξ (idx.symm ⟨i,h⟩) e else 0)

theorem paid (R:Run G)(D d:I→ℕ)(S:Finset I)(idx:Fin n≃S)(T:(i:I)→Rarity (D i))
    {r:ℝ}(rp:0<r)(m K:ℕ)(y:ℝ)(o:CellR)(z:Fin n → Cover)(ξ:Points n):
    let x:=paceT R.family.S m K
    let σ:=r/R.family.S.a m
    (∏i:S,x^(d i))*weight D d S (moved D S idx T x y σ (div_pos rp (R.family.S.a_pos m)) o ξ)
      x y o (layout S idx z)=∏k,price R (T (idx k)) (d (idx k)) rp m K y o (z k) (fun e=>ξ k e):=by
  intro x σ
  unfold WilsonPositionProgramTrialPublicCellVisits.weight
  rw [←Finset.prod_mul_distrib,←Equiv.prod_comp idx]
  apply Finset.prod_congr rfl
  intro i _
  simp [held,price,layout,moved,x,σ,paceT,map_smul,mul_assoc]

theorem measured (R:Run G)(D d:I→ℕ)(S:Finset I)(idx:Fin n≃S)(T:(i:I)→Rarity (D i))
    {r:ℝ}(rp:0<r)(m K:ℕ)(y:ℝ)(o:CellR)(z:Fin n → Cover)(ξ:Points n)(Φ:Test n)
    (product:∀t:Points n,Φ t=((∏i,(T (idx i)).ψ.val (fun a=>t i a):ℝ):ℂ)):
    let x:=paceT R.family.S m K
    let σ:=r/R.family.S.a m
    ((((∏i:S,x^(d i))*weight D d S (moved D S idx T x y σ (div_pos rp (R.family.S.a_pos m)) o ξ)
      x y o (layout S idx z)):ℝ):ℂ)=
      (R.family.S.a K/r)^(4*n) • Φ (WilsonViewerAffineCells.pull (R:=R) r K z ξ):=by
  intro x σ
  rw [paid R D d S idx T rp m K y o z ξ]
  simp_rw [WilsonPositionProgramTrialPublicCellProduct.leg R _ _ rp m K y o z ξ]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,
    product (WilsonViewerAffineCells.pull (R:=R) r K z ξ),Complex.real_smul,Complex.ofReal_mul]

end YM.Integration.WilsonPositionProgramTrialPublicCellPhase
end
