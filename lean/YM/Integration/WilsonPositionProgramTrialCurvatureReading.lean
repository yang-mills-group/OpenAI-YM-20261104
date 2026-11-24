import YM.Integration.WilsonPositionProgramTrialGroundCylinder

/-! On the chosen finite inverted period, every branch of the numerical
public vector has the same Laurent expansion as its complete original
curvature programme. The test functions and the index-dependent poles
are restored before any limit in a physical regulator. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCurvatureReading
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato
open XSpace PowerSeries RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb
open MeasureTheory Pert.Asymptotics
open WilsonThermometerPositionTunedSlope (Columns paid finite)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonPositionProgramCopyTop (planted)
open private sum_ratio from YM.Integration.WilsonThermometerInversionFaces
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
variable (v:∀i,(R.family.labels.level (d i)).Coeff)(z:I → Cover)(P:XSpace.Period)

private theorem real_leg (L:ℂ→L[ℝ]ℝ)(r:ℝ)(x:ℂ):L (x*(r:ℂ))=L x*r:=by
  simpa only [Complex.real_smul,smul_eq_mul,mul_comm] using L.map_smul r x

omit [LinearOrder I] in
private theorem expansion (b:Columns R d)(u:ℝ):
    WilsonOriginalPublicTrialFigure.weight R d u v b=(∏j,v j (b j))*(((u⁻¹)^(Kick.depthF univ d b):ℝ):ℂ):=by
  simp only [WilsonOriginalPublicTrialFigure.weight,WilsonOriginalPublicTrialFigure.amount,
    Complex.ofReal_inv,Complex.ofReal_pow,inv_pow,prod_mul_distrib,prod_inv_distrib,
    prod_pow_eq_pow_sum,Kick.depthF]

theorem original (tree:P.Tree)(L:ℂ→L[ℝ]ℝ)(k:ℕ):
    L (coeff k (paid R d (frozen R d v) (finite R d P z tree)))=
      WilsonThermometerInversionFaces.series R d (wrap P.side ∘ z) 1 1 v
        (fun (_:I) (_:Unit)=>1) () L k:=by
  let w(b:Columns R d):=L (∏i,v i (b i))
  let O(b:Columns R d):=planted R P d z b
  let pole(b:Columns R d):=Kick.depthF univ d b
  let face:=WilsonThermometerInversionFaces.face R d (wrap P.side ∘ z) 1 1 v
    (fun (_:I) (_:Unit)=>1) () L
  have admissible(b:Columns R d):PreTest (O b):=WilsonPositionProgramCopyTop.allowed R P d z b
  have ev:=even_iff_two_dvd.mpr P.even
  have phase(u:ℝ)(pos:0<u):preExpectation (face u) u=
      ∑b,w b*(u⁻¹)^(pole b)*preExpectation (O b) u:=by
    have printed:face u=∑b,(w b*(u⁻¹)^(pole b)) • O b:=by
      funext U
      dsimp only [face]
      rw [WilsonPositionProgramTrialGroundCylinder.original R d v z pos.ne',
        WilsonOriginalPublicTrialFigure.opened,map_sum]
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      refine sum_congr rfl fun b _=>?_
      rw [expansion,real_leg,real_leg]
      rfl
    rw [printed,sum_ratio O (fun b=>(admissible b).continuous)]
  have read:=WilsonPositionFiniteLaurentCoefficient.identify pole w _ _
    (fun b u=>preExpectation (O b) u) (fun b=>Orb.diag (restrictedO (O b)))
    (WilsonThermometerInversionFaces.finite R d (wrap P.side ∘ z) 1 1 v
      (fun (_:I) (_:Unit)=>1) () L ev)
    (fun b=>before_tree_formula ev (traySpec G) (admissible b)) phase k
  rw [read,WilsonPositionProgramTrialThermalGrades.coefficient,map_sum]
  refine sum_congr rfl fun b _=>?_
  rw [WilsonPositionProgramCopyTop.normalized,YM.FVA2.XPos.genuine_X tree (admissible b),
    coeff_map,coeff_mk]
  rw [add_comm k]
  exact real_leg L _ _

end YM.Integration.WilsonPositionProgramTrialCurvatureReading
end
