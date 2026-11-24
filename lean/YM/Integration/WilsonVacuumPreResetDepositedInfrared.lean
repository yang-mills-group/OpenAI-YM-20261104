import YM.Integration.WilsonVacuumPreResetDepositedPhase

/-! The native infrared subtraction of the original finite reader is
the coarse quadratic. Its common free Gaussian cancels between fields. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedInfrared
open Next.SectorChange Function Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Mosaic WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric Marker Multi
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)
variable (head:filed R N m p Z 0=shine (orbQ (precisionC G (fine R m p) (upper R N m))))

abbrev quadratic := orbC (precisionC G (coarse R m p) (lower R N m))
abbrev net := retool (shift R N m p hm F) (unscaled (step R m p) F (prediction R N m p)
  (filed R N m p Z))-relativeHaar R N m p hm F

include tag head in
private theorem origin:
    coeff 0 (net R N m p hm F Z)=coeff 0 (coarseAction R N m p F)+
      coeff 0 (bodyQ (Woods G (coarse R m p)) (precision R N m p F)):=by
  have shell:shellK 2 (filed R N m p Z):=WilsonLimitConstruction.FundedSpringPeriodGerm.grade _ _ _ _
  have e:=WilsonVacuumPreResetStationaryChange.phase_zero R N m p hm F tag _ shell head 0 (map_zero _)
  unfold relativePhase at e
  rw [map_sub (retool _),retool_tall,map_zero,add_zero] at e
  simp only [map_add,map_sub] at e
  simp only [net,coeff_zero_eq_constantCoeff_apply,map_sub]
  linear_combination -e

variable {T:Type}[DecidableEq T]{J:Census T}(Q:Bulk.Colors J G (fine R m p))
variable (cash:BudgetPoint)(cap:ℕ){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)
    (x y:fieldDir G (coarse R m p) 1)

include head cash width draw low high in
private theorem one (well:Bulk.Well Q):
    let K:=model R N m p hm
    let z:Key F G→ℝ:=0
    Bulk.infrared (step R m p) (income R N m p).clip (income R N m p).path F tag (K.b F) x+
      Gaussian.force (K.covariance F tag) z/2=
      MvPolynomial.eval (flatten x) (coeff 0 (quadratic R N m p))+
        MvPolynomial.eval z (paint 2 (orbQ (precision R N m p F))):=by
  intro K z
  have w:Bulk.Well (source R m p Z Q cap):=
    (QuadraticLocal.Fk.well _ _ (WilsonVacuumPreResetTorusDeposit.legal Z width draw low _) Q well).1
  have calcG:=WilsonVacuumPreResetDepositedGeometric.original R N m p hm F tag Z Q cash cap
    width draw low high x z w 2
  have h:=(Bulk.completed K F tag (source R m p Z Q cap) x z w).symm.trans calcG
  rw [←mul_sub,coeff_X_pow_mul',if_pos (le_refl _),Nat.sub_self,origin R N m p hm F tag Z head,map_add] at h
  simp only [body_orb_C,coeff_zero_eq_constantCoeff_apply,constantCoeff_C,cord_apply,left_hit] at h
  have side (D:Ink (Woods G (coarse R m p))):
      MvPolynomial.eval (profile R m p F x z) (constantCoeff (holdUp (Active G F) D))=
      MvPolynomial.eval (flatten x) (coeff 0 D):=by
    rw [←coeff_zero_eq_constantCoeff_apply,holdUp,coeff_map]
    change MvPolynomial.eval (Sum.elim z (flatten x)) (MvPolynomial.rename Sum.inr (coeff 0 D))=_
    rw [MvPolynomial.eval_rename]
    rfl
  rw [side] at h
  exact h

include head cash width draw low high in
theorem original (well:Bulk.Well Q):
    Symmetry.price (model R N m p hm) F tag x-Symmetry.price (model R N m p hm) F tag y=
      -((MvPolynomial.eval (flatten x) (coeff 0 (quadratic R N m p))-
         MvPolynomial.eval (flatten y) (coeff 0 (quadratic R N m p))):ℝ):=by
  have a:=one R N m p hm F tag Z head Q cash cap width draw low high x well
  have b:=one R N m p hm F tag Z head Q cash cap width draw low high y well
  dsimp only at a b
  unfold Symmetry.price
  norm_cast
  linarith only [a,b]

end YM.Integration.WilsonVacuumPreResetDepositedInfrared
