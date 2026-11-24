import YM.Integration.WilsonVacuumPreResetDepositedGeometric

/-! The physical finite vacuum vertices, including every higher-degree term
of the old Wilson action, on the original true conditional Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedLetters
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 Cumulants FreeResolvent WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo
open WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam Marker Multi Stationary WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetDepositedGeometric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (tag:(step R m p).Choices)(Z:SeriesA G)
variable {T:Type}[DecidableEq T]{J:Census T}(Q:Bulk.Colors J G (fine R m p))
variable (cash:BudgetPoint)(cap:ℕ){σ C:ℝ}(width:0<σ)(draw:Draw Z σ C)
    (low:∀a∈Z,3≤a.grade)(high:∀a∈Z,a.grade≤cap)
    (x:fieldDir G (coarse R m p) 1)(z:Key F G→ℝ)

def exponent :=
  relativeHaar R N m p hm F -
    retool (shift R N m p hm F) (unscaled (step R m p) F (prediction R N m p)
      (filed R N m p Z))

def opened :=
  exponent R N m p hm F Z - PowerSeries.C (constantCoeff (exponent R N m p hm F Z))

theorem leading:constantCoeff (opened R N m p hm F Z)=0:=by simp [opened]

include cash width draw low high in
theorem original (input:Bulk.Well Q)(j:ℕ):
    Cloud.paint z (Assembly.naked (Bulk.stage (model R N m p hm) F x)
      (Bulk.hinge F) (Bulk.geometric (model R N m p hm) F tag (source R m p Z Q cap)) j)=
      (MvPolynomial.eval (profile R m p F x z) (coeff j (opened R N m p hm F Z)):ℝ):=by
  have well:Bulk.Well (source R m p Z Q cap):=by
    exact (QuadraticLocal.Fk.well _ _ (WilsonVacuumPreResetTorusDeposit.legal Z width draw low _) Q input).1
  by_cases hj:j=0
  · subst j
    simp [Assembly.naked,coeff_zero_eq_constantCoeff_apply,leading]
  · let v:=profile R m p F x z
    let u:=retool (shift R N m p hm F) (unscaled (step R m p) F (prediction R N m p)
      (filed R N m p Z))
    let d:=relativeHaar R N m p hm F
    have geom:=WilsonVacuumPreResetDepositedGeometric.original R N m p hm F tag Z Q cash cap
      width draw low high x z well (j+2)
    change _ = MvPolynomial.eval v (coeff (j+2) (X^2*u-X^2*d)) at geom
    rw [←mul_sub,coeff_X_pow_mul',if_pos (Nat.le_add_left 2 j),Nat.add_sub_cancel_right] at geom
    rw [Assembly.readingVacuum]
    change ((if j=0 then 0 else -Assembly.jet (Bulk.geometric (model R N m p hm) F tag
      (source R m p Z Q cap)) (j+2) (Bulk.translated (model R N m p hm) F x z):ℝ):ℂ)=_
    rw [if_neg hj,geom]
    apply congrArg Complex.ofReal
    change -(MvPolynomial.eval v (coeff j (u-d)))=
      MvPolynomial.eval v (coeff j ((d-u)-PowerSeries.C _))
    simp only [map_sub,coeff_C,hj,if_false,sub_zero,neg_sub]

end YM.Integration.WilsonVacuumPreResetDepositedLetters
