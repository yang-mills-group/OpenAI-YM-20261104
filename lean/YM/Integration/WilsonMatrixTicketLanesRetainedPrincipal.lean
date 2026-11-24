import YM.Integration.WilsonMatrixTicketLanesReflectedGauge
import YM.FVA2.Shipment

/-! Original homogeneous conditional coefficients at every prescribed retained field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesRetainedPrincipal
open Function Filter MeasureTheory PowerSeries
open PertExtension PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial PertExtension.GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.OpenSlots FormalOPE.RG10.OpenSlots.Quadratic
open scoped Topology Classical BigOperators
variable {E K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [MeasurableSpace E] [BorelSpace E]
    (Q : Quadratic (E×K)) (μ : Measure E) [Measure.IsAddHaarMeasure μ] (hp : (core Q).RespectsPrice)
    (y : K) (W : Ticket (E×K)) (hw : incline W) (U : Ticket (E×K))
include hw

/-- The old action has unit constant after the genuine Gaussian change of field. -/
theorem vacuum : coeff 0 (Stack.read y (Q.fit μ hp U W)) = hp.inner.average μ (fun x=>(constantCoeff U).val (x+Q.skew hp y,y)) := by
  have funded : incline (Return (Q.uptake μ hp W)) := investment (Q.upright μ hp hw)
  rw [Quadratic.fit,Stack.reading_term,coeff_zero_eq_constantCoeff_apply,map_mul,funded,mul_one]
  change reading y ((Q.integrateP μ hp) (coeff 0 (W*U)))=_
  rw [coeff_zero_eq_constantCoeff_apply,map_mul,hw,one_mul]
  change (Q.integrateP μ hp (constantCoeff U)).val y=_
  exact Quadratic.integrateP_display Q μ hp _ y

/-- All perturbative terms in the inherited action remain in `W`. Its unit constant gives the
original conditional Gaussian at the first possible coefficient, for any homogeneous source. -/
theorem initial (r : ℕ) : coeff r (Stack.read y (Q.fit μ hp (X^r*U) W)) = hp.inner.average μ (fun x=>(constantCoeff U).val (x+Q.skew hp y,y)) := by
  have shift : Q.fit μ hp (X^r*U) W = X^r*Q.fit μ hp U W := by
    unfold Quadratic.fit
    rw [mul_left_comm W (X^r),show Q.uptake μ hp (X^r*(W*U))=X^r*Q.uptake μ hp (W*U) from
      FVA2.Shipment.transferX (Q.integrateP μ hp).toAddMonoidHom (W*U),mul_assoc]
  rw [shift,map_mul,map_pow,show Stack.read y X=X from PowerSeries.map_X _,coeff_X_pow_mul',if_pos (le_refl r),Nat.sub_self]
  exact vacuum Q μ hp y W hw U

omit hw in
theorem covariance_translate {A : Type} [CommRing A] [Algebra ℝ A]
    (B : A →ₗ[ℝ] ℝ) (unit : B 1=1) (a b : A) (s t : ℝ) :
    B ((a+s•1)*(b+t•1))-B (a+s•1)*B (b+t•1) = B (a*b)-B a*B b := by
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul,map_add,map_smul,
    smul_eq_mul,unit,mul_one];ring

end YM.Integration.WilsonMatrixTicketLanesRetainedPrincipal
