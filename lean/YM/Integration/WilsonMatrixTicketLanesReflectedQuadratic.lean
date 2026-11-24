import YM.Integration.WilsonMatrixTicketLanesReflectedGauge
import YM.FVA2.Shipment

/-! The first homogeneous insertion in the actual FVA2 Gaussian integration, with its retained ledger. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReflectedQuadratic
open Function Filter MeasureTheory PowerSeries
open PertExtension PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial PertExtension.GaussianScore
open FormalOPE.RG10 FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.OpenSlots FormalOPE.RG10.OpenSlots.Quadratic
open scoped Topology Classical BigOperators
variable {E K : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup K] [NormedSpace ℝ K] [MeasurableSpace E] [BorelSpace E]
    (Q : Quadratic (E×K)) (μ : Measure E) [Measure.IsAddHaarMeasure μ] (hp : (core Q).RespectsPrice)
    (W : Ticket (E×K)) (hw : incline W) (U : Ticket (E×K))
include hw

/-- Evaluation at zero holds the *coarse field* at zero while retaining all inner variables. -/
theorem vacuum : coeff 0 (Stack.read 0 (Q.fit μ hp U W)) = hp.inner.average μ (fun x=>(constantCoeff U).val (x,0)) := by
  have funded : incline (Return (Q.uptake μ hp W)) := investment (Q.upright μ hp hw)
  rw [Quadratic.fit,Stack.reading_term,coeff_zero_eq_constantCoeff_apply,map_mul,funded,mul_one]
  change reading 0 ((Q.integrateP μ hp) (coeff 0 (W*U)))=_
  rw [coeff_zero_eq_constantCoeff_apply,map_mul,hw,one_mul]
  change (Q.integrateP μ hp (constantCoeff U)).val 0=_
  rw [Quadratic.integrateP_display];simp only [map_zero,add_zero]

/-- All perturbative terms in the inherited action remain in `W`. Its unit constant gives the
original conditional Gaussian at the first possible coefficient, for any homogeneous source. -/
theorem initial (r : ℕ) : coeff r (Stack.read 0 (Q.fit μ hp (X^r*U) W)) = hp.inner.average μ (fun x=>(constantCoeff U).val (x,0)) := by
  have shift : Q.fit μ hp (X^r*U) W = X^r*Q.fit μ hp U W := by
    unfold Quadratic.fit
    rw [mul_left_comm W (X^r),show Q.uptake μ hp (X^r*(W*U))=X^r*Q.uptake μ hp (W*U) from
      FVA2.Shipment.transferX (Q.integrateP μ hp).toAddMonoidHom (W*U),mul_assoc]
  rw [shift,map_mul,map_pow,show Stack.read (0:K) X=X from PowerSeries.map_X _,coeff_X_pow_mul',if_pos (le_refl r),Nat.sub_self]
  exact vacuum Q μ hp W hw U

end YM.Integration.WilsonMatrixTicketLanesReflectedQuadratic
