import YM.Integration.PhysicalAffineScalarStationary
import YM.Integration.OriginalMarkedHeatCovariance

/-! The independently submitted full-path response has the original Wilson
and blocking Hessian, in each signed channel separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedFullQuadratic
open Function Filter Lattice Wilson RG RG.Patch Pressure Pressure.Stores Pressure.Tube
open Precision Exterior Tree Push Push.SectorMeasure Push.SectorMeasure.Oriented
open MeasureTheory Matrix Bid Work.F03 FreeResolvent FreeResolvent.Affine
open Next.Fluctuations Next.SectorChange Progress.StationaryScenes PhysicalNext.Repeat
open AnalyticNext.ConnectedActivity.Aff PhysicalAffineScalarStationary
open scoped Topology BigOperators Classical RealInnerProductSpace
open private norm_axis from YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Station

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S)

private theorem noise (x : LogField G f) :
    (∑ i, ‖zLin S x 0 i‖^2) = S.kernel.penalty *
      ∑ i, inner ℝ (bills S x i) (bills S x i) := by
  rw [← (Work.E03.poleEquiv c).sum_comp (fun i => inner ℝ (bills S x i) (bills S x i)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change ‖Real.sqrt S.kernel.penalty • (0-bills S x (pole i))‖^2 = _
  rw [zero_sub,norm_smul,norm_neg,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow,Real.sq_sqrt S.kernel.penalty_pos.le,real_inner_self_eq_norm_sq]
  rfl

theorem chamber {P : Teller G} {A B : Bed} (path : Alongside A B T) (fund : P.Funds S T)
    (k : S.Choices) (s : Signed) (v : Vec G f 1) :
    (∑ i : Twin f ⊕ Bond c, ‖PhysicalAffineScalarJets.slope T k all 0 v (s,i)‖^2) =
      dotProduct v (fullMatrix G S A.metric *ᵥ v) := by
  obtain ⟨_,_,bounds,_⟩ := fund.feeds
  obtain ⟨_,_,_,_,floor,_⟩ := path.budgets
  rw [←fund.high] at bounds
  let x := decode v
  have flat : flatten x = v := rfl
  have face : counted (xLin T.high T.up (orient s x)) = gaugeFiscal A x x := by
    rw [← norm_axis A T.high T.up (orient s x) bounds path.inbound floor,
      orient_pulls, path.old s x x]
  have spring := z_energy (S:=S) s x 0 (fund.knobs.symm ▸ fund.kernel)
  rw [orient_zero] at spring
  rw [←flat, fiscal_eq]
  simp only [flat]
  simp_rw [PhysicalAffineScalarStationary.flat_slope T path fund k]
  rw [Fintype.sum_sum_type]
  change counted (xLin T.high T.up (orient s x)) + (∑ i, ‖zLin S (orient s x) 0 i‖^2) =
    curlCharge A.metric x x + _
  rw [face,spring,noise]
  rfl

end YM.Integration.WilsonOriginalSignedFullQuadratic
