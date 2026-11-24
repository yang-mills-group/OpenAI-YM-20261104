import YM.Integration.WilsonMatrixOriginalDeckPath
import YM.Integration.WilsonMatrixOriginalDeckCapacity

/-! Uniform forward subproduct bounds on the full measured, independently indexed field space. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckRelative
open Function Filter Set Finset Extraction Extraction.Order Spec Climb OPE OPE.Levy RG11.Fields
open Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater FVA2 FVA2.ColorCode
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato Pert.RawLabels PhysMS Trace.Pilot
open WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckColumns WilsonMatrixOriginalDeckCapacity
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} {C:Family G} {S:Table C.book} {f:Extraction.Order}
variable (B:Deck G) (F:Spec.Final C f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

def amount {I:Type*} [Fintype I] (A:Matrix I I ℂ) : ℝ := ∑ i,∑ j,‖A i j‖

private def basisCost : ℝ :=
  let E := WilsonMatrixOriginalDeckColumns.basis C B h
  ∑ i,∑ j,‖(E.coord i).toContinuousLinearMap‖*‖E j‖

private theorem represented (r s k:ℝ) (paid:∀z,capacity h J r z≤k*capacity h J s z) :
    amount (change B J h r s) ≤ basisCost (C:=C) B h * k := by
  classical
  let E := WilsonMatrixOriginalDeckColumns.basis C B h
  unfold amount basisCost
  rw [sum_mul]
  apply sum_le_sum
  intro i _
  rw [sum_mul]
  apply sum_le_sum
  intro j _
  let v := (J r h).symm (J s h (E j))
  have run : ‖v‖≤k*‖E j‖ := by simpa only [v,capacity,LinearEquiv.symm_apply_apply] using paid (J s h (E j))
  change ‖(E.coord i) v‖≤(‖(E.coord i).toContinuousLinearMap‖*‖E j‖)*k
  calc ‖(E.coord i) v‖ ≤ ‖(E.coord i).toContinuousLinearMap‖*‖v‖ := (E.coord i).toContinuousLinearMap.le_opNorm v
       _ ≤ ‖(E.coord i).toContinuousLinearMap‖*(k*‖E j‖) := mul_le_mul_of_nonneg_left run (E.coord i).toContinuousLinearMap.opNorm_nonneg
       _ = _ := by ring

/-- The forward rate has arbitrarily small exponent for every pair of lengths simultaneously.
In the inverse direction the original field height contributes its full engineering exponent. -/
theorem original (lead:Leading F J) : ∃K:ℝ,1≤K ∧ ∀η:ℝ,0<η → ∀ᶠr in trail,∀a∈Set.Ioc (0:ℝ) 1,
    amount (change B J h r (a*r))≤K*a^(-η) ∧ amount (change B J h (a*r) r)≤K*a^(-(h:ℝ)-η) := by
  obtain ⟨k,_,cost⟩ := WilsonMatrixOriginalDeckCapacity.original F h J lead
  let K := max 1 (basisCost (C:=C) B h * k)
  refine ⟨K,le_max_left ..,?_⟩
  intro η hη
  filter_upwards [cost η hη] with r pay a ha
  constructor
  · calc amount (change B J h r (a*r)) ≤ basisCost (C:=C) B h*(k*a^(-η)) :=
           represented B J h r (a*r) _ fun z=>(pay a ha z).2
         _ = (basisCost (C:=C) B h*k)*a^(-η) := (mul_assoc ..).symm
         _ ≤ K*a^(-η) := mul_le_mul_of_nonneg_right (le_max_right ..) (Real.rpow_nonneg ha.1.le _)
  · calc amount (change B J h (a*r) r) ≤ basisCost (C:=C) B h*(k*a^(-(h:ℝ)-η)) :=
           represented B J h (a*r) r _ fun z=>(pay a ha z).1
         _ = (basisCost (C:=C) B h*k)*a^(-(h:ℝ)-η) := (mul_assoc ..).symm
         _ ≤ K*a^(-(h:ℝ)-η) := mul_le_mul_of_nonneg_right (le_max_right ..) (Real.rpow_nonneg ha.1.le _)

end YM.Integration.WilsonMatrixOriginalDeckRelative
