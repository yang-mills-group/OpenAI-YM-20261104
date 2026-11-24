import YM.Integration.WilsonPhysicalStationMixedWickMeasured
import YM.Integration.WilsonPhysicalStationMixedListener
import YM.Integration.WilsonPhysicalStationThermalCoordinates
import YM.Integration.WilsonPhysicalStationLowerReceiver

/-! Expand the original fitted left field in the mixed two-point measurement
at its actual cutoff. The physical and Maxwell readings use the same ballot. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPortfolio
open Filter Finset Function Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace
open PhysicalNext.Repeat.Legato Next.Rank.Price Maxwell.Free
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationThermalCoordinates (word)
open WilsonPhysicalStationMixedListener (seated port)
open Spec OPE PhysMS Trace.Pilot Next.UVStress GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationMixedWickTest (fields)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {m N p:ℕ}(V:Vane R.family m)(dl dr:Fin (m+1))(checked:V.checked f H m)(fine:V.k<N)
    (j:ℕ)(o:Fin 2 → Cover)(y:Points 2)(z:(standard R.family).Field dr)
local notation "L₀" => R.family.label dl
local notation "C₀" => standard R.family

def allowance:(C₀).Field dl→ₗ[ℂ]ℂ:=
  ((C₀).classMoment (C₀) (grades dl dr) y).toLinearMap (fields R.family (0:L₀) z) (0:Fin 2)

theorem evaluated (x:L₀):allowance R dl dr y z ((C₀).project dl x)=reference R.family x z y:=by
  change (C₀).classMoment (C₀) (grades dl dr) y (Function.update (fields R.family (0:L₀) z) 0 _) = _
  apply congrArg ((C₀).classMoment (C₀) (grades dl dr) y)
  funext i
  fin_cases i <;> simp [WilsonPhysicalStationMixedWickTest.fields]

def balance:L₀→ₗ[ℂ]ℂ:=
  let projected:L₀→ₗ[ℂ](C₀).Field dl:=(C₀).project dl
  let measured:L₀→ₗ[ℂ]ℂ:=(port R dl N p j o (V.wheel.atCut (N,p) dr z)).comp (word R V dl (p:=p) checked fine)
  measured-(allowance R dl dr y z).comp projected

theorem incurred (x:L₀):
    balance R V dl dr (p:=p) checked fine j o y z x=
    cell R V dl dr (p:=p) checked fine j o x z-reference R.family x z y:=by
  change port R dl N p j o (V.wheel.atCut (N,p) dr z) (raw R V dl (p:=p) checked fine x) -
      allowance R dl dr y z ((C₀).project dl x)=_
  rw [seated,evaluated]

theorem original (x:L₀):
    cell R V dl dr (p:=p) checked fine j o x z-reference R.family x z y=
      ∑i,x i*(cell R V dl dr (p:=p) checked fine j o (Pi.single i 1) z -
        reference R.family (Pi.single i 1) z y):=by
  let pay:=balance R V dl dr (p:=p) checked fine j o y z
  have split:(∑i,x i • (Pi.single i 1:L₀))=x:=by
    funext i
    simp [Finset.sum_apply,Pi.single_apply]
  change _=∑i,x i*_
  simp_rw [←incurred]
  change pay x=_
  conv_lhs => rw [←split,map_sum]
  simp only [map_smul,smul_eq_mul,pay]

theorem priced (x:L₀)(scale:ℝ)(hs:0 ≤ scale)(cost:(R.family.labels.level dl).Index→ℝ)
    (bills:∀i,x i≠0 → scale*‖cell R V dl dr (p:=p) checked fine j o (Pi.single i 1) z -
      reference R.family (Pi.single i 1) z y‖≤cost i):
    scale*‖cell R V dl dr (p:=p) checked fine j o x z-reference R.family x z y‖≤
      ∑i,‖x i‖*cost i:=by
  rw [original]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hs).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _=>?_
  by_cases live:x i=0
  · simp only [live,zero_mul,norm_zero,mul_zero,le_refl]
  · rw [norm_mul,mul_left_comm]
    exact mul_le_mul_of_nonneg_left (bills i live) (norm_nonneg _)

end YM.Integration.WilsonPhysicalStationMixedWickPortfolio
end
