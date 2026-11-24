import YM.Integration.WilsonPhysicalStationMixedNamedProbe
import YM.Integration.WilsonPhysicalStationMixedWickRespondents
import YM.Integration.WilsonPhysicalStationThermalBasisOffice
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedNativePorts
open Function Filter Lattice Wilson RG Source Cells Finset Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationMixedNamedProbe (coefficient)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){S:Table R.family.book}(U:tower S)(B:Deck G)(e:ℕ)(j:Glyph B e)
    (x:Points 2){h:ℕ}(Y:S.Field h)(T:ℝ)(q:ℕ)
def fare (j:Glyph B e)(cost:(R.family.labels.level e).Index→ℝ):ℝ:=∑b,‖coefficient R B e j b‖*cost b
theorem original (positive:0 ≤ T)(cost:(R.family.labels.level e).Index→ℝ)
    (seated:∀b,‖WilsonPhysicalStationLowerReceiver.ear R (S:=S) x (U e (probe R.family b 1 0)) Y‖*T^(rank R.family e b) ≤ T^q*cost b):
    ‖WilsonPhysicalStationLowerReceiver.ear R (S:=S) x (U e (named R B e j)) Y‖*T^j.2.1.val ≤ T^q*fare R B e j cost:=by
  let read:=WilsonPhysicalStationMixedWickRespondents.native R U (r:=e) x ((U h).symm Y)
  have actual (z:(standard R.family).Field e):read z=WilsonPhysicalStationLowerReceiver.ear R x (U e z) Y:=by
    dsimp only [read]
    rw [WilsonPhysicalStationMixedWickRespondents.actual,LinearEquiv.apply_symm_apply]
  rw [←actual,WilsonPhysicalStationMixedNamedProbe.original R B e j,map_sum]
  simp only [map_smul,smul_eq_mul]
  refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg positive _)).trans ?_
  rw [Finset.sum_mul,fare,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  by_cases empty:coefficient R B e j b=0
  · simp [empty]
  · have degree:rank R.family e b=j.2.1.val:=congrArg Prod.snd (WilsonPhysicalStationMixedNamedProbe.grades R B e j b empty)
    rw [norm_mul,mul_assoc,actual,←degree]
    exact (mul_le_mul_of_nonneg_left (seated b) (norm_nonneg _)).trans_eq (by ring)
end YM.Integration.WilsonPhysicalStationMixedNativePorts
end
