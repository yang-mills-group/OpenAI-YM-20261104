import YM.Integration.WilsonPhysicalNamedVaneBasis
import YM.Integration.WilsonPhysicalStationThermalPortfolio
/-! Neutral genuine thermal probes synthesize the physical named basis on its native
homogeneous engineering and curvature coordinates, including the zero vote. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedNamedProbe
open Function Filter Lattice Wilson RG Source Cells Finset Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationThermalRanks (probe)
open Further.CorrectedLift (ladder)
open scoped Classical BigOperators
variable {G:Gauge}(C:Family G){d:ℕ}
theorem neutral (b:(C.labels.level d).Index):
    probe C b 1 0=(standard C).project d (Pi.single b 1):=by
  change (Bel C.book).mirror (Maxwell.Free.spin_free C.labels) d 1 _=_
  exact Table.mirror_one _ _ _ _

variable (R:Run G)(B:Deck G)(e:ℕ)
local notation "I"=>Glyph B e
local notation "F₀"=>R.family.labels.level e

def coefficient (j:I)(b:(F₀).Index):ℂ:=ladder R.family e (named R B e j) b
theorem grades (j:I)(b:(F₀).Index)(live:coefficient R B e j b≠0):
    (F₀).grades b=(j.1.val,j.2.1.val):=WilsonPhysicalNamedVaneBasis.original R B j b live

theorem original (j:I):
    named R B e j=∑b,(coefficient R B e j b) • probe R.family b 1 0:=by
  simpa only [neutral,coefficient] using WilsonPhysicalStationThermalPortfolio.columns R.family (named R B e j)

theorem measured {X:Type*}[AddCommMonoid X][Module ℂ X]
    (U:(standard R.family).Field e→ₗ[ℂ]X)(j:I):
    U (named R B e j)=∑b,(coefficient R B e j b) • U (probe R.family b 1 0):=by
  rw [original R B e j,map_sum]
  exact Finset.sum_congr rfl (fun b _=>U.map_smul _ _)

theorem restored {T:ℝ}(Q:ℕ)(c:I→ℂ)(roof:I→ℝ)
    (sale:∀j,‖c j‖*T^Q≤roof j*T^j.2.1.val)(j:I)(b:(F₀).Index):
    ‖c j*coefficient R B e j b‖*T^Q≤(roof j*‖coefficient R B e j b‖)*T^((F₀).grades b).2:=by
  by_cases zero:coefficient R B e j b=0
  · simp only [zero,mul_zero,norm_zero,zero_mul,le_refl]
  have eq:=congrArg Prod.snd (grades R B e j b zero)
  calc _=(‖c j‖*T^Q)*‖coefficient R B e j b‖:=by rw [norm_mul];ring
       _≤(roof j*T^j.2.1.val)*‖coefficient R B e j b‖:=mul_le_mul_of_nonneg_right (sale j) (norm_nonneg _)
       _=_:=by rw [eq];ring

end YM.Integration.WilsonPhysicalStationMixedNamedProbe
end
