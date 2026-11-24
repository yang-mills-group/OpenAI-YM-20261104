import YM.Integration.WilsonPhysicalStationMixedNamedProbe
import YM.Integration.WilsonPhysicalStationMixedRegisteredRight
/-! Each original named right field is expanded at its own location inside the same
linear Wilson or Maxwell reading. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedNamedAmounts
open Function Filter Lattice Wilson RG Source Cells Finset Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationThermalRanks (probe)
open Further.CorrectedLift (ladder)
open scoped Classical BigOperators
open WilsonPhysicalStationMixedNamedProbe (coefficient)
variable {G:Gauge}(R:Run G)(B:Deck G)(e:ℕ)
local notation "I"=>Glyph B e
local notation "F₀"=>R.family.labels.level e

theorem original (L:I→(standard R.family).Field e→ₗ[ℂ]ℂ)(c:I→ℂ):
    (∑j,c j*L j (named R B e j))=
      ∑t:I×(F₀).Index,(c t.1*coefficient R B e t.1 t.2)*L t.1 (probe R.family t.2 1 0):=by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [WilsonPhysicalStationMixedNamedProbe.measured R B e (L j) j,Finset.mul_sum]
  simp only [smul_eq_mul,mul_assoc]

open Next.Rank Next.Rank.Tapes Next.Rank.Tapes.West MergeProof.East Trace.Physical.GermGraph Next.UVStress Trace Trace.Pilot
open WilsonPhysicalStationMixedBilledPort (base)
variable {D h:ℕ}(A:Vane R.family D)(dr:e<D+1)(N p k:ℕ)
theorem registered (o:Glyph B e→Fin 2 → Lattice.Cover) (Y:R.family.label h)(c:I→ℂ):
    (∑j,c j*WilsonPhysicalStationMixedListener.value R N p k (o j) Y (A.wheel.atCut (N,p) ⟨e,dr⟩ (named R B e j)))=
      ∑t:I×(F₀).Index,(c t.1*coefficient R B e t.1 t.2)*WilsonPhysicalStationMixedListener.value R N p k (o t.1) Y
        (A.wheel.atCut (N,p) ⟨e,dr⟩ (probe R.family t.2 1 0)):=by
  let L (i:I): (standard R.family).Field e→ₗ[ℂ]ℂ:=
    WilsonPhysicalStationMixedRegisteredRight.registered R A ⟨e,dr⟩ N p k (o i) Y
  have seen(i:I)(z:(standard R.family).Field e): L i z=
      WilsonPhysicalStationMixedListener.value R N p k (o i) Y (A.wheel.atCut (N,p) ⟨e,dr⟩ z):=
    WilsonPhysicalStationMixedRegisteredRight.reading R A ⟨e,dr⟩ N p k (o i) Y z
  calc
    (∑j:I,c j*WilsonPhysicalStationMixedListener.value R N p k (o j) Y (A.wheel.atCut (N,p) ⟨e,dr⟩ (named R B e j)))
      =∑j:I,c j*L j (named R B e j):=Finset.sum_congr rfl (fun j _=>congrArg (fun z:ℂ=>c j*z) (seen j (named R B e j)).symm)
    _=∑t:I×(F₀).Index,(c t.1*coefficient R B e t.1 t.2)*L t.1 (probe R.family t.2 1 0):=original R B e L c
    _=∑t:I×(F₀).Index,(c t.1*coefficient R B e t.1 t.2)*WilsonPhysicalStationMixedListener.value R N p k (o t.1) Y
        (A.wheel.atCut (N,p) ⟨e,dr⟩ (probe R.family t.2 1 0)):=Finset.sum_congr rfl (fun t _=>
          congrArg (fun z:ℂ=>(c t.1*coefficient R B e t.1 t.2)*z) (seen t.1 (probe R.family t.2 1 0)))

theorem wick (x:I→Points 2)(a:(R.family.labels.level h).Index)(c:I→ℂ):
    (∑j,c j*base R h (named R B e j) (x j) a)=
      ∑t:I×(F₀).Index,(c t.1*coefficient R B e t.1 t.2)*base R h (probe R.family t.2 1 0) (x t.1) a:=by
  simpa only [WilsonPhysicalStationMixedRegisteredRight.standing] using
    original R B e (fun j=>WilsonPhysicalStationMixedRegisteredRight.free R h e (x j) a) c

end YM.Integration.WilsonPhysicalStationMixedNamedAmounts
end
