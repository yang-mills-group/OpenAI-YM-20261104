import YM.Integration.WilsonPhysicalStationRegisteredFiling
import YM.Integration.WilsonPhysicalStationEndCurrency
import YM.Integration.WilsonPhysicalStationThermalCoordinates

/-! Factor the genuine reported row into its actual engineering, fitted radius
and cutoff-specific thermal powers on the physical table. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationEndpointFactor
open Function Filter Finset Lattice RG Wilson Source Labels Extra.Histories Bid
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph OPE Work.G08
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open WilsonPhysicalStationEndCurrency (row charge)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationFineCorrection (measured)
open WilsonPhysicalStationRegisteredDiagonal (ratio)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) {N p:ℕ}
local notation "F₀" => R.family.labels.level d
local notation "M₀" => Station.mag R.family.path.levels A.b A.k
local notation "u₀" => shrink R.family A.k N p

theorem row_pos (top:A.k≤N) (w q:ℕ):
    0<row R d N p A.k w q (M₀) :=
  mul_pos (mul_pos (pow_pos (R.family.S.a_pos _) _) (pow_pos (inv_pos.mpr (shrink_pos R.family R.makes top p)) _))
    (pow_pos (Station.mag_pos ..) _)

theorem written (top:A.k≤N) (z:R.family.label d) (i:(F₀).Index):
    measured R A d N p z i=
      (row R d N p A.k ((F₀).grades i).1 ((F₀).grades i).2 (M₀):ℂ)*filed R A d N p z i := by
  let w:=((F₀).grades i).1
  let q:=((F₀).grades i).2
  let a:=R.family.S.a A.k
  let u:=(u₀)
  let M:=(M₀)
  let c:=A.R N p d z i
  have hu:(u:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (shrink_pos R.family R.makes top p).ne'
  have hm:(M:ℂ)≠0:=Complex.ofReal_ne_zero.mpr (Station.mag_pos ..).ne'
  change (a:ℂ)^d.val*c= (↑(a^d.val*u⁻¹^q*M^w):ℂ)*((↑(M⁻¹):ℂ)^w*((↑(u^q):ℂ)*c))
  push_cast
  simp only [inv_pow]
  field_simp [hu,hm]

theorem entrance (ca:A.checked f H D) (top:A.k<N) (s:R.family.label d) (i:(F₀).Index):
    measured R A d N p (entered R A d (p:=p) ca top s) i=
      (row R d N p A.k ((F₀).grades i).1 ((F₀).grades i).2 (M₀):ℂ)*s i := by
  have raw:A.R N p d (entered R A d (p:=p) ca top s)=
      (F₀).scaled (u₀)⁻¹ (weightTag R.family d (M₀) s):=
    (WilsonPhysicalStationTableJump.table R A d (p:=p) ca top).apply_symm_apply _
  change (R.family.S.a A.k:ℂ)^d.val*(A.R N p d _ i)=_
  rw [raw]
  change (R.family.S.a A.k:ℂ)^d.val*((↑((u₀)⁻¹^((F₀).grades i).2):ℂ)*(((M₀:ℝ):ℂ)^((F₀).grades i).1*s i))=_
  unfold row
  push_cast
  ring

theorem start (ca:A.checked f H D) (top:A.k<N) (i:(F₀).Index):
    (1-WilsonPhysicalStationRawReading.err R A.k)*
      (F₀).coeffSize (WilsonPhysicalStationFactoryGerm.incoming R d N p
        (entered R A d (p:=p) ca top (Pi.single i 1)) A.k).x ≤
       row R d N p A.k ((F₀).grades i).1 ((F₀).grades i).2 (M₀) := by
  have quoted:=WilsonPhysicalStationThermalStart.original R A d (p:=p) ca top (Pi.single i 1)
  have one :
      (∑ j:(F₀).Index,(M₀)^((F₀).grades j).1*(u₀)⁻¹^((F₀).grades j).2*‖(Pi.single i (1:ℂ):R.family.label d) j‖)=
      (M₀)^((F₀).grades i).1*(u₀)⁻¹^((F₀).grades i).2:=by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Pi.single_eq_of_ne hji]
    · simp
  rw [one] at quoted
  apply quoted.trans_eq
  unfold WilsonPhysicalStationRawReading.eng row
  simp only [norm_pow,Complex.norm_real,Real.norm_of_nonneg (R.family.S.a_pos _).le]
  ring

end YM.Integration.WilsonPhysicalStationEndpointFactor
end
