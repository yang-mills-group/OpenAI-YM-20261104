import YM.Integration.WilsonPhysicalStationThermalPair
import YM.Integration.WilsonPhysicalStationRawReading

/-! The true finer endpoint, including its fitted-table error, before the
lower engineering graph is transported to the other report. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalStart
open Function Filter Finset Lattice RG Wilson Cells Labels Source Next.Rank Next.Rank.East Next.Rank.Price
open MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationRawReading (err eng)
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationTableJump (table)
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) {N p:ℕ}
    (checked:A.checked f H D) (top:A.k<N)
local notation "F₀" => R.family.labels.level d
local notation "μ" => (F₀).coeffSize
local notation "τ" => shrink R.family A.k N p
local notation "M₀" => Station.mag R.family.path.levels A.b A.k

def entered (x:R.family.label d) : R.family.label d :=
  WilsonPhysicalStationThermalPair.raw R A d (p:=p) checked top x

theorem income (x:R.family.label d) :
    μ (eng R d A.k • A.R N p d (entered R A d (p:=p) checked top x)) =
    ‖eng R d A.k‖*(∑ a,(M₀)^((F₀).grades a).1*(τ)⁻¹^((F₀).grades a).2*‖x a‖) := by
  have filed: A.R N p d (entered R A d (p:=p) checked top x)=
      (F₀).scaled (τ)⁻¹ (weightTag R.family d (M₀) x) :=
    (table R A d (p:=p) checked top).apply_symm_apply _
  rw [filed]
  have hp:=shrink_pos R.family R.makes top.le p
  have hm:=Station.mag_pos R.family.path.levels A.b A.k
  unfold Frame.coeffSize; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  change ‖(eng R d A.k) * (((((τ)⁻¹^((F₀).grades a).2:ℝ):ℂ)) * (((M₀:ℝ):ℂ)^((F₀).grades a).1 * x a))‖=_
  rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr hp.le) _),
    norm_pow,Complex.norm_real,Real.norm_of_nonneg hm.le]
  ring

theorem original (x:R.family.label d) :
    let y:=entered R A d (p:=p) checked top x
    (1-err R A.k)*μ (incoming R d N p y A.k).x ≤
      ‖eng R d A.k‖*(∑ a,(M₀)^((F₀).grades a).1*(τ)⁻¹^((F₀).grades a).2*‖x a‖) := by
  intro y
  let v:=(incoming R d N p y A.k).x
  let b:=eng R d A.k • (A.R N p d y)
  have paid:=WilsonPhysicalStationRawReading.original R A d y (p:=p) checked top
  change μ (v-b) ≤ err R A.k*μ v at paid
  have ht:=Extra.Histories.Size.add (F₀) (v-b) b
  rw [sub_add_cancel] at ht
  rw [← income R A d (p:=p) checked top x]
  change (1-err R A.k)*μ v ≤ μ b
  linarith only [ht,paid]

end YM.Integration.WilsonPhysicalStationThermalStart
end
