import YM.Integration.WilsonPhysicalStationLowerPlane
import YM.Integration.WilsonPhysicalStationRawReading

/-! The lower graph inside the very table on which the thermal words are read. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationFiledSlope
open Work.G08
open Function Filter RG Wilson MergeProof Labels Source Lattice OPE
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph PhysicalNext.Repeat.Legato.Bandage
open WilsonPhysicalStationFactoryGerm (incoming)
open WilsonPhysicalStationRawReading (err eng)
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
    (fac:Facilities R.family f S) {H:(Bel R.family.book).Hierarchy}
    {D:ℕ} (A:Vane R.family D) (d:Fin (D+1)) {N p:ℕ} (e:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "μ" => (F₀).coeffSize
local notation "C₀" => (R.family.path.levels.params A.k).columns
local notation "K₀" => R.family.factory d N p
local notation "T₀" => Columns.trace R.family d N p A.k
local notation "P₀" => Columns.low (F₀) e

def testing (N p:ℕ) : Module.End ℂ (R.family.label d) :=
  (eng R d A.k) • ((A.R N p d).comp ((R.family.factory d N p).terminal.toLinearMap))

theorem fee (check:A.checked f H D) (top:A.k<N) (x:R.family.label d) :
    μ ((T₀) x-testing R A d N p x) ≤ err R A.k* μ ((T₀) x) := by
  have paid:=WilsonPhysicalStationRawReading.original R A d ((K₀).terminal x) (p:=p) check top
  simpa [incoming, Columns.trace, testing] using paid

include fac in
theorem original (check:A.checked f H D) (top:A.k<N) (he:e<d.val)
    (gate:(C₀)*err R A.k ≤ 1/2) (u:R.family.label d) (lower:(P₀) u=u):
    μ ((T₀) u) ≤ 2*(C₀)*μ ((P₀) (testing R A d N p u)) := by
  obtain ⟨_,_,_,budget⟩:=fac.purchase
  let x:=(T₀) u
  let y:=testing R A d N p u
  have cone:=Columns.entire_cone (p:=p) budget.toTableTickets R.makes lower he (check.early d) top.le
  change μ x ≤ (C₀)*μ ((P₀) x) at cone
  have gap:=fee R A d (p:=p) check top u
  change μ (x-y) ≤ err R A.k*μ x at gap
  have identity : (P₀) (x-y)+(P₀) y=(P₀) x:=by rw [map_sub,sub_add_cancel]
  have triangle:=Extra.Histories.Size.add (F₀) ((P₀) (x-y)) ((P₀) y)
  rw [identity] at triangle
  have split:=triangle.trans (add_le_add (Columns.size_low (F₀) e (x-y)) (le_refl _))
  have estimate:=cone.trans (mul_le_mul_of_nonneg_left
    (split.trans (add_le_add gap (le_refl _))) (zero_le_one.trans (R.family.path.levels.params A.k).columns_ge))
  have debit:=mul_le_mul_of_nonneg_right gate (size_nonneg (F₀) x)
  change μ x ≤ 2*(C₀)*μ ((P₀) y)
  linarith only [estimate,debit]

end YM.Integration.WilsonPhysicalStationFiledSlope
end
