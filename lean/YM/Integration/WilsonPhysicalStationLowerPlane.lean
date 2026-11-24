import YM.Integration.WilsonPhysicalStationFactoryGerm
import YM.OPE.Columns.Limit
import YM.OPE.ElementaryLog

/-! Transport the enrolled lower engineering fields before rescaling any leg.
The two endpoints retain their actual bare subtractions in the same factory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationLowerPlane
open Function Filter RG Wilson MergeProof Labels Source Lattice OPE
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationFactoryGerm
open scoped BigOperators Classical Topology
variable {G:Gauge} (R:Run G) (d N p:ℕ)
local notation "C" => R.family
local notation "K" => R.family.factory d N p
local notation "F₀" => R.family.labels.level d
local notation "μ" => (F₀).coeffSize

theorem refiles (y z:R.family.label d) (i:ℕ) :
    (incoming R d N p (y-(K).terminal z) i).x =
      Columns.trace (C) d N p i ((K).terminal.symm y-z) := by
  unfold incoming Columns.trace
  rw [map_sub, LinearEquiv.symm_apply_apply]

variable {f:Extraction.Order} {S:Table R.family.book} (fac:Facilities R.family f S)

include fac in
theorem original (y:R.family.label d) (e m k:ℕ) (he:e<d)
    (hm:(C).ref d ≤ m) (hkm:m ≤ k) (hk:k ≤ N) :
    ∃ z u:R.family.label d,
      Columns.low (F₀) e z=z ∧ Columns.low (F₀) e u=u ∧
      Columns.low (F₀) e (incoming R d N p (y-(K).terminal z) k).x=0 ∧
      Columns.low (F₀) e (incoming R d N p (y-(K).terminal (z+u)) m).x=0 ∧
      μ (incoming R d N p (y-(K).terminal z) k).x ≤ 
        (1+((C).path.levels.params k).columns)*μ (incoming R d N p y k).x ∧
      Columns.gel (C).path.levels m * μ (incoming R d N p (y-(K).terminal (z+u)) m).x ≤ 
        Columns.gel (C).path.levels k * ((C).S.a m/(C).S.a k)^(d-(e+1)) *
          μ (incoming R d N p (y-(K).terminal z) k).x := by
  obtain ⟨_,_,_,budget⟩:=fac.purchase
  let T:=budget.toTableTickets
  let v := (K).terminal.symm y
  obtain ⟨z,hz,zeroK,fine⟩ := Columns.cancel (p:=p) T R.makes v he (hm.trans hkm) hk
  obtain ⟨u,hu,zeroM,coarse⟩ :=
    Columns.quotient_between (p:=p) T R.makes (v-z) he hm hkm hk zeroK
  refine ⟨z,u,hz,hu,?_,?_,?_,?_⟩
  · rw [refiles]; exact zeroK
  · rw [refiles,← sub_sub]; exact zeroM
  · rw [refiles]; exact fine
  · rw [refiles,refiles,← sub_sub]; exact coarse

end YM.Integration.WilsonPhysicalStationLowerPlane
end
