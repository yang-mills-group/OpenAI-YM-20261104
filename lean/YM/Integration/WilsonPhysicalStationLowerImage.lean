import YM.Integration.WilsonPhysicalStationLowerPlane

/-! Physical image of the subtracted plane on the same ordered Wilson tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationLowerImage
open Push.RelayDifference
open Function Filter RG Wilson Labels Source Lattice OPE Next.Extract
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Spec.Final R.family f S) (fac:Facilities R.family f S)

include fac in
theorem original (d e:ℕ) (he:e<d) (u:Cutoffs → R.family.label d) {b:Filter Cutoffs} [b.NeBot]
    (ordered:b ≤ f.fuse) (lower:∀ᶠ i in b, Columns.low (R.family.labels.level d) e (u i)=u i)
    (v:R.family.label d) (arrived:Tendsto (fun i:Cutoffs=> (R.family.factory d i.1 i.2).terminal (u i)) b (𝓝 v)) :
    S.project d v ∈ LinearMap.range (F.sector.derivatives.rise he.le) := by
  obtain ⟨_,_,_,budget⟩:=fac.purchase
  obtain ⟨_,_,_,_,same⟩:=fac.along
  apply Columns.limit_lower budget.toTableTickets fac.simpleGate same F.phase.transport.injection
    (fun i:Cutoffs=> (R.family.factory d i.1 i.2).terminal (u i)) v he ordered _ arrived
  simpa only [LinearEquiv.symm_apply_apply] using lower

include fac in
theorem bounded (d e:ℕ) (he:e<d) (u:Cutoffs → R.family.label d) {b:Filter Cutoffs} [b.NeBot]
    (ordered:b ≤ f.fuse) (lower:∀ᶠ i in b, Columns.low (R.family.labels.level d) e (u i)=u i)
    (M:ℝ) (bill:∀ᶠ i in b, ‖(R.family.factory d i.1 i.2).terminal (u i)‖ ≤ M) :
    ∃ l:Filter Cutoffs, l ≤ b ∧ l.NeBot ∧ ∃ v:R.family.label d,
      Tendsto (fun i:Cutoffs=> (R.family.factory d i.1 i.2).terminal (u i)) l (𝓝 v) ∧
        S.project d v ∈ LinearMap.range (F.sector.derivatives.rise he.le) := by
  obtain ⟨l,hl,hn,v,hv⟩:=finite_extract (𝓛:=b)
    (fun i:Cutoffs=> (R.family.factory d i.1 i.2).terminal (u i)) M bill
  letI:=hn
  exact ⟨l,hl,hn,v,hv,original R F fac d e he u (hl.trans ordered) (lower.filter_mono hl) v hv⟩

end YM.Integration.WilsonPhysicalStationLowerImage
end
