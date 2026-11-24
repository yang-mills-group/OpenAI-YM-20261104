import YM.Integration.WilsonPhysicalStationMixedWickNamedGram
import YM.Integration.WilsonMovingForkReporterMixedHouses

/-! Complete lower electrodes and additional fields on one original attendance. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickPlacement
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical


open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonMovingForkReporterMixedHouses (Held)
open WilsonPhysicalStationMixedBasisSale (Sold)
open WilsonPhysicalStationMixedWickNamedGram (electrode)
open scoped Classical

variable {G:Gauge}(R:Run G)(e:ℕ)(K:Set (Points 2))(compact:IsCompact K)(clear:K⊆conf 2)
    {n:ℕ}(extra:Fin n→Slot R.family)
def quantity (n:ℕ)(_:ℕ):ℕ:=Fintype.card ((R.family.labels.level e).Index ⊕ Fin n)
def menu (D:ℕ)(s:Fin (quantity R e n D)):Slot R.family:=
  Sum.elim (electrode R e K compact clear) extra ((Fintype.equivFin _).symm s)

theorem lower (D:ℕ)(b:(R.family.labels.level e).Index):∃s,menu R e K compact clear extra D s=electrode R e K compact clear b:=by
  refine ⟨Fintype.equivFin _ (Sum.inl b),?_⟩
  simp [menu]
theorem additional (D:ℕ)(i:Fin n):∃s,menu R e K compact clear extra D s=extra i:=by
  refine ⟨Fintype.equivFin _ (Sum.inr i),?_⟩
  simp [menu]

variable (B:Binding R.family)(O:HaarBudget G)(χ:ChartRatio G)
    {f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}(price:ℕ→ℝ){D m:ℕ}
    (P:Tapes.Panel D)(V:Vane R.family m)(checked:V.checked f H m)

theorem occupied {qty:ℕ→ℕ}{ledger:∀d,Fin (qty d)→Slot R.family}
    (held:Held (f:=f) R B O χ H price qty ledger P V)(A:Slot R.family)
    (address:∃s,ledger D s=A)(hl:A.left < m+1)(hr:A.right < m+1)
    (width:100*(max A.left A.right+1)≤D):Sold R V A hl hr D checked:=by
  obtain ⟨_,ink,ripe,registered⟩:=held
  obtain ⟨s,hs⟩:=address
  subst A
  exact WilsonPhysicalStationMixedBasisSale.original R B O χ V _ hl hr checked P ink ripe (registered s width)

theorem original
    (held:Held (f:=f) R B O χ H price (quantity R e n) (menu R e K compact clear extra) P V)
    (he:e < m+1)(lowerWidth:100*(e+1)≤D):
    (∀b,Sold R V (electrode R e K compact clear b) he he D checked) ∧
    ∀i:Fin n,∀(hl:(extra i).left < m+1)(hr:(extra i).right < m+1),
      100*(max (extra i).left (extra i).right+1)≤D→Sold R V (extra i) hl hr D checked:=by
  constructor
  · intro b
    apply occupied R B O χ price P V checked held _ (lower R e K compact clear extra D b) he he
    simpa only [electrode,max_self] using lowerWidth
  · intro i hl hr width
    exact occupied R B O χ price P V checked held _ (additional R e K compact clear extra D i) hl hr width

end YM.Integration.WilsonPhysicalStationMixedWickPlacement
end
