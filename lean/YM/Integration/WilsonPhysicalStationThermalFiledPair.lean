import YM.Integration.WilsonPhysicalStationThermalVotes
import YM.Integration.WilsonPhysicalStationThermalRanks
import YM.Integration.WilsonReporterWeightedRankEpoch
import YM.Integration.WilsonMovingForkReporterNamedInk

/-! Apply the paid original two-name experiment to the actual before-
cutoff reporter. Both duties belong to the same prior and named Vane. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalFiledPair
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward MergeProof
open MergeProof.East MergeProof.Accent
open Next.Rank.Ribbon Table Trace.Pilot Trace PhysicalNext.Repeat.Legato
open WilsonPhysicalStationThermalVotes (votes offered)
open WilsonPhysicalStationThermalPair (cell)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(B:Binding R.family)(O:HaarBudget G)(J:ChartRatio G)
    {f:Extraction.Order}{S:(Bel R.family.book).Hierarchy}{h D u:ℕ}
    (V:Vane R.family h)(d:Fin (h+1))(checked:V.checked f S h)
    {K:Set (Points 2)}{z bound:ℝ}(P:Tapes.Panel D)
local notation "C"=>R.family
local notation "AX"=>R.family.path.levels

theorem original (x:R.family.label d)(y:(standard R.family).Field d)(q:Fin 2→ℕ)
    (ink:WilsonMovingForkReporterNamedInk.Filed B R.makes O J P V u z)
    (bought:WilsonReporterWeightedRankEpoch.Result B R.makes O J (u:=u) (K:=K)
        (d:=fun _:Fin 2=>d.val) (votes R d x y) P q V.k bound z):
    ∀ᶠ N:ℕ in atTop,∀ p:ℕ,∀ fine:V.k<N,∀ a:Points 2,
    tested AX V.b V.k a∈K → FitSky AX V.b V.k a →
      (R.family.path.levels.clock.monitor V.k)^(((q 1-q 0:ℕ):ℝ)+1/(16*u)) *
        ‖cell R V d (p:=p) checked fine V.k (choose AX V.b V.k a) x y -
          (standard R.family).classMoment (standard R.family) (fun _:Fin 2=>d.val)
            (tested AX V.b V.k a) ![(standard R.family).project d x,y]‖≤bound:=by
  obtain ⟨l,r,L,unfolded⟩:=ink.bill
  have width:(P.bag (R.family.path.levels.clock.J V.k)).band=V.b:=(P.factor _).trans ink.aperture
  filter_upwards [bought] with N funded
  intro p fine a live fit
  obtain ⟨Ψ,act,stamps⟩:=unfolded N p fine
  obtain ⟨stamp,same⟩:=stamps d
  have solved (i:Fin 2):Price.Solves R.family (mag AX (P.bag (R.family.path.levels.clock.J V.k)).band V.k)
      d V.k N p stamp.T (votes R d x y i) (offered R V d (p:=p) checked fine x y i):=by
    rw [width,same]
    exact WilsonPhysicalStationThermalVotes.solves R V d checked fine x y i
  have cash:=funded p fine l r L Ψ act a (width ▸ live) (width ▸ fit) (fun _=>stamp)
      (offered R V d (p:=p) checked fine x y) solved
  rw [width,WilsonPhysicalStationThermalVotes.physical,WilsonPhysicalStationThermalVotes.reference] at cash
  exact cash

end YM.Integration.WilsonPhysicalStationThermalFiledPair
end
