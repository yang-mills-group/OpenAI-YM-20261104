import YM.Integration.WilsonReporterWeightedRankEpoch
import YM.TraceExtension.Prom.Front.West.Tael

/-! Pay the higher raw counts directly by the original unamplified
two-name ensemble on the same stamps, with every proper face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalPlain
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft MergeProof
open Function Filter Set Lattice Wilson RG Labels Pressure Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open Source Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal Next.Rank.Ribbon MergeProof.Accent Extra.Histories PhysicalNext.Repeat.Legato.Bandage
open WilsonPhysicalThermalWickSky (labels)
open WilsonPhysicalThermalWickRescale (pure)
open WilsonPhysicalThermalWickStretched (rates)
open WilsonReporterWeightedRankPrice (heats)
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {W:Bid.Worth} {u₀ ψ φ δ:ℕ→ℝ} {r:ℕ→ℕ}
    {door:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
    (B:Binding C) (H:C.Makes) (h:G.Simple)
    (source:Scrim C W u₀ ψ φ δ (fly C.path.levels) r door)
    (O:HaarBudget G) (J:ChartRatio G) {u D dSmall:ℕ} {d:Fin 2→ℕ}
    (g:(i:Fin 2)→C.label (d i)) {K:Set (Points 2)}
local notation "AX"=>C.path.levels

include h source
theorem stage (panel:ℕ→Tapes.Panel D)(θ:ℕ)(e roof z:ℝ)
    (taylor:∀k,(panel k).θ=θ)(coins:∀k,(panel k).currency=e)(bounded:∀k,(panel k).arc≤roof)
    (amounts:∀i≤D,generator G i≤z)(two:2≤u)(grade:∀i,d i≤D)(compact:IsCompact K)(clear:K⊆conf 2)
    (A:ℝ)(range:∀y∈K,Poly.price (fun _=>1) (Read.maxProfile C y (jointX g))≤A):
    ∀ᶠ k:ℕ in atTop,
      WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K) g (panel k) (fun _=>0) k A z:=by
  filter_upwards [earningsSky B H h source O J amounts θ e roof panel taylor coins bounded (d0:=d)
    g two two grade compact clear] with k money
  let α:=(panel k).bag ((C.path.levels).clock.J k)
  filter_upwards [WilsonReporterWeightedCourt.inside (k:=k) (b:=α.band) H d] with N permit
  intro p fine l v L V act x visit fit F t solved
  have receipts:=money l v L N p fine V act x visit fit F t solved
  have actual:=Read.full_cost H (Ship.fittingSky fit) (Ship.budget_pos AX u k).le
      (Ship.yardSky C α.band fine.le p) (permit p fine.le x fit t) receipts
  have small:=actual.trans (mul_le_mul_of_nonneg_right (range _ visit)
      (Ship.budget_pos AX u k).le)
  apply WilsonReporterWeightedRankPrice.gains AX u k 0 A
  simpa only [Fin.prod_univ_two,rates,Fin.zero_ne_one,if_false,if_pos,pow_zero,mul_one,one_mul] using small

theorem original (panel:ℕ→Tapes.Panel D)(θ:ℕ)(e roof z:ℝ)
    (taylor:∀k,(panel k).θ=θ)(coins:∀k,(panel k).currency=e)(bounded:∀k,(panel k).arc≤roof)
    (amounts:∀i≤D,generator G i≤z)(two:2≤u)(grade:∀i,d i≤D)(compact:IsCompact K)(clear:K⊆conf 2):
    ∃A:ℝ,0≤A ∧ ∀ᶠ k:ℕ in atTop,
      WilsonReporterWeightedRankEpoch.Result B H O J (u:=u) (K:=K) g (panel k) (fun _=>0) k A z:=by
  obtain ⟨A,range⟩:=WilsonReporterWeightedMarket.compact (C:=C) g compact clear
  refine ⟨max A 0,le_max_right _ _,stage B H h source O J g panel θ e roof z taylor coins
    bounded amounts two grade compact clear _ fun y hy=>(range y hy).2.trans (le_max_left _ _)⟩

end YM.Integration.WilsonPhysicalStationThermalPlain
end
