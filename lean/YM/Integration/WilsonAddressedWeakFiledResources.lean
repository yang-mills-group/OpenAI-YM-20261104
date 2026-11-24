import YM.Integration.WilsonAddressedWeakJoinedWick
import YM.MergeProof.West.Tael

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakFiledResources
open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G}
local notation "Lev" => C.path.levels

theorem original (simple:G.Simple) (B:Binding C) (J:ChartRatio G) (M:C.Makes) (O:HaarBudget G) (D:ℕ):
    ∀ᶠ k:ℕ in atTop,∀ (N p u:ℕ) (live:k≤N) (ξ:Purse) (w z l r:ℝ)
    (L:LegacyCost B J w z ξ k u D O l r) (P:(i:ℕ)→Rep G (C.side i p)),
    let c:=isohypse M live p
    let Y:=stamp (Lev) N p
    Whip B J ξ L.hours L.moves c P (Station.width (Lev) ξ.band k) le_rfl → 0≤ξ.band →
    Nylon c P Y (short B N p) ξ ∧ Ceremony ξ c P (short B N p) Y ∧
    Ship.bank O (Lev) (Station.width (Lev) ξ.band k) ∧
    ∀ n≤u,Wall.Vantage (Lev) D k p n ξ.taylor ξ.band Y ∧
      ∀ (x:Points n),Fit (Lev) ξ.band k x → Plessey ξ x c P (short B N p) u:=by
  obtain ⟨a,bank⟩:=eventually_atTop.mp (Ship.banking (Lev) O simple)
  filter_upwards [eventually_ge_atTop (C.ref D),Radian.commissioned (Lev) simple D 2 (by decide) chartHeat_pos,
    (hat_rate (Lev) simple).eventually Flux.timing,
    (Lev).fits.deep.eventually_gt_atTop ((Lev).clock.J a)] with k date ready gaugeTickets late
  intro N p u live ξ w z l r L P c Y whip band
  have market:=embroidered B J c ξ M L.hours L.token L.moves P whip band
  have permit:=L.age.allot.permitted
  have eligible:D-1≤(Lev).clock.J k-2:=by
    have h:=(M.stages D).1
    have g:=(Lev).fits.mono date
    omega
  have width:a≤Station.width (Lev) ξ.band k:=by
    by_contra! h
    have he:=(permit.plateau (Station.width (Lev) ξ.band k) le_rfl ((wider ..).trans (before ..)))
    exact not_lt_of_ge (he ▸ (Lev).fits.mono h.le) late
  refine ⟨market,v_ceremony market L.moves.coup,bank _ width,?_⟩
  intro n enough
  obtain ⟨he,rows⟩:=y_supply _ _ rfl permit eligible L.clears N p
  let h:=rows n enough
  obtain ⟨q,height,level,join⟩:=h.optics
  refine ⟨⟨ready _ _ he,Radian.flown _ _ _ _ _ height join level h.visor h.hinge h.rotor h.force⟩,?_⟩
  intro x fit
  exact billing_X B J M L.hours P L.moves whip x fit market (L.room n enough) gaugeTickets (L.tariff n enough)
end YM.Integration.WilsonAddressedWeakFiledResources
end
