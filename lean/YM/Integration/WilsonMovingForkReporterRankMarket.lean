import YM.Integration.WilsonReporterWeightedPairSale
import YM.Integration.WilsonMovingForkReporterRankCourt

/-! The actual finite compensated cutoffs pay the signed rank price at every original admitted aperture. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForkReporterRankMarket
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


open WilsonMovingForkReporterHeatedAperture (spread)

noncomputable def amount (E:WilsonMovingForkReporterHeatedAperture.Test C) : ℝ :=
  max 1 (WilsonReporterWeightedMarket.compact E.raw E.compact E.clear).choose

theorem pays (E:WilsonMovingForkReporterHeatedAperture.Test C) (x:Points 2) (hx:x∈E.support) :
    ‖Read.maxProfile C x (jointX E.raw)‖≤amount E ∧ Poly.price (fun _=>1) (Read.maxProfile C x (jointX E.raw))≤amount E := by
  have bought := (WilsonReporterWeightedMarket.compact E.raw E.compact E.clear).choose_spec x hx
  exact ⟨bought.1.trans (le_max_right ..),bought.2.trans (le_max_right ..)⟩

theorem active (E:WilsonMovingForkReporterHeatedAperture.Test C) (pan:Tapes.Panel D) (k n:ℕ) (z:ℝ)
    (quoted:WilsonMovingForkReporterRankCourt.Signed B H O J E pan k n z) :
    WilsonReporterWeightedPairSale.Ready (K:=E.support) (u:=n) B H O J E.raw pan E.rank k z := by
  let α := pan.bag (C.path.levels.clock.J k)
  intro N p fine l v L P whip x member fit F t solved
  have positive:0≤α.band := by rw [show α.band=pan.arc from pan.factor _]; linarith only [pan.huge,Nat.cast_nonneg (α:=ℝ) D]
  have native:=embroideredSky B J (isohypse H fine.le p) α H L.hours L.token L.moves P whip positive
  have chart:=native.fixture (beforeSky ..) (le_refl k)
  have day : ActumSky B H O J pan L (P k) fine := by
    refine ⟨⟨fun Z hZ=>hZ.symm ▸ native.stencil,chart.threshold,chart.budget,?_⟩,P,rfl,whip⟩
    have inner:=native.paths.canvas.radius
    change _+10≤α.era.coast.Q at inner
    change _ ≤ α.era.coast.Q
    omega
  exact quoted N p fine l v L (P k) day x member fit F t solved P rfl

include h source in
theorem original (E:WilsonMovingForkReporterHeatedAperture.Test C) (D u θ:ℕ) (e z upper:ℝ)
    (activeD:100*(E.height+1)≤D) (shelf:100*(E.height+1)≤θ) (two:2≤u)
    (wide:(D:ℝ)+6≤upper) (tax:∀i,generator G (E.deg i)≤z)
    (axes:∀i, WilsonPhysicalThermalWickRescale.pure (E.rank i)
      (thawKey (labels E.raw (fun i=>(E.elevated i).trans (show E.height≤D by omega)) i))) :
    ∀ᶠ k:ℕ in atTop,∀pan:Tapes.Panel D,pan.θ=θ →pan.currency=e →pan.arc≤upper →
      WilsonReporterWeightedRankEpoch.Result (K:=E.support) (u:=u) B H O J E.raw pan E.rank k (amount E) z := by
  have window := WilsonMovingForkReporterRankCourt.original B H O J h E (D:=D) (by omega) θ shelf
    ((D:ℝ)+6) upper (by linarith only [Nat.cast_nonneg (α:=ℝ) D]) wide (fun i=>by
      have cap := E.capped 1
      have lower := E.elevated i
      have enough : E.deg i + spread E ≤ D := by dsimp [WilsonMovingForkReporterHeatedAperture.spread];omega
      have grown : (E.deg i:ℝ)+(spread E:ℝ)≤D := by exact_mod_cast enough
      linarith only [Tapes.savings C (E.deg i),grown])
  obtain ⟨k₀,old⟩:=eventually_atTop.mp (Ship.banking AX O h)
  filter_upwards [window,WilsonReporterWeightedCash.original C h H source θ e z E.deg E.raw E.elevated tax,
    (hat_rate AX h).eventually Flux.timing,(C.path.levels).fits.deep.eventually_gt_atTop (C.path.levels.clock.J k₀+1),
    eventually_all.mpr (fun i:Fin 2=>eventually_ge_atTop (C.ref (E.deg i)))] with k room pay tariff enough refs pan study cash cover
  obtain ⟨walls,regular⟩:=room pan study ⟨pan.huge,cover⟩
  exact WilsonReporterWeightedPairSale.funded B H h source O J E.raw pan E.rank (amount E) e z study cash
    (fun i=>(E.elevated i).trans (by omega)) E.elevated tax axes two
    (WilsonReporterWeightedRankPrice.purse _ (by omega) ((Nat.sub_le ..).trans ((E.capped 1).trans (by omega))))
    pay (active B H O J E pan k u z (regular u two z)) (pays E) walls tariff refs k₀ enough old

end YM.Integration.WilsonMovingForkReporterRankMarket
end
