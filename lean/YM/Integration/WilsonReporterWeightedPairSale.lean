import YM.Integration.WilsonReporterWeightedRankEpoch

/-! The two-arm rank surplus on the original Wilson measure, with one actual
heat map for each fitted source. Costs are booked at the active degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedPairSale
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

open WilsonReporterWeightedRankEpoch (Stage Result)
def Ready (pan:Tapes.Panel D) (q:Fin 2→ℕ) (k:ℕ) (z:ℝ) : Prop :=
  let α:=pan.bag (C.path.levels.clock.J k)
  let a:=rates ((bill 1 (clim AX k))^(q 1-q 0))
  ∀ (N p:ℕ) (fine:k<N) (l v:ℝ) (L:LegacyCostSky B J (-3) z α k u D O l v)
    (P:(i:ℕ)→Rep G (C.side i p)), WhipSky B J α L.hours L.moves (isohypse H fine.le p) P (widthSky AX α.band k) le_rfl →
    ∀ (x:Points 2), tested AX α.band k x∈K → ∀ (fit:FitSky AX α.band k x)
    (F:(i:Fin 2)→StampDuty C k N p (d i) α.taylor (P k) α.era.coast.Q (PhysicalNext.RankCovariance.stamp AX N p))
    (t:(i:Fin 2)→C.label (d i)),
    (∀ i,Price.Solves C (mag AX α.band k) (d i) k N p (F i).T (g i) (t i)) →
    WilsonReporterWeightedReturn.Signed (ξ:=α) (P:=P) (WilsonReporterWeightedOrdinary.stretch C a g)
      (WilsonReporterWeightedOrdinary.stretch C a t) fit F

include source in
theorem funded {k θ:ℕ} (pan:Tapes.Panel D) (q:Fin 2→ℕ) (A e z:ℝ)
    (sch:pan.θ=θ) (budget:pan.currency=e)
    (grades:∀i,d i≤D) (small:∀i,d i≤dSmall) (zpaid:∀i,generator G (d i)≤z)
    (ranks:∀i,WilsonPhysicalThermalWickRescale.pure (q i) (thawKey (labels g grades i)))
    (two:2≤u)
    (credit:∀ j,pan.arc*dSmall+dSmall+2+(q 1-q 0:ℕ)≤(pan.bag j).credit)
    (pre:Stage (WilsonReporterWeightedCash.original C h H source θ e z d g small zpaid) k)
    (regular:Ready (u:=u) (K:=K) B H O J g pan q k z)
    (bounds:∀ y∈K,‖Read.maxProfile C y (jointX g)‖≤A ∧ Poly.price (fun _=>1) (Read.maxProfile C y (jointX g))≤A)
    (held:WallsSky pan.arc grades g K θ k)
    (tariff:∀ A:BudgetPoint,A.B≤Perch.walls (clim AX k)→Flux.Tickets A (Flux.kinetics (clim AX k)))
    (ref:∀i,C.ref (d i)≤k)
    (k₀:ℕ) (enough:C.path.levels.clock.J k₀+1<C.path.levels.clock.J k)
    (old:∀ i≥k₀,Ship.bank O AX i) :
    Result (K:=K) B H O J g (u:=u) pan q k A z := by
  let α:=pan.bag (C.path.levels.clock.J k)
  unfold Result
  filter_upwards [WilsonReporterWeightedCourt.inside (k:=k) (b:=α.band) H d] with N inside p fine l v L V day x hx fit F t solved
  obtain ⟨P,eq,Fd⟩:=day.acts
  subst V
  have hb : α.band=pan.arc := pan.factor _
  have ht : α.taylor=θ := (pan.stable _).trans sch
  have hpos : 0≤α.band := by rw [hb]; linarith only [pan.huge,Nat.cast_nonneg (α:=ℝ) D]
  have window : WallsSky α.band grades g K α.taylor k := by rw [hb,ht]; exact held
  let gap:=q 1-q 0
  let a:=rates ((bill 1 (clim AX k))^gap)
  have calibrated:=regular N p fine l v L P Fd x hx fit F t solved
  have same:=WilsonPhysicalThermalWickFree.original (tested AX α.band k x) (Ship.fittingSky fit) g grades q ranks (bill 1 (clim AX k))
  have ar (i:Fin 2) : WilsonReporterWeightedRankPrice.offsets gap i ≤ (gap:ℝ) := by
    by_cases hi:i=1 <;> simp [WilsonReporterWeightedRankPrice.offsets,hi]
  have positive (i:Fin 2) : 0 < a i := by
    by_cases hi:i=1
    · simp only [a,rates,hi,if_pos]; exact pow_pos (Real.exp_pos _) _
    · simp [a,rates,hi]
  have acct:=pre α α.band gap hpos (WilsonReporterWeightedRankPrice.offsets gap) ((pan.vital _).trans budget) ht (hb ▸ credit _) ar
    L.moves.year N p fine.le F t solved
  let row:=WilsonReporterWeightedOrdinary.stretch C a t
  have cash (i) : α.cash (clim AX k)*Spindle.moneys C (d i) k N p (row i)≤bill (-8) (clim AX k) := by
    change α.cash _*Spindle.moneys C _ _ _ _ ((a i:ℂ) • t i)≤_
    rw [show a=WilsonReporterWeightedMarket.radius (WilsonReporterWeightedRankPrice.offsets gap) (clim AX k) from (heats ..).symm]; exact acct.2.1 i
  have coins (i) : Rise.coin ((F i).W (row i))≤α.principal (clim AX k) := by
    change Rise.coin ((F i).W ((a i:ℂ) • t i))≤_
    rw [show a=WilsonReporterWeightedMarket.radius (WilsonReporterWeightedRankPrice.offsets gap) (clim AX k) from (heats ..).symm]; exact acct.2.2.1 i
  have hard (i) : Vac.Numbers.Hat (clim AX k)^z * Spindle.paid C (d i) k N p (row i)≤fly AX (d i) k := by
    change _ * Spindle.paid C _ _ _ _ ((a i:ℂ) • t i)≤_
    rw [show a=WilsonReporterWeightedMarket.radius (WilsonReporterWeightedRankPrice.offsets gap) (clim AX k) from (heats ..).symm]; exact acct.2.2.2 i
  exact WilsonReporterWeightedRankPrice.gains AX u k gap _ _
    (WilsonReporterWeightedMarket.onCourse B H source O J g grades two two L fine P Fd hpos
      (old _ (WilsonReporterWeightedMarket.permitted B O J L enough)) tariff ref window fit hx
      F a positive t same (bounds _ hx).2 cash coins hard calibrated
      (inside p fine.le x fit row))


include h source in
theorem original (panels:ℕ→Tapes.Panel D) (θ:ℕ) (e cap z:ℝ)
    (school:∀k,(panels k).θ=θ) (budget:∀k,(panels k).currency=e) (arc:∀k,(panels k).arc≤cap)
    (q:Fin 2→ℕ) (grades:∀i,d i≤D) (small:∀i,d i≤dSmall) (hSmall:dSmall<D)
    (zpaid:∀i,generator G (d i)≤z)
    (ranks:∀i,WilsonPhysicalThermalWickRescale.pure (q i) (thawKey (labels g grades i)))
    (order:∀i,q i≤D) (two:2≤u) (hK:IsCompact K)(sep:K⊆conf _):
    ∃ A:ℝ, ∀ᶠ k:ℕ in atTop, Ready (K:=K) (u:=u) B H O J g (panels k) q k z →
      Result (K:=K) (u:=u) B H O J g (panels k) q k A z := by
  obtain ⟨A,bounds⟩:=WilsonReporterWeightedMarket.compact g hK sep
  refine ⟨A,?_⟩
  let c:ℝ:=D+6
  have lo : 6≤c := by unfold c; linarith only [Nat.cast_nonneg (α:=ℝ) D]
  have walls:=mural_castSky grades g hK sep H h c lo
    (fun i=>by unfold c; linarith only [Tapes.savings C (d i),show (d i:ℝ)≤D from Nat.cast_le.mpr (grades i)])
    θ (fun k=>(panels k).arc) (fun k=>(panels k).huge) cap arc
  obtain ⟨k₀,old⟩:=eventually_atTop.mp (Ship.banking AX O h)
  filter_upwards [walls,WilsonReporterWeightedCash.original C h H source θ e z d g small zpaid,
    (hat_rate AX h).eventually Flux.timing,(C.path.levels).fits.deep.eventually_gt_atTop (C.path.levels.clock.J k₀+1),
    eventually_all.mpr (fun i=>eventually_ge_atTop (C.ref (d i)))] with k room cash tariff enough refs ready
  exact funded B H h source O J g (panels k) q A e z (school k) (budget k) grades small zpaid ranks two
    (WilsonReporterWeightedRankPrice.purse _ hSmall ((Nat.sub_le ..).trans (order 1)))
    cash ready bounds room tariff refs k₀ enough old

end YM.Integration.WilsonReporterWeightedPairSale
