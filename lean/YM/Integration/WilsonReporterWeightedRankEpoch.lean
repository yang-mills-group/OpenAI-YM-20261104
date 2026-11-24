import YM.Integration.WilsonReporterWeightedRankPrice

/-! The two-arm rank surplus on the original Wilson measure, with one actual
heat map for each fitted source. Costs are booked at the active degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReporterWeightedRankEpoch
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

def Stage {p:ℕ→Prop} (_:∀ᶠ k:ℕ in atTop,p k) (k:ℕ) := p k

def Result (panel:Tapes.Panel D) (q:Fin 2→ℕ) (k:ℕ) (A z:ℝ) : Prop :=
  let α:=panel.bag (C.path.levels.clock.J k)
  ∀ᶠ N:ℕ in atTop, ∀ (p:ℕ) (fine:k<N) (l v:ℝ)
    (L:LegacyCostSky B J (-3) z α k u D O l v)
    (V:Rep G (C.side k p)) (_:ActumSky B H O J panel L V fine)
    (x:Points 2) (_:tested AX α.band k x∈K) (_:FitSky AX α.band k x)
    (F:(i:Fin 2)→StampDuty C k N p (d i) α.taylor V α.era.coast.Q (PhysicalNext.RankCovariance.stamp AX N p))
    (t:(i:Fin 2)→C.label (d i)),
    (∀ i,Price.Solves C (mag AX α.band k) (d i) k N p (F i).T (g i) (t i)) →
    (C.path.levels.clock.monitor k)^(((q 1-q 0:ℕ):ℝ)+1/(16*u)) *
      ‖C.numeric N p (q_asked (C:=C) t) (fun i=>Cells.location C.S k N p (Station.choose AX α.band k x i)) -
        (standard C).useAt (standard C) (tested AX α.band k x) (jointX g)‖ ≤ A

include source in
theorem attained {k θ:ℕ} (pan:Tapes.Panel D) (q:Fin 2→ℕ) (A e z:ℝ)
    (sch:pan.θ=θ) (budget:pan.currency=e)
    (grades:∀i,d i≤D) (small:∀i,d i≤dSmall) (zpaid:∀i,generator G (d i)≤z)
    (ranks:∀i,WilsonPhysicalThermalWickRescale.pure (q i) (thawKey (labels g grades i)))(order:∀i,q i≤D)(rise:q 0≤q 1)
    (shelf:100*(D+1)≤θ) (two:2≤u)
    (fees:∀i,saves C (d i)+(q 1-q 0:ℕ)+3≤pan.arc)
    (credit:∀ j,pan.arc*dSmall+dSmall+2+(q 1-q 0:ℕ)≤(pan.bag j).credit)
    (pre:Stage (WilsonReporterWeightedCash.original C h H source θ e z d g small zpaid) k)
    (regular:Stage (WilsonPhysicalThermalWickHearing.original h g grades q ranks order rise shelf A) k)
    (bounds:∀ y∈K,‖Read.maxProfile C y (jointX g)‖≤A ∧ Poly.price (fun _=>1) (Read.maxProfile C y (jointX g))≤A)
    (held:WallsSky pan.arc grades g K θ k)
    (tariff:∀ A:BudgetPoint,A.B≤Perch.walls (clim AX k)→Flux.Tickets A (Flux.kinetics (clim AX k)))
    (ref:∀i,C.ref (d i)≤k) (refD:C.ref D≤k)
    (k₀:ℕ) (enough:C.path.levels.clock.J k₀+1<C.path.levels.clock.J k)
    (old:∀ i≥k₀,Ship.bank O AX i)
    (models:∀ N p,Radian.Seal AX k p D 2 (PhysicalNext.RankCovariance.stamp AX N p) chartHeat →
      Wall.Model AX D k p (PhysicalNext.RankCovariance.stamp AX N p)) :
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
  obtain ⟨single,pair,inv⟩:=WilsonReporterWeightedCourt.original B H J L fine Fd hpos refD two (models N p) grades window hx fit
  let gap:=q 1-q 0
  let a:=rates ((bill 1 (clim AX k))^gap)
  have calibrated:=regular (ξ:=α) (P:=P) fine.le ht fit F single pair inv (fun i=>hb ▸ fees i) (bounds _ hx).1 t solved
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

end YM.Integration.WilsonReporterWeightedRankEpoch
