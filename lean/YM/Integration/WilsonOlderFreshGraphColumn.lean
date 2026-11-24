import YM.FormalBulk08.Primer.Fields
import YM.Integration.WilsonWindowFormalAnnouncement
import YM.Integration.WilsonOlderFreshGraphTours

/-! Re-issue the complete inverse-normalized finite-cutoff column on its own
physical school's strip. Every field component, including the scalar and the
stable fourth field jet, comes from this one section on the actual clock. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphColumn
open Function Filter Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Mentor Push.PriceCompiler Primer
open WilsonOlderFreshGraphTours WilsonOlderFreshGraphSchool WilsonWindowJointPurchase WilsonFundedWindowMenu
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

theorem funding {φ:ℕ→ℕ} (law:VowsR.LawScroll G φ) (U:ℕ→ℕ) (shell:ℕ→ℝ) (cost:∀k,0<shell k)
    (before : ∀(s:Sheet G)(q:MapPrices),WilsonWindowBookPurchase.Permitted law s (ThroughLaunch.raging s q)):
    AllPrices (Together (@WilsonOlderFreshGraphSchool.grant G φ (signedMenu G shell cost) simple law)
      (@WilsonWindowFormalPurchase.Canonical G U)) := fun s q=>
  joint (WilsonOlderFreshGraphSchool.before_period (signedMenu G shell cost) simple law before s q)
    (WilsonWindowFormalPurchase.prepaid U s _)

theorem normalized {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)) (r E:ℕ)
    (shell:ℕ→ℝ) (pos:∀k,0<shell k) (load:ℕ→ℕ) (grade:ℕ) (late:1≤grade):
    ∃ (B:ℝ) (v:ℕ),0≤B ∧ ∀ᶠ i:ℕ in atTop,∀ N:ℕ,i≤N→∀(f:Studio D) (e:ℕ),e≤E→
      ∀(m:ℕ) (len:chain (Biglot (Loc G 1)) r→ℕ),
      (∀z,(len z:ℝ) ≤ shell grade*(1+(wide (fame _) (Fin.cons (0,o) z):ℝ)))→
      let x:=R.family.path.levels.clock.J i
      let b:=(windowBasis G R.family.path.levels.clock.kernel).width x
      let σ:=Poetry.Agenda.seed (roots (signedMenu G shell pos) simple R.metals.p R.metals.K) load grade x
      let T:=Primer.fieldCoeffs R.family a L depth N i w f e r
      (∑' z:chain (Biglot (Loc G 1)) r,ENNReal.ofReal ((1+(wide (fame _) (Fin.cons (0,o) z):ℝ))^m *
          Real.exp (3*σ*(len z:ℝ))) * ‖T z‖ₑ) ≤
        ENNReal.ofReal (fee b m*(B*(Borough.ageZ (R.family.path.levels.clock.hatBeta i))^v*‖Annex.compress D f‖)) := by
  let C:=R.family
  let J:=d+D+E+5
  have j5:5≤J:=by dsimp [J];omega
  have jD:D≤J:=by dsimp [J];omega
  have jE:E≤J:=by dsimp [J];omega
  have jd:d+3≤J:=by dsimp [J];omega
  obtain ⟨K,eventual⟩:=eventually_atTop.mp (C.path.levels.fits.deep.eventually_ge_atTop J)
  have gate:J≤C.path.levels.clock.J (K+1):=eventual _ (Nat.le_succ K)
  let ann:=WilsonWindowFormalAnnouncement.on_run R purchase
  obtain ⟨B,v,B0,ledger⟩:=Primer.landedFields C simple a L o ann j5 gate jE depth jd jD w r
  refine ⟨B,v,B0,?_⟩
  filter_upwards [eventually_ge_atTop K] with i past
  intro N room f e order m len route
  exact enrolled simple R load shell pos grade (C.path.levels.clock.J i) late (fame _) (0,o)
    (Primer.fieldCoeffs C a L depth N i w f e r) _ (((ledger i past f e order).2.2 N room).1) len route m

include simple in
theorem issued {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit) (o:Loc G 1):
    ∀ᶠ i:ℕ in atTop,∀ N:ℕ,i<N→
      let C:=R.family
      let S:=Primer.fieldStep C a L depth N i
      let T:=Primer.fieldCoeffs C a L depth N
      let step:=migrates a (destination C.path.levels N i) (L i) (Primer.Noise C)
        (Primer.densityCoeff C L a N (i+1)) (chart G) (Hay.Wday _ _) (Elm.growL _ i) d d
      T i=larch (step ∘ T (i+1)) S⁻¹ ∧ larch (T i) S=step ∘ T (i+1) := by
  let C:=R.family
  let J:=d+D+5
  have j5:5≤J:=by dsimp [J];omega
  have jD:D≤J:=by dsimp [J];omega
  have jd:d+3≤J:=by dsimp [J];omega
  obtain ⟨K,eventual⟩:=eventually_atTop.mp (C.path.levels.fits.deep.eventually_ge_atTop J)
  have gate:J≤C.path.levels.clock.J (K+1):=eventual _ (Nat.le_succ K)
  let ann:=WilsonWindowFormalAnnouncement.on_run R purchase
  filter_upwards [eventually_ge_atTop K] with i past
  intro N room
  exact ((Primer.primal C simple a L o ann j5 gate depth jd jD past N room.le).2.2 room).2

end YM.Integration.WilsonOlderFreshGraphColumn
end
