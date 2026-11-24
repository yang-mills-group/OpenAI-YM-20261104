import YM.Integration.WilsonOlderFreshGraphInk

/-! One source field on the issued run for the entire independently normalized
column. The outgoing section is fixed before taking its angular components. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonOlderFreshGraphRoster
open Function Filter Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Mentor Push.PriceCompiler Primer AllOrder
open WilsonOlderFreshGraphInk
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

def row (N i:ℕ) (w:Letter (R.family.labels.level d)) (f:Studio D) (e:ℕ):
    Ink.Field (Loc G 1 ⊕ Unit):=
  WilsonOlderFreshGraphInk.all (fun r:Fin (d+e+1)=>Primer.fieldCoeffs R.family a L depth N i w f e r)

def narrow (d Q:ℕ) (i:ℕ) : ℝ:=
  (windowBasis G R.family.path.levels.clock.kernel).width (R.family.path.levels.clock.J i) /
    ((d:ℝ)+Q+1)

include simple in
theorem salary {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)) (Q:ℕ):
    ∃ (B:Fin (d+Q+1)→ℝ) (v:Fin (d+Q+1)→ℕ), (∀r,0≤B r) ∧
    ∀ᶠ i:ℕ in atTop, ∀ (N:ℕ),i≤N→∀(f:Studio D) (e:ℕ) (he:e≤Q),
      let cost (r:Fin (d+e+1)):=B (r.castLE (by omega)) *
        (ageZ (R.family.path.levels.clock.hatBeta i))^(v (r.castLE (by omega))) *
        ‖Annex.compress D f‖
      (row R L a depth N i w f e).Good (narrow R d Q i) (∑r,cost r) (d+e+1) ∧
        ∀k,QuadraticLocal.Sunrise.Focus.Depicted ({()}:Finset Unit) ((row R L a depth N i w f e).slip k) := by
  let C:=R.family
  let J:=d+D+Q+5
  have j5:5≤J:=by dsimp [J];omega
  have jD:D≤J:=by dsimp [J];omega
  have jQ:Q≤J:=by dsimp [J];omega
  have jd:d+3≤J:=by dsimp [J];omega
  obtain ⟨K,eventual⟩:=eventually_atTop.mp (C.path.levels.fits.deep.eventually_ge_atTop J)
  have gate:J≤C.path.levels.clock.J (K+1):=eventual _ (Nat.le_succ K)
  let ann:=WilsonWindowFormalAnnouncement.on_run R purchase
  have each (r:Fin (d+Q+1)):=Primer.landedFields C simple a L o ann j5 gate jQ depth jd jD w r.val
  choose B v nonneg ledger using each
  refine ⟨B,v,nonneg,?_⟩
  filter_upwards [eventually_ge_atTop K] with i past
  intro N room f e he
  let b:=(windowBasis G R.family.path.levels.clock.kernel).width (R.family.path.levels.clock.J i)
  have hb:0<b := (windowBasis G R.family.path.levels.clock.kernel).pos _
  apply purchased (b:=b) o _ _ (fun r=>((ledger (r.castLE (show d+e+1≤d+Q+1 by omega)) i past f e he).2.2 N room).1)
  · exact div_nonneg hb.le (by positivity)
  · rw [narrow,div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast (show d+e≤d+Q+1 by omega)) hb.le

end YM.Integration.WilsonOlderFreshGraphRoster
end
