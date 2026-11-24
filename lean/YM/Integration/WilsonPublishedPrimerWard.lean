import YM.Integration.WilsonOlderFreshGraphPublication

/-! The actual normalized primary column carries the full nonlinear
formal gauge identity, at every age, before a torus is chosen. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPublishedPrimerWard
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Mentor Push.PriceCompiler Primer AllOrder
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)

include simple
theorem original {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)):
    ∀ᶠ i:ℕ in atTop,∀N:ℕ,i≤N→∀(f:Studio D)(n:Side),
    let W:=Kemp.banner d (Primer.fieldCoeffs R.family a L depth N i w f) n
    Reef.Rite W W 1 0:=by
  let C:=R.family
  let J:=d+D+5
  have j5:5≤J:=by dsimp [J];omega
  have jD:D≤J:=by dsimp [J];omega
  have jd:d+3≤J:=by dsimp [J];omega
  obtain ⟨K,eventual⟩:=eventually_atTop.mp (C.path.levels.fits.deep.eventually_ge_atTop J)
  have gate:J≤C.path.levels.clock.J (K+1):=eventual _ (Nat.le_succ K)
  let ann:=WilsonWindowFormalAnnouncement.on_run R purchase
  filter_upwards [eventually_ge_atTop K] with i past
  intro N live f n
  have native:=(Primer.primal C simple a L o ann j5 gate depth jd jD past N live).1.officers w
  exact (solo_iff ..).mp (clef_through native (slotsFits _ w)).ward n f

end YM.Integration.WilsonPublishedPrimerWard
end
