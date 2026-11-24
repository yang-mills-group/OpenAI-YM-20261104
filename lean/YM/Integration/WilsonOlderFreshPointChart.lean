import YM.Integration.WilsonOlderFreshPointCommission
import YM.Integration.WilsonOriginalPrimerStampedRay
/-! Localized signed readings of the actual directed field, on every
auxiliary side and point. All angular ranks use the original lamp on the
specified printed roll. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointChart
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open WilsonOlderFreshGraphPainter
open scoped Topology ENNReal BigOperators Classical
variable {G:Gauge} {d D:ℕ} (R:Run G) (L:Primer.Families R.family)
variable (a:hue G) (depth:d<D) (simple:G.Simple)





def chart (i:ℕ)(b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R i D)
    (n:Side)(x:Site n):WilsonCoeffUV.PChart G n:=
  WilsonOriginalPlacedPrimerInk.filed d (WilsonOlderFreshPointGauge.field R L a depth i b p) n x

theorem named (i:ℕ)(b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R i D)
    (n:Side)(x:Site n)(j:ℕ)(A:Board (Loc G 1) n ℝ):
    MvPolynomial.eval A (coeff j (WilsonCoeffUV.Blue.flash (chart R L a depth i b p n x)))=
      WilsonOlderFreshPointGauge.panel R L a depth i b p n (WilsonElectedPrimaryTensor.pin x) j A:=by
  rw [chart,WilsonOriginalPlacedPrimerInk.tested]
  classical
  simp [WilsonOlderFreshPointGauge.panel,WilsonFormalGaugeSections.panel,WilsonElectedPrimaryTensor.pin,ite_mul]
  rfl

theorem admitted (i:ℕ)(b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R i D)
    (n:Side)(x:Site n):
    WilsonCoeffUV.Blue.shellK d (chart R L a depth i b p n x) ∧
      ∀j,WilsonCoeffUV.Blue.Pure (chart R L a depth i b p n x j):=
  ⟨WilsonOriginalPlacedPrimerInk.shelf d _ n x,WilsonOriginalPlacedPrimerInk.pure d _ n x⟩

theorem original {Q:ℕ}{σ:ℝ}(i:ℕ)(b:Letter (R.family.labels.level d))(p:WilsonOlderFreshPointGauge.Ballot R i D)
    (T:WilsonOlderFreshGraphSlate.Copy G d Q σ)(source:WilsonOlderFreshPointCommission.Published R L a depth i b p T):
    WilsonOriginalPrimerStampedRay.Matched T (chart R L a depth i b p):=by
  intro e he n x A
  exact (named R L a depth i b p n x e A).trans (source ⟨e,Nat.lt_succ_of_le he⟩ n A (WilsonElectedPrimaryTensor.pin x))

end YM.Integration.WilsonOlderFreshPointChart
end
