import YM.Integration.WilsonElectedPrimaryCurvature
import YM.Integration.WilsonOriginalPlacedPrimerInk

/-! The actual positioned angular chart, including its whole symmetric tensor, and
the funded curvature roster read the same coefficient on every direction
through the purchased degree. The marked point is tested with a single
physical delta; all of its periodic translates are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonElectedPrimaryTensor
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

open WilsonOlderFreshGraphAward
include simple

def pin {n:Side} (x:Site n) : Board Unit n ℝ:=fun z=>if z.1=x then 1 else 0

def chart (i:ℕ)(w:Letter (R.family.labels.level d))(p:Ballot i D)(n:Side)(x:Site n):WilsonCoeffUV.PChart G n:=
  WilsonOriginalPlacedPrimerInk.filed d (Primer.fieldCoeffs R.family a L depth p.1.1 i w p.2) n x

omit simple in
theorem named (i:ℕ)(w:Letter (R.family.labels.level d))(p:Ballot i D)(n:Side)(x:Site n)
    (j:ℕ)(A:Board (Loc G 1) n ℝ):
    MvPolynomial.eval A (coeff j (WilsonCoeffUV.Blue.flash (chart R L a depth i w p n x)))=
      probe R L a depth i w p n (pin x) j A:=by
  rw [chart,WilsonOriginalPlacedPrimerInk.tested,WilsonOlderFreshGraphAward.probe]
  classical
  simp [pin,ite_mul]

omit simple in
theorem admitted (i:ℕ)(w:Letter (R.family.labels.level d))(p:Ballot i D)(n:Side)(x:Site n):
    WilsonCoeffUV.Blue.shellK d (chart R L a depth i w p n x) ∧
    ∀j,WilsonCoeffUV.Blue.Pure (chart R L a depth i w p n x j):=
  ⟨WilsonOriginalPlacedPrimerInk.shelf d _ n x, WilsonOriginalPlacedPrimerInk.pure d _ n x⟩

theorem original {φ U:ℕ→ℕ} (law:VowsR.LawScroll G φ)
    (I:Unit→Loan) (toll:d≤(I ()).toll) (Q:ℕ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G I d Q) simple law)
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)):
    let M:=menu G I d Q
    let H:=roots M simple R.metals.p R.metals.K
    (∃ B,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) B) ∧
    ∀ᶠ i:ℕ in atTop,
      ∃ P:ℕ→Ballot i D→Poetry.Roll G Unit,
       (∀(k:ℕ),1≤k→∀j≤Q,Agenda.Booked {()} () I (P j) (test i D) j
          (2*Agenda.seed H φ k (R.family.path.levels.clock.J i)) 1) ∧
       (∀j≤Q,∀(p:Ballot i D)(n:Side)(x:Site n)(A:Board (Loc G 1) n ℝ),
         MvPolynomial.eval A (coeff j (WilsonCoeffUV.Blue.flash (chart R L a depth i w p n x))) =
           ∑l∈Finset.range (Q+1),((P l p).folded l j).table n (mingle A (pin x))) := by
  intro M H
  obtain ⟨chamber,words⟩:=WilsonElectedPrimaryCurvature.original R L a depth simple law I toll Q purchase o w
  refine ⟨chamber,?_⟩
  filter_upwards [words] with i paid
  obtain ⟨P,budget,reads⟩:=paid
  refine ⟨P,budget,fun j hj p n x A=>?_⟩
  rw [named]
  exact reads j hj p n A (pin x)

end YM.Integration.WilsonElectedPrimaryTensor
end
