import YM.Integration.WilsonFormalGaugeSections
import YM.Integration.WilsonOlderFreshGraphAward

/-! A normalized original Wilson primary on its own formal course has a
jointly booked finite curvature-word representation on every torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonElectedPrimaryCurvature
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

theorem heard {U:ℕ→ℕ} (purchase:WilsonWindowFormalPurchase.Canonical U R.kit)
    (o:Loc G 1)(w:Letter (R.family.labels.level d)):
    ∀ᶠ i:ℕ in atTop,∀(n:Side)(s:Board Unit n ℝ)(j:ℕ)(p:Ballot i D),
      Haiku.Vernal G n (probe R L a depth i w p n s) j:=by
  filter_upwards [WilsonPublishedPrimerWard.original R L a depth simple purchase o w] with i valid
  intro n s j p
  exact WilsonFormalGaugeSections.original j (fun y=>s (y,())) _ (valid p.1.1 p.1.2 p.2 n)

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
       (∀j≤Q,∀(p:Ballot i D)(n:Side)(A:Board (Loc G 1) n ℝ)(s:Board Unit n ℝ),
         probe R L a depth i w p n s j A =
           ∑l∈Finset.range (Q+1),((P l p).folded l j).table n (mingle A s)) := by
  intro M H
  obtain ⟨chamber,words⟩:=WilsonOlderFreshGraphAward.original R L a depth simple law I toll Q purchase o w
  refine ⟨chamber,?_⟩
  filter_upwards [words,heard R L a depth simple purchase.2 o w] with i paid tested
  exact paid (fun n s j _ p=>tested n s j p)

end YM.Integration.WilsonElectedPrimaryCurvature
end
