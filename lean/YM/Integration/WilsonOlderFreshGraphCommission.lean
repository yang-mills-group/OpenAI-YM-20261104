import YM.Integration.WilsonElectedPrimaryCurvature
import YM.Integration.WilsonOlderFreshGraphSlate

/-! The actual inverse-normalized field supplies a single before-test signed
word roster. The cutoff and the source film are varied after its tariff and
the physical roots were chosen. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCommission
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


open WilsonOlderFreshGraphSlate
theorem original {φ U:ℕ→ℕ} (law:VowsR.LawScroll G φ) (I:Unit→Loan)
    (toll:(I ()).toll=d) (d0:0<d) (Q:ℕ)
    (purchase:Together (@WilsonOlderFreshGraphSchool.grant G φ (menu G I d Q) simple law)
      (@WilsonWindowFormalPurchase.Canonical G U) R.kit)
    (o:Loc G 1) (w:Letter (R.family.labels.level d)):
    let M:=menu G I d Q
    let H:=roots M simple R.metals.p R.metals.K
    (∃ B,VowsR.Chamber law R.kit H (rollTab M simple R.metals R.rolls) B) ∧
    ∀ᶠ i:ℕ in atTop,∀ k:ℕ,1≤k→
      ∃ P:ℕ→Ballot i D→Poetry.Roll G Unit,
      ∃ b:ℝ,0 ≤ b ∧ ∃ T:Ballot i D → WilsonOlderFreshGraphSlate.Copy G d Q (Agenda.seed H φ k (R.family.path.levels.clock.J i)),
        (∀p,(∑j,(T p).fare j) ≤ b*(1+|test i D p|)) ∧
        (∀p (j:Fin (Q+1)),(T p).roll j=P j.val p) ∧
        ∀j≤Q,∀(p:Ballot i D)(n:Side)(A:Board (Loc G 1) n ℝ)(s:Board Unit n ℝ),
          probe R L a depth i w p n s j A =
             ∑l∈Finset.range (Q+1),((P l p).folded l j).table n (mingle A s):=by
  intro M H
  obtain ⟨school,published⟩:=WilsonElectedPrimaryCurvature.original R L a depth simple law I toll.ge Q purchase o w
  refine ⟨school,?_⟩
  filter_upwards [published] with i pi
  intro k hk
  obtain ⟨P,roll,eq⟩:=pi
  obtain ⟨b,b0,C,_,all,mass⟩:=WilsonOlderFreshGraphTariff.original I toll
    (fun j:Fin (Q+1)=>P j.val) _ _ (fun j=>roll k hk j.val (Nat.le_of_lt_succ j.isLt))
  let T (p:Ballot i D):Copy G d Q (Agenda.seed H φ k (R.family.path.levels.clock.J i)) :=
    ⟨(fun j=>P j.val p),(fun j=>C j p),(fun j=>(all j p).1),(fun j=>(all j p).2),d0⟩
  exact ⟨P,b,b0,T,mass,fun _ _=>rfl,eq⟩
end YM.Integration.WilsonOlderFreshGraphCommission
end
