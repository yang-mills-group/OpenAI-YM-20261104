import YM.Integration.WilsonElectedPrimaryCurvature
import YM.Integration.WilsonPointChildFiledPress
/-! The genuinely displaced, independently normalized column has the full
nonlinear group Ward and a finite tensor presentation at each original
pair of dates. No average over the children is taken. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshPointGauge
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


abbrev Ballot (R:Run G)(i D:ℕ) := WilsonPointChildFiledPress.Tour R i × Studio D

def field (i:ℕ)(b:Letter (R.family.labels.level d))(p:Ballot R i D):Pot G :=
  WilsonNeutralPointCourse.filed R L a depth p.1.digit p.1.cutoff i b p.2

def sheet (i:ℕ)(b:Letter (R.family.labels.level d))(p:Ballot R i D)(e:ℕ):Ink.Field (Loc G 1 ⊕ Unit):=
  WilsonOlderFreshGraphInk.all (fun r:Fin (d+e+1)=>field R L a depth i b p e r)

def panel (i:ℕ)(b:Letter (R.family.labels.level d))(p:Ballot R i D)(n:Side)
    (s:Board Unit n ℝ):ℕ→Board (Loc G 1) n ℝ→ℝ:=
  WilsonFormalGaugeSections.panel (fun y=>s (y,())) (Kemp.banner d (field R L a depth i b p) n)

include simple in
theorem original (i:ℕ)(o:Loc G 1)(front:d≤R.family.path.levels.clock.J (i+1))
    (b:Letter (R.family.labels.level d))(p:Ballot R i D)(n:Side)(s:Board Unit n ℝ)(e:ℕ):
    Haiku.Vernal G n (panel R L a depth i b p n s) e ∧
    ∀A:Board (Loc G 1) n ℝ,
      (sheet R L a depth i b p e).table n (mingle A s)=panel R L a depth i b p n s e A:=by
  have actual:=(WilsonNeutralPointCourse.original R L a depth p.1.digit p.1.cutoff i simple o p.1.live front).officers b
  have widened:=clef_through actual (slotsFits _ b)
  refine ⟨WilsonFormalGaugeSections.original e (fun y=>s (y,())) _ ((solo_iff ..).mp widened.ward n p.2),?_⟩
  intro A
  apply WilsonOlderFreshGraphPublication.table o
  intro r
  obtain ⟨b,B,hb,_,paid⟩:=widened.fare.2.2 e r
  exact ⟨b,_,hb.le,paid p.2⟩

end YM.Integration.WilsonOlderFreshPointGauge
end
