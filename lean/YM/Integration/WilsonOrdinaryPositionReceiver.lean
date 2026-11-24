import YM.Integration.WilsonOrdinaryPositionPrescription
import YM.Integration.WilsonReportPrescribedScene
import YM.Integration.WilsonPositionThermometerFreeLimit
import YM.Integration.WilsonPositionThermometerFinite

/-! Prescribe the complete signed, rotation-compatible primary once, before
any thermometer, cutoff, arity or perturbative order. Its actual reporting
calendar and independently normalized seven-term physical thermometer live
on the original measured continuum and the original regulator. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryPositionReceiver
open Function Filter Finset Set MeasureTheory Extraction Table Spec
open Next.Rank OPE OPE.Orbits RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS Trace
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Trace.Pilot Next.UVStress XSpace XSpace.Normalize XSpace.Rose
open MS MS.Theater MS.Menus MS.Land MS.Local.Physical Extra.FD FVA2 FVA2.ColorCode
open scoped Topology BigOperators Classical
universe u
variable {G : Gauge} (B : Deck G) {O : Booked B} (M : MS_Data G O)
  (V : Warehouse G) (μ : ℕ→ℝ) {p : E4} (nonzero : (0:E4)≠p)
  (U : ℕ→Set (Points 2)) (nbd : ∀d,U d∈𝓝 (Extra.FD.couple 0 p))

def profile (d : ℕ) : Test 2 := (MSSeparatedTestGram.localized V M d (μ d) nonzero (U d) (nbd d)).choose

theorem filed (d : ℕ) :
    let z := profile B M V μ nonzero U nbd d
    tsupport z⊆U d ∧ (∀x,(z x).im=0 ∧ 0≤(z x).re) ∧ 0<(z (Extra.FD.couple 0 p)).re ∧
      (∫ x,z x)=1 ∧ IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 z) :=
  (MSSeparatedTestGram.localized V M d (μ d) nonzero (U d) (nbd d)).choose_spec

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Spec.Final R.family f S) (J : ℝ→PhysMS.tower S) (H : (Bel R.family.book).Hierarchy) (γ : ℝ→ℝ)
def tower (r : ℝ) : PhysMS.tower S :=
  WilsonOrdinaryPositionPrescription.positioned B M F J H (profile B M V μ nonzero U nbd) μ γ r

/-- The *whole* originally normalized rotation-averaged seven-term
observable, and its genuine finite cutoff limit, before the test is named. -/
def monitored (Y : ℝ→PhysMS.tower S) (l : Filter UVIndex) : Prop :=
  ∀(store : XSpace.Normalize.Store G) (K : XSpace.Rose.Pick store),
    Tendsto (WilsonPositionThermometerReading.reading F Y K) Trace.Pilot.trail (𝓝 0) ∧
    ∀ r : ℝ,0<r→Tendsto (WilsonPositionThermometerFinite.finite (R:=R) Y r K) l
      (𝓝 (WilsonPositionThermometerReading.reading F Y K r))

theorem on_run (hG : G.Simple) (lead : PhysMS.Leading F J)
    (old : ∀d,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F H (J r) d) (hγ : Trace.Pilot.Coupling G γ)
    {T : Campaign R} (W : Campaign.Pillars R T) {δ : ℝ} (funded : FundedOriginalProperties.{u} hG δ W)
    (subsidy : WilsonReportColumnSubsidy.Eligible R.kit) (pace : WilsonWindowReportingPace.Slow R.kit)
    {b : ℕ} (hb : 0<b) (fac : OPE.Facilities R.family f S)
    (reader : OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (X : Scaling S) (foundation : Foundation F reader) :
    let Y := tower B M V μ nonzero U nbd F J H γ
    PhysMS.Leading F Y ∧ (∀d,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F H (Y r) d) ∧
    Pier.Lair.Present F Y ∧
    ∃ (u : Ultrafilter UVIndex) (Q : Lenses.Mantle F (u:Filter UVIndex)) (L : Layout F),
      (u:Filter UVIndex)≤f.fuse ∧ Pegs Q L ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels hG b ∧
      Pier.Scene.ScenePlan R F L ∧ (∀ d : ℕ,Pier.Lair.Paying F (Pier.Lair.tender F L Y) d) ∧
      monitored F Y (u:Filter UVIndex) := by
  let z := profile B M V μ nonzero U nbd
  let Y := tower B M V μ nonzero U nbd F J H γ
  have live (d : ℕ) : IsUnit (MSSeparatedTestGram.matrix M d (μ d) 0 (z d)) :=
    (filed B M V μ nonzero U nbd d).2.2.2.2
  have led : PhysMS.Leading F Y :=
    WilsonOrdinaryPositionPrescription.leading B M F J H z μ γ hG lead live hγ old
  have admitted (d : ℕ) : ∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F H (Y r) d :=
    WilsonOrdinaryPositionPrescription.symmetries B M F J H z μ γ hG lead live hγ old d
  have present := WilsonReportPrescribedFrame.present F Y led admitted
  obtain ⟨u,Q,L,cut,pegs,level,scene,pay⟩ :=
    WilsonReportPrescribedScene.selected hG W funded subsidy pace hb F fac reader Y led admitted
  refine ⟨led,admitted,present,u,Q,L,cut,pegs,level,scene,pay,?_⟩
  intro store K
  exact ⟨WilsonPositionThermometerFreeLimit.measured F Y K reader led hG X foundation,
    fun r hr=>WilsonPositionThermometerFinite.original F Y r K hG cut hr⟩

end YM.Integration.WilsonOrdinaryPositionReceiver
end

