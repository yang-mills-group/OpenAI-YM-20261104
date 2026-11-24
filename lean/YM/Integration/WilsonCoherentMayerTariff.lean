import YM.Integration.WilsonCoherentMayerMultiplier
import YM.RGLocalTaylor.Laminate.Edit

/-! Price the fully correlated signed Mayer integrand at each actual
orbit and noise. The catastrophe and tariff are those of its entered
molecule, and the unselected partners carry their enrolled team weights. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerTariff
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
  {R:Rep G f} {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}
  {q r a b D v Y C' A B cost K θ δ ζ α:ℝ} {p select:Molecule S}
  (N:Captain H j C' D v Y A b r B q n χ)
  (law:Awning H N.conduit A b cost a δ ζ k l) (room:Q.goal L s≤K)
  (allow:Mayer.Approved K θ j M)

include law room allow
theorem priced (u:Mayer.Decors select M) (hs:select⊆p) (hw:Mayer.decorOrder u≤M)
    (f':Head S→Insert T) (w:Head S→ℝ)
    (factors:∀i∈p\select,EstFactor N.conduit i (f' i) A (w i) α)
    (cohort:Mayer.Start select) (reserve:(M+4:ℝ)*r≤α) (charge:1≤α)
    (inside:troupe T R Q.halo (radiusB s) p)
    (X:Coat T F) (healthy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx:X.x=s) (hk:X.width=o.K) (hχ:X.χ=χ) (hm:X.manifest) (z:momentSpace X):
    |Mayer.planned H p u f' X z| ≤
      (X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator
        (fun _=>Mayer.tariff N.conduit p θ u w) z.2 :=by
  let Y':=X.wrapY z.1
  let held : ℝ → Config G c:=fun _=>Y'.V
  have mode:Mode held 0 j v:=⟨N.position.le,fun i=>a_oneB G _ N.position.le⟩
  have covered:=Mayer.prizes law allow room factors hs cohort reserve charge inside u
  have bound:=(covered F Y' z.2 hx hk hχ hm healthy ℝ held 0 mode rfl).bound
  change ‖(Mayer.tagged H p f' u).value (vary Y' Y'.V) (course Y' A R.beta z.2 Y'.V)‖≤_ at bound
  rw [Silica.home Y' law.chart z.2 H.laws.intake.positive] at bound
  rw [←Mayer.physical_plan u hs hw N law room allow f' cohort healthy hx hk hχ hm]
  exact bound

theorem partners (team:Team R) (before:team.signs S⊆p)
    (u:Mayer.Decors (p\team.signs S) M) (hw:Mayer.decorOrder u≤M)
    (cohort:Mayer.Start (p\team.signs S)) (reserve:(M+4:ℝ)*r≤α) (charge:1≤α)
    (speed:ζ≤α) (inside:authorized H p)
    (X:Coat T F) (healthy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx:X.x=s) (hk:X.width=o.K) (hχ:X.χ=χ) (hm:X.manifest) (z:momentSpace X):
    |Mayer.planned H p u (Laminate.partner team H) X z| ≤
      (X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator
        (fun _=>Mayer.tariff N.conduit p θ u (Laminate.coverWeight team S)) z.2 :=by
  apply priced N law room allow u sdiff_subset hw _ _ _ cohort reserve charge inside.2 X healthy hx hk hχ hm z
  intro i hi
  rw [Laminate.compartments team p before] at hi
  obtain ⟨j,hj,rfl⟩:=mem_image.mp hi
  unfold Laminate.coverWeight Laminate.partner
  rw [Laminate.chosenAt team _ _ _ j hj,Laminate.chosenAt team _ _ _ j hj]
  exact (Laminate.afford law j).weaken le_rfl speed

end YM.Integration.WilsonCoherentMayerTariff
