import YM.Integration.WilsonCoherentMayerHearing

/-! The actual signed Mayer multiplier has a bounded measurable read on its
original sampled coat. The bound comes from the paid value in the same
near-configuration certificate, including the unselected marked partners. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerMultiplier
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
  {R:Rep G f} {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}
  {q r a b D v Y C' A B price K θ δ ζ:ℝ} {p select:Molecule S}
  (u:Mayer.Decors select M) (hs:select⊆p) (hw:Mayer.decorOrder u≤M)
  (N:Captain H j C' D v Y A b r B q n χ)
  (law:Awning H N.conduit A b price a δ ζ k l) (room:Q.goal L s≤K)
  (allow:Mayer.Approved K θ j M) (f':Head S→Insert T)
  (billed:∀ i∈p\select, Fits H (f' i) (H.supportP i) j) (cohort:Mayer.Start select)

include hs hw N law room allow billed cohort
theorem earned (X:Coat T F) (healthy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    (hx:X.x=s) (hk:X.width=o.K) (hχ:X.χ=χ) (hm:X.manifest):
    Measurable (Mayer.planned H p u f' X) ∧ ∃ C:ℝ, 0≤C ∧ ∀z, |Mayer.planned H p u f' X z|≤C :=by
  let actual:=Mayer.tagged H p f' u
  have fits:Fits H actual (H.unionP p) j:=Mayer.fits_tagged H f' billed u
  rw [←Mayer.physical_plan u hs hw N law room allow f' cohort healthy hx hk hχ hm]
  refine ⟨fits.along (V:=fun _=>X.V) X hx hk (momentSpace X) measurable_const
      measurable_fst measurable_snd,?_⟩
  let held : ℝ → Config G c:=fun _=>X.V
  have mode:Mode held 0 j v:=⟨N.position.le,fun i=>a_oneB G _ N.position.le⟩
  have flow:=N.oboe.flow F X hx hχ hk hm ℝ held 0 rfl mode
  obtain ⟨C,hC,hL⟩:=(fits.near X hx hk hm ℝ held 0 N.oboe.conduit N.oboe.mode flow).post
  refine ⟨C,hC,fun z=>?_⟩
  have cost:=(hL.self_of_nhds z).bound
  rw [Insert.tracking,show held 0=(X.wrapY z.1).V from rfl,
    Silica.home (X.wrapY z.1) N.oboe.conduit z.2 H.laws.intake.positive] at cost
  exact cost

end YM.Integration.WilsonCoherentMayerMultiplier
