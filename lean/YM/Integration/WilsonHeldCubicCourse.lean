import YM.Integration.WilsonHeldCubicHistory
import YM.Integration.ManuscriptQLocalMarkedHeight
import YM.LocalTaylorR2.Curriculum

/-! Choose the estimates for the cubic comparison before the period or the
interacting old Wilson field is specified. Both estimates use one physical
field, one moving direction scale, and one change of variables. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonHeldCubicCourse
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy LocalTaylorR2 LocalTaylorR2.Kiln
open Axial Channel Canvas Itinerary Port WilsonHeldKineticTeamIntegral
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}

theorem purchased (P : Teller G) (Q : ConnectedActivityE6.Target G P) :
    ∃ n₀ : ℕ, ∀ (L : Side), n₀≤L.val → ∀ (patch : Patch), patch.Branches P.bind G →
    ∀ (W μ : ℝ), 0<W → 0<μ → ∀ (o : Target.Order G W) (v : ℝ → ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop, 0≤v x) → ∀ (n j : ℕ) (χ : Chi),
    ∃ (a b B q r : ℝ → ℝ) (C₀ : ℝ) (l : ℕ), Rate G L (-((n+4:ℕ):ℝ)/2) a ∧
      Rate G L 0 b ∧ Rate G L 0 B ∧ ∀ᶠ x in atTop,
      ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f) (C : ℝ)
      (H : Cash W x μ L Q o C T R), S.patch=patch → Stamp T →
      ∃ Ξ : Utopia H j (v x) (q x) (r x) C₀ χ, ∀ (M : Team R) (p : H.ThinP) (i : Trans f),
      M.signs S ⊆ p.val → Ac.Spark H.supportP p.val → troupe T R Q.halo (radiusB x) p.val →
      atomFoot S.ratio Q.halo (radiusB x) R.path.cubic i ⊆ H.unionP p.val →
      ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x → X.width=o.K → X.manifest → X.χ=χ →
      Healthy (Pressure.temp x) (H.unionP p.val) X.V →
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (V : E → Config G c) (y : E), Mode V y j (v x) → V y=X.V →
      let η := -Raw.orientation*R.beta
      let K := debt (primary G) (n+3) R.path.cubic R o.a η i
      let α := bill (a x) (b x) η x R.path.cubic i
      let τ := seating Q.halo x S R.path.cubic i
      Brush j (expense M p (|B x|) α τ j l Ξ) 1 (fun z =>
        Port.average (vary X (V z)) (podium S G (H.unionP p.val) (radiusB x))
          (fun F X z => Orbit.hero M H p F X z * K F X z)) y := by
  obtain ⟨m,hM⟩ := Oboe.invoiceFundedRows P Q
  obtain ⟨k,hK⟩ := LocalTaylorR2.pearls P Q
  refine ⟨max m k,?_⟩
  intro L hL patch branches W μ hW hμ o v hv pos n j χ
  obtain ⟨A,c,hA⟩ := Eider.weave G
  obtain ⟨s,hs,hr⟩ := exists_between Q.start
  obtain ⟨C,d,r,B,l,hB,read⟩ := hM L ((le_max_left ..).trans hL) patch branches j 0 χ 1 W hW μ hμ o A c hA v hv pos
  obtain ⟨C₁,d₁,r₁,b₁,D,p,k₁,l₁,hd,_,_,_,_,stocks⟩ :=
    hK L ((le_max_right ..).trans hL) s 0 hs hr le_rfl patch branches j χ W hW μ hμ o A c hA v hv pos
  obtain ⟨a,b,ha,hb,paid⟩ := WilsonHeldCubicHistory.original P o Q L patch branches v d₁ hv hd pos n j χ
  refine ⟨a,b,B,d,r,C,l,ha,hb,hB,?_⟩
  filter_upwards [read,stocks,paid] with x ready funds test c' f' S T R C' H draw stamp
  have cap := H.laws.intake.cap.labels.boundE
  rw [H.laws.data.funds.length_eq] at cap
  obtain ⟨Ξ,_,_,host,ob⟩ := ready c' f' S T draw stamp R C' H _ (ManuscriptQLocalMarkedHeight.pumps cap)
  obtain ⟨_,Ξ₁,_,st⟩ := funds c' f' S T draw stamp R C' H
  exact ⟨Ξ,test c' f' S T R μ C' H draw st host ob⟩

end YM.Integration.WilsonHeldCubicCourse
