import YM.Integration.WilsonHeldKineticTeamIntegral

/-! The genuine cubic part of the incoming Wilson action in its original
moving affine marginal, with every previously entered signed spectator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonHeldCubicHistory
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy LocalTaylorR2 LocalTaylorR2.Kiln
open Axial Channel Canvas Itinerary Port WilsonHeldKineticTeamIntegral
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f} {P : Teller G}
    {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
    {H : Cash W s μ L Q o C T R}

private theorem minus {U : Support c} {K K' : Port.Test T}
    (a : Kept H U K) (b : Kept H U K') : Kept H U (fun F X w => K F X w-K' F X w) := by
  constructor
  · intro F X Y z w hx hk Z stored same equal
    rw [a.links F X Y z w hx hk Z stored same equal,b.links F X Y z w hx hk Z stored same equal]
  · intro E _ F X hx hk V Y w hV hY hw
    exact (a.borel E F X hx hk V Y w hV hY hw).sub (b.borel E F X hx hk V Y w hV hY hw)
  · intro F X hx hk hue z w
    rw [a.rotate F X hx hk hue z w,b.rotate F X hx hk hue z w]
  intro F X hx hk hm j v d E _ _ _ V x hv hd hw
  exact (a.clutch F X hx hk hm j v d E V x hv hd hw).plusminus
    (b.clutch F X hx hk hm j v d E V x hv hd hw)

theorem kept (H : Cash W s μ L Q o C T R) (patch : Patch) (hp : patch.Branches P.bind G)
    (draw : S.patch=patch) (p : ℕ) (i : Trans f) :
    Kept H (atomFoot S.ratio Q.halo (radiusB s) R.path.cubic i)
      (debt (primary G) p R.path.cubic R o.a (-Raw.orientation*R.beta) i) := by
  let A := R.path.cubic
  let η := -Raw.orientation*R.beta
  have physical : Kept H (atomFoot S.ratio Q.halo (radiusB s) A i)
      (fun _ X w => living X o.a η A R i (worldZ X R.beta w)) :=
    logTest H (.inl (.inr (.inl i)))
  have jet := snuffed H A η i p patch hp draw (H.laws.intake.cap.paths.invariant _).2.1 physical
  exact minus physical jet

theorem original {W : ℝ} (P : Teller G) (o : Target.Order G W) (Q : ConnectedActivityE6.Target G P)
    (L : Side) (patch : Patch) (hp : patch.Branches P.bind G) (v d : ℝ → ℝ)
    (hv : Rate G L (-(1/2)) v) (hd : Rate G L (-(1/2)) d) (pos : ∀ᶠ x in atTop, 0 ≤ v x)
    (n j : ℕ) (χ : Chi) :
    ∃ a b : ℝ → ℝ, Rate G L (-((n+4:ℕ):ℝ)/2) a ∧ Rate G L 0 b ∧
      ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f) (μ C : ℝ)
      (H : Cash W x μ L Q o C T R), S.patch=patch →
      ∀ {A D h d₀ r q B b₀ : ℝ} {k m l : ℕ} {Ξ : Utopia H j (v x) d₀ r q χ},
      StoresR2 H j (v x) (d x) A D k h m χ → HostQ H Ξ A B l → Oboe H j (v x) B l A b₀ Ξ →
      ∀ (M : Team R) (p : H.ThinP) (i : Trans f),
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
      Brush j (expense M p B α τ j l Ξ) 1 (fun z =>
        Port.average (vary X (V z)) (podium S G (H.unionP p.val) (radiusB x))
          (fun F X z => Orbit.hero M H p F X z * K F X z)) y := by
  obtain ⟨a,b,ha,hb,reads⟩ := portrait G P o L (primary G) patch hp v d hv hd pos 3 j (n+3) χ Q.halo
  refine ⟨a,b,ha,hb,reads.mono ?_⟩
  intro x hrs c f S T R μ C H draw A D h d₀ r q B b₀ k m l Ξ st host ob M p i all spark tr inc F X hx hk hm hχ healthy E _ _ _ V y mode base
  dsimp only
  have seen := hrs c f S T R Q μ C H draw (-Raw.orientation*R.beta) R.path.cubic i
    (H.laws.intake.cap.paths.invariant _).2.1
  exact integrated st host ob M p all spark tr _ ((kept H patch hp draw (n+3) i).mono inc)
    (positiveBill ..) (zero_le_one.trans (sit_ge ..)) seen X hx hk hm hχ healthy V y mode base

end YM.Integration.WilsonHeldCubicHistory
