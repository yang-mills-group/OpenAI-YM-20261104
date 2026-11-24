import YM.Integration.WilsonHeldKineticSectorPurchase
import YM.LocalTaylorR2.Orbit.Hero
import YM.LocalLTE.Marked.Strength

/-! Integrate a tested local remainder with a whole signed incoming team in
the original moving conditional law. The Gaussian density occurs once. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonHeldKineticTeamIntegral
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy LocalTaylorR2 LocalTaylorR2.Port
open Itinerary Port
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {R : Rep G f} {P : Teller G}
    {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W}
    {H : Cash W s μ L Q o C T R} {j k n l : ℕ} {v d d₀ A D h t r q B b : ℝ} {χ : Chi}
    {Ξ : Utopia H j v d₀ r q χ}

def expense (M : Team R) (p : H.ThinP) (B a t : ℝ) (j l : ℕ) (Ξ : Utopia H j v d r q χ) : ℝ :=
  B * (M.weight * (∏ i ∈ p.val \ M.signs S, Ξ.tag i) * Ξ.rad^(blaze p.val).card *
    (1+H.shapeW p.val)^l) * a * (1+(1+t))^j

theorem income (st : StoresR2 H j v d A D k h n χ) (host : HostQ H Ξ A B l)
    (M : Team R) (p : H.ThinP) (all : M.signs S ⊆ p.val)
    (sp : Ac.Spark H.supportP p.val) (tr : troupe T R Q.halo (radiusB s) p.val)
    (K : Port.Test T) {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (paid : Sees H j v d χ K a t) :
    IntegrandCost H (H.unionP p.val) (fun F X w => Orbit.hero M H p F X w * K F X w)
      j A v (expense M p B a t j l Ξ) χ := by
  constructor
  intro F X hx hk hm hχ healthy E _ _ _ V y mode base
  obtain ⟨f, hfi, hsum, point⟩ := host.nil M E F X V y p.val hχ hm hx hk
    (by simpa only [hx] using healthy) tr sp all mode base
  refine ⟨fun z => f z * a * (1+(1+t))^j, (hfi.mul_const _).mul_const _, ?_, ?_⟩
  · rw [integral_mul_const, integral_mul_const]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum ha) (by positivity)
  intro z
  let Y := X.wrapY z.1
  have flight := (st.flight F Y hx hχ hk hm z.2 E V y base mode).1
  have other := paid E F Y V _ _ y z.2 hx hk hm hχ mode flight
  have joint := ((point z).paints other).trim
  apply joint.shimmy
  filter_upwards with w
  simp only [Port.duoTilt, Port.tilted, Team.qlocal4a_carat, Team.qlocal4a_chimes,
    Team.qlocal4a_floret, if_pos all, Orbit.hero, Orbit.restP, Y, mul_assoc]

/-- The protected factor and every signed spectator share the true
tree-conditioned Gaussian and the same Haar integral over the held links. -/
theorem integrated (st : StoresR2 H j v d A D k h n χ) (host : HostQ H Ξ A B l)
    (ob : Oboe H j v B l A b Ξ) (M : Team R) (p : H.ThinP) (all : M.signs S ⊆ p.val)
    (sp : Ac.Spark H.supportP p.val) (tr : troupe T R Q.halo (radiusB s) p.val)
    (K : Port.Test T) (kept : Kept H (H.unionP p.val) K)
    {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (paid : Sees H j v d χ K a t)
    {F : Forest S.ratio} (X : Coat T F) (hx : X.x=s) (hk : X.width=o.K)
    (hm : X.manifest) (hχ : X.χ=χ) (healthy : Healthy (Pressure.temp s) (H.unionP p.val) X.V)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E → Config G c) (y : E) (mode : Mode V y j v) (base : V y = X.V) :
    Brush j (expense M p B a t j l Ξ) 1 (fun w =>
      Port.average (vary X (V w)) (podium S G (H.unionP p.val) (radiusB s))
        (fun F X w => Orbit.hero M H p F X w * K F X w)) y := by
  exact Port.lands hx hm hk ((Orbit.hero_test M H p all).times kept) ob
    (income st host M p all sp tr K ha ht paid) hχ healthy mode base

end YM.Integration.WilsonHeldKineticTeamIntegral
