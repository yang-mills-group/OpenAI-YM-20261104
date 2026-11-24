import YM.Integration.WilsonConditionalTaylorCourseAttachment
import YM.Integration.WilsonConditionalTaylorCaliperPayment
import YM.Integration.WilsonConditionalTaylorPurchase

/-! The selected Wilson run buys the caliper sampling condition at every
stage on every torus. Its actual finite action and both measured coupling
coordinates therefore attach to the finite recursion without interchanging
the period and ultraviolet cutoff limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonUniformUnmarkedCourse
open Filter Function PowerSeries Lattice RG Wilson Tree Stationary Push.Uniform Bloch Exterior Precision
open FormalBulk08 Jets Flat Reef Mesa Lava Shore Lotus Wine Bank Orb Next.Free Series
open PhysicalNext.Repeat.Legato MSbar MSbar.Heath MSbar.Rolling MSbar.Cacao MSbar.Midpoint MSbar.Bakery MSbar.Bakery.Portal
open WilsonConditionalTaylorCourseAttachment WilsonConditionalTaylorFieldBalance WilsonConditionalTaylorSceneCalibration
open WilsonMovingPolynomialPull
open scoped Classical Topology

variable {G : Gauge} (R : Run G) (simple : G.Simple) (u : G.ColorIndex) (V : Voice G)
variable (bought : WilsonConditionalTaylorPurchase.Inventory u V R.kit)
variable (wood : ∀ j,Lodge (R.family.path.levels.clock.op j 0).patch)
variable (tags : ∀ j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

include simple bought in
theorem issued (N per k cap : ℕ) (S : Scene R.family.path.levels per cap)
    (law : Realized R.alloy.B.kin N per k cap (Lis.sun G u) S) (j : ℕ) (lo : k≤j) (hi : j≤N) :
    Fields cap (S.Poly j) (placed R u wood tags N per j) ∧
      (j<N → Through cap (S.action j) (bookU (price R u wood tags N per j)) ∧
        Through cap (S.action j)⁻¹ (bookH (price R u wood tags N per j))) := by
  have paid (i : ℕ) : Alto.Sampled (R.family.side i per) (R.family.path.levels.params i) :=
    WilsonConditionalTaylorCaliperPayment.pulse R u V bought.2.2 i per
  have fields (i : ℕ) (iN : i ≤ N) (ki : k ≤ i) :=
    sceneField R simple u wood tags law (fun m _ => paid m) i iN ki
  refine ⟨fields j hi lo,?_⟩
  intro step
  exact (nextField R simple u wood tags law j lo step (paid j) (fields (j+1) step (by omega))).2

include simple bought in
theorem actual (N per k cap : ℕ) (kN : k≤N) :
    ∃ S : Scene R.family.path.levels per cap,
      Realized R.alloy.B.kin N per k cap (Lis.sun G u) S ∧ ∀ j, k≤j → j≤N →
      Fields cap (S.Poly j) (placed R u wood tags N per j) ∧
        (j<N → Through cap (S.action j) (bookU (price R u wood tags N per j)) ∧
          Through cap (S.action j)⁻¹ (bookH (price R u wood tags N per j))) := by
  have growth : Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop := by
    apply tendsto_atTop.2
    intro h
    filter_upwards [eventually_ge_atTop (R.t h)] with j hj
    exact (Nat.le_succ h).trans (((R.makes.stages h).2 j hj).1)
  have dates := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have fortune := townsR R.b R.Q R.T R.t R.stories R.doors dates
  obtain ⟨S,law⟩ := Alto.chosen R.alloy.B simple (bought.2.2.1 growth).levy fortune N u cap per kN
  exact ⟨S,law,fun j lo hi => issued R simple u V bought wood tags N per k cap S law j lo hi⟩

end YM.Integration.WilsonUniformUnmarkedCourse
