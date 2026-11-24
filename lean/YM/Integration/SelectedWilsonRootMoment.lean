import YM.Integration.SelectedWilsonForward
import YM.Integration.WilsonPhysicalEventPrice
import YM.Integration.FullQLocalRetainedModelPrice

/-! Measurable prescribed model and true hot-event moments of a selected
signed defect against every original bounded fine signed source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedWilsonRootMoment
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato PhysicalNext.ThroughLaunch LocalComparison LocalComparison.Global
open IterationFour IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open MergeProof MergeProof.Accent OPE.Therm OPE.Therm.House
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
local notation "W₁" => C.path.rep datum.cutoff datum.period (datum.level+1)
local notation "nc" => C.side datum.level datum.period
local notation "nf" => C.side (datum.level+1) datum.period
local notation "w₀" => fun i => F.outputRadii i/F.kernelCosts i
local notation "c₀" => MarkedPackets.uniformModelCost caps.packetRank (Fintype.card V) (K.geometry datum.level)

/-- Whole true prescribed-model field under a complete physical dual. -/
theorem model (hC : C.Makes) (S : Chosen K I M) (x : IndependentTests J.tests) (L : Poly B →L[ℂ] ℂ)
    (hL : ∀ y, ‖L y‖ ≤ Poly.price w₀ y) : Envelope (fun U => L (S.output.modelValue (testInclusion J.tests x) U)) := by
  have hg : Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1) ≠ 0 :=
    inv_ne_zero ((Real.sqrt_pos.2 (Overlay.beta_positive hC.wilson (Nat.succ_le_of_lt datum.below))).ne')
  have h : Envelope (S.output.modelValue (testInclusion J.tests x)) := by
    change Envelope (fun U => Poly.pass (S.output.model.read (testInclusion J.tests x)
      (Pert.Asymptotics.regulatorRun C datum.cutoff datum.period (datum.level+1)) U))
    rw [S.same_model]
    exact M.prescribed.multiplier_envelope M.paid hg (testInclusion J.tests x)
  exact ⟨L.continuous.measurable.comp h.meas,c₀, fun U => (hL _).trans (S.uniform_model_price x U)⟩

/-- The common true Wilson hot-event inequality at this level. -/
def Hot (C : Family G) (m : ℕ) : Prop := ∀ (N : ℕ), m < N → ∀ p (X : Finset (Site (C.side m p)))
    (g : Config G (C.side (m+1) p) → ℂ) (model t : Config G (C.side m p) → ℂ),
    Envelope g → Envelope model → Envelope t → (∀ W, ‖t W‖ ≤ 1) →
    (∀ W, t W ≠ 0 → ∃ z ∈ X, z ∈ flags (cool C.path.levels m) W) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (∀ T, ‖g T‖ ≤ a) → (∀ W, ‖model W‖ ≤ b) →
    ‖∫ W,t W*(actualAverage C (N:=N) g W-model W) ∂scene C.path N p m‖ ≤
      (((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*vanishP C.path.levels m)*(a+b)

theorem eventual (hC : C.Makes) (hG : G.Simple) (θ : Poetry C.path.levels) : ∀ᶠ m in atTop,Hot C m :=
  WilsonPhysicalEventPrice.paired hC hG θ

/-- The actual selected model is retained and paid by its original rank and
geometry. The fine bill belongs to one signed preimage of the complete
selected input density. All exterior gauge fields remain unrestricted. -/
theorem selected (hC : C.Makes) (good : Hot C datum.level) (S : Chosen K I M)
    (x : IndependentTests J.tests) (L : Poly B →L[ℂ] ℂ) (hL : ∀ y, ‖L y‖ ≤ Poly.price w₀ y)
    (g : Config G nf → ℂ) (hg : Envelope g) (a : ℝ) (ha : 0 ≤ a) (hp : ∀ T, ‖g T‖ ≤ a)
    (pre : ∀ T,L ((I.input.leaf (testInclusion J.tests x)).density T) = (W₁).eval T • g T)
    (X : Finset (Site nc)) (t : Config G nc → ℂ) (ht : Envelope t) (h1 : ∀ W, ‖t W‖ ≤ 1)
    (root : ∀ W, t W ≠ 0 → ∃ z ∈ X,z ∈ flags (cool C.path.levels datum.level) W) :
    ‖∫ W,t W*L (ActualSelectedModelIntegral.defect S (testInclusion J.tests x) W) ∂scene C.path datum.cutoff datum.period datum.level‖ ≤
      (((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*vanishP C.path.levels datum.level)*(a+c₀) := by
  simp_rw [SelectedWilsonForward.residual hC S (testInclusion J.tests x) L g pre]
  have h0 : 0 ≤ c₀ := (norm_nonneg (L (S.output.modelValue (testInclusion J.tests x) (fun _ => 1)))).trans
    ((hL _).trans (S.uniform_model_price x (fun _ => 1)))
  exact good datum.cutoff datum.below datum.period X g _ t hg (model hC S x L hL) ht h1 root a c₀ ha h0 hp
    (fun U => (hL _).trans (S.uniform_model_price x U))

end YM.Integration.SelectedWilsonRootMoment
