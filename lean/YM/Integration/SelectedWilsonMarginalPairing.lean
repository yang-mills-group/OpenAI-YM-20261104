import YM.Integration.WilsonSpectatorReflection
import YM.Integration.SelectedCofactorLocalProjection
import YM.Push.GRID_APPROXIMATION.KernelLocal

/-! Retained probes see the signed packet on the original fine Wilson run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedWilsonMarginalPairing

open Function Finset Set MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open RG3.Forms RG3.Script.Picnic OPE.Therm Push.GridApprox
open SelectedCofactorChamberMarginal SelectedCofactorLocalProjection SelectedCofactorReplicatedFlags
open scoped Classical BigOperators Topology

variable {G : Gauge} {n : Side}

/-- The positive-normalized signed marginal pairs with every bounded
measurable retained-field probe, including probes depending on all retained links. -/
theorem weighted (D : Set (Edge (Site n))) {P : Config G n → ℝ} {f : Config G n → ℂ}
    (hP : Envelope P) (hf : Envelope f) {a : ℝ} (ha : 0 < a) (hl : ∀ U, a ≤ P U)
    (φ : Fields G D → ℂ) (hφ : Envelope φ) :
    (∫ U, P U • (φ (((cut G D) U).1) * projected D P f U) ∂prior G n) =
      ∫ U, φ (((cut G D) U).1) * f U ∂prior G n := by
  let read (U : Config G n) := ((cut G D) U).1
  have hread : Measurable read := measurable_fst.comp (cut G D).measurable
  have hh := pairing D hP ((hφ.comp_env hread).mulC hf) ha hl
  have hp (U : Config G n) : projected D P (fun T => φ (read T)*f T) U = φ (read U)*projected D P f U := by
    have hm (u : Fields G D) : marginal D (fun T => φ (read T)*f T) u = φ u * marginal D f u := by
      simp only [marginal,read,MeasurableEquiv.apply_symm_apply]
      exact integral_const_mul _ _
    simp only [projected,hm,Complex.real_smul,read]
    ring
  simpa only [hp] using hh

variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V} {J : Request V}
variable {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "n₁" => C.side (datum.level+1) datum.period
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "op₀" => C.path.levels.clock.op datum.level datum.period
local notation "b₀" => C.path.β datum.cutoff datum.period (datum.level+1)
local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)

/-- The exact original Wilson expectation of the pulled-back, tested sparse
readout is the corresponding joint signed packet integral divided by its
original common partition. All exterior partners remain in the integrand. -/
theorem fine (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta order)
    (x : IndependentTests J.tests) (A₀ X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop)
    (L : Poly B →L[ℂ] ℂ) (φ : Fields G (links A₀) → ℂ) (hφ : Envelope φ) :
    let r := fun U : Config G n₀ => φ (((cut G (links A₀)) U).1) * readout S x A₀ X Q L U
    C.omega datum.cutoff datum.period (backTo C.path datum.cutoff datum.period datum.below.le r) =
      (Z₀ : ℂ)⁻¹ * ∫ U, φ (((cut G (links A₀)) U).1) * L (rooted S x X Q U) ∂prior G n₀ := by
  intro r
  have hroot := rooted_envelope hC S H x X Q
  have hraw : Envelope (fun U => L (rooted S x X Q U)) :=
    ⟨L.continuous.measurable.comp hroot.meas,‖L‖*hroot.cost.choose,fun U => (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hroot.cost.choose_spec U) (norm_nonneg _))⟩
  have hp := (W₀).envelope (hC.wilson.represents _ _ _ datum.below.le).good
  obtain ⟨a,ha,hl⟩ := SelectedCofactorLocalProjection.floor hC (p:=datum.period) datum.below
  have hr : Envelope r := (hφ.comp_env (measurable_fst.comp (cut G (links A₀)).measurable)).mulC
    (SelectedCofactorLocalProjection.realization hC S H x A₀ X Q L).2.1
  have hi : Integrable (backTo C.path datum.cutoff datum.period datum.below.le r)
      (law G (C.side datum.cutoff datum.period) (C.beta datum.cutoff datum.period)) :=
    (backTo_env C.path datum.cutoff datum.period datum.below.le hr).integrableC _
  have hscene := (onstage (H:=C.path) (p:=datum.period) hC.wilson _ hi).symm.trans
    (retro (H:=C.path) (p:=datum.period) hC.wilson datum.below.le le_rfl r hr)
  have htest := weighted (links A₀) hp hraw ha hl φ hφ
  rw [violet (H:=C.path) (p:=datum.period) hC.wilson datum.below.le,div_eq_inv_mul] at hscene
  apply hscene.trans
  exact congrArg (fun z : ℂ => (Z₀ : ℂ)⁻¹*z) (by simpa only [r,readout,Complex.real_smul] using htest)

/-- The coarse nonzero readout has an actual physical hot flag. Its full
adjoint is supported on the native fine reach of the retained links. -/
theorem support (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta order)
    (x : IndependentTests J.tests) (A₀ X : Set (Site n₀)) (hX : X ⊆ deep A₀)
    (Q : (ℕ × Finset ℕ) → Prop) (L : Poly B →L[ℂ] ℂ) {t : ℝ} (ht : t ≤ S.output.carrier.rep.p.threshold)
    (Y₁ : Set (Site n₁)) (hY : ∀ z ∈ A₀, window ((op₀).ratio.embed z) (reach (op₀).patch) ⊆ Y₁) :
    (∀ U, readout S x A₀ X Q L U ≠ 0 → ∃ z ∈ X, z ∈ flags t U) ∧
      LocalOn Y₁ (back op₀ b₀ (readout S x A₀ X Q L)) := by
  have hs := SelectedCofactorLocalProjection.realization hC S H x A₀ X Q L
  exact ⟨SelectedCofactorLocalProjection.hot S x A₀ X hX Q L ht,
    back_local (S := op₀) (C.path.levels.blocks datum.level datum.period).branches hs.2.1 hs.1 b₀ Y₁ hY⟩

end YM.Integration.SelectedWilsonMarginalPairing
