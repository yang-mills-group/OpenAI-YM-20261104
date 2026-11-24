import YM.Integration.SelectedCofactorGaugeProjection
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! One complex chamber observable attaining the full signed polynomial price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorPriceReadout
open Function Finset Set Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags SelectedCofactorLocalProjection
open scoped Classical BigOperators Topology
open SelectedCofactorGaugeProjection
variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V}

omit [Fintype V] in
/-- A single complex linear reading attains the weighted mode price after the
original signed insertion has been integrated. -/
theorem norming {w : V → ℝ} (hw : ∀ v, 0 < w v) (y : Poly B) :
    ∃ L : Poly B →L[ℂ] ℂ, (∀ b, ‖L b‖ ≤ Poly.price w b) ∧ L y = (Poly.price w y : ℂ) := by
  choose k hk hy using fun i : B.Mode => exists_dual_vector'' ℂ (y.part i)
  let L : Poly B →L[ℂ] ℂ := ∑ i, (Poly.toll w i : ℂ) • (k i).comp (Poly.get i)
  have app (b : Poly B) : L b = ∑ i, (Poly.toll w i : ℂ) * k i (b.part i) := by
    simp only [L,_root_.sum_apply,_root_.smul_apply,
      ContinuousLinearMap.comp_apply,smul_eq_mul]
    rfl
  refine ⟨L,fun b => ?_,?_⟩
  · rw [app]
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Poly.worth hw i).le]
    apply mul_le_mul_of_nonneg_left _ (Poly.worth hw i).le
    exact ((k i).le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hk i) (norm_nonneg _)).trans_eq (one_mul _))
  · simp only [app,hy,Poly.price,Complex.ofReal_sum,Complex.ofReal_mul]
    rfl

variable {G : Gauge}
variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V} {J : Request V}
variable {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F} {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)

local notation "w₀" => (fun v => F.outputRadii v / F.kernelCosts v)

/-- The true finite-volume signed price is the expectation of one hot local
gauge-invariant observable on the original coarse Wilson scene. -/
theorem selected (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta order)
    (x : IndependentTests J.tests) (A₀ X : Set (Site n₀)) (hX : X ⊆ deep A₀)
    (Q : (ℕ × Finset ℕ) → Prop) :
    ∃ L : Poly B →L[ℂ] ℂ, (∀ b, ‖L b‖ ≤ Poly.price w₀ b) ∧
      let f := orbit (readout S x A₀ X Q L)
      Interior A₀ f ∧ (∀ t ≤ S.output.carrier.rep.p.threshold, ∀ U, f U ≠ 0 → ∃ z ∈ X, z ∈ flags t U) ∧
        (∫ U, f U ∂scene C.path datum.cutoff datum.period datum.level) =
          (Poly.price w₀ (Z₀⁻¹ • ∑' j : {a : ℕ × Finset ℕ // (rootEdge S a.1).1 ∈ X ∧ Q a},
            exteriorPacket S x j.val) : ℂ) := by
  let y : Poly B := Z₀⁻¹ • ∫ U, rooted S x X Q U ∂prior G n₀
  have hw v : 0 < w₀ v := div_pos (F.output_radius_positive v) (F.kernel_positive v)
  obtain ⟨L,hL,hv⟩ := norming hw y
  obtain ⟨hI,hH,hp⟩ := SelectedCofactorGaugeProjection.selected hC S H x A₀ X hX Q L
  refine ⟨L,hL,hI,hH,hp.trans ?_⟩
  have en := rooted_envelope hC S H x X Q
  obtain ⟨c,hc⟩ := en.cost
  have hi : Integrable (rooted S x X Q) (prior G n₀) :=
    Integrable.of_bound en.meas.aestronglyMeasurable c (ae_of_all _ hc)
  let Lr := L.restrictScalars ℝ
  have He : ∫ U, L (rooted S x X Q U) ∂prior G n₀ = L (∫ U, rooted S x X Q U ∂prior G n₀) :=
    Lr.integral_comp_comm hi
  calc
    _ = L y := by
      rw [He]
      change (Z₀:ℂ)⁻¹ * Lr (∫ U, rooted S x X Q U ∂prior G n₀) = Lr (Z₀⁻¹ • _)
      rw [Lr.map_smul,Complex.real_smul,Complex.ofReal_inv]
    _ = (Poly.price w₀ y : ℂ) := hv
    _ = _ := by simp only [y,rooted_integral hC S H x X Q]

end YM.Integration.SelectedCofactorPriceReadout
end
