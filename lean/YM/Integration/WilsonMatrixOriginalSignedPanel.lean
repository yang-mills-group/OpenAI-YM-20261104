import YM.Integration.WilsonMatrixOriginalActionReality
import YM.Integration.WilsonMatrixOriginalPolarReadout
import YM.Integration.WilsonMatrixOriginalSignedReading

/-! A fixed signed covariance of the actual elementary fields has a positive lower margin. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalSignedPanel
open Filter Function Set Table Spec Climb Spin Trace.Pilot Trace.Over TraceExtension PhysMS
open Next.UVStress PhysicalNext.Repeat.Legato Extraction Extraction.Order Push.GridApprox
open WilsonMatrixOriginalRealFields WilsonMatrixOriginalSignedReading WilsonInvariantActionPairCovariance
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S)

private theorem choose_component {c : ℂ} (nonzero : c ≠ 0) :
    ∃ χ : ℂ →L[ℝ] ℝ, (χ = Complex.reCLM ∨ χ = Complex.imCLM) ∧ 0 < |χ c| := by
  by_cases hr : c.re = 0
  · have hi : c.im ≠ 0 := fun h => nonzero (Complex.ext hr h)
    exact ⟨Complex.imCLM,Or.inr rfl,abs_pos.mpr hi⟩
  · exact ⟨Complex.reCLM,Or.inl rfl,abs_pos.mpr hr⟩

private theorem dilate_real (φ : Test 2) (real_test : ∀ x, φ x = ((φ x).re : ℂ))
    {r : ℝ} (hr : 0 < r) (x : Points 2) :
    dilate hr φ x = (((dilate hr φ x).re : ℝ) : ℂ) := by
  change (((r ^ (4*2))⁻¹ : ℝ) : ℂ) * φ (r⁻¹ • x) =
    (((((r ^ (4*2))⁻¹ : ℝ) : ℂ) * φ (r⁻¹ • x)).re : ℂ)
  rw [real_test (r⁻¹ • x),←Complex.ofReal_mul]
  rfl

include F in
theorem ordered (cut : (N p : ℕ) → Fin (N+1)) (φ : Test 2)
    (real_test : ∀ x, φ x = ((φ x).re : ℂ)) (χ : ℂ →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r)
    (y b : S.Field 4)
    (real_action : centering S 4 (S.project 4 (realLabel (R:=R) (S.representative 4 y))) = centering S 4 y) :
    f.limits (fun p => suitable R.family.S p (dilate hr φ))
      (signed R (S.representative 4 y) (S.representative 4 b) χ (dilate hr φ))
      (χ (tested y b r φ)) := by
  have read := WilsonMatrixOriginalPolarReadout.ordered F cut φ hr
    (realLabel (R:=R) (S.representative 4 y)) (S.representative 4 b)
  rw [S.rep] at read
  have same : tested (S.project 4 (realLabel (R:=R) (S.representative 4 y))) b r φ =
      tested y b r φ := by
    unfold WilsonInvariantActionPairCovariance.tested covariance
    simp only [real_action]
  rw [same] at read
  obtain ⟨ok,v,inner,outer⟩ := read
  refine ⟨ok,fun p => χ (v p),?_,(χ.continuous.tendsto _).comp outer⟩
  intro p hp
  apply ((χ.continuous.tendsto _).comp (inner p hp)).congr'
  filter_upwards [f.mesh.cofinal.eventually (eventually_ge_atTop (R.family.ref 4))] with k hk
  exact measured R cut _ _ χ _ (dilate_real φ real_test hr) hk

def Row (b : ℝ → S.Field 4) (φ : Test 2) (χ : ℂ →L[ℝ] ℝ) {r : ℝ} (hr : 0 < r) :
    ℕ → ℕ → ℝ :=
  signed R (S.representative 4 (J r 4 (stepField R.family))) (S.representative 4 (b r)) χ (dilate hr φ)

def Lower (b : ℝ → S.Field 4) (φ : Test 2) (c : ℂ) (χ : ℂ →L[ℝ] ℝ) : Prop :=
  (χ = Complex.reCLM ∨ χ = Complex.imCLM) ∧ 0 < |χ c| ∧
    ∀ᶠ r in trail, ∀ hr : 0 < r,
      let v := χ (tested (J r 4 (stepField R.family)) (b r) r φ)
      |χ c| / 2 < |v| ∧
      f.limits (fun p => suitable R.family.S p (dilate hr φ)) (Row J b φ χ hr) v ∧
      (∀ᶠ z : ℕ × ℕ in f.fuse, |χ c| / 4 < |Row J b φ χ hr z.1 z.2|) ∧
      ∀ (cut : (N p : ℕ) → Fin (N+1)) (N p : ℕ), R.family.ref 4 ≤ N →
        χ (WilsonInvariantActionIntegratedPair.profile R cut
          (realLabel (R:=R) (S.representative 4 (J r 4 (stepField R.family))))
          (S.representative 4 (b r)) (dilate hr φ) N p) = Row J b φ χ hr N p

theorem on_column (simple : G.Simple) {P : ℝ → change S 4} {δ g : ℝ → ℝ}
    (same : ∀ᶠ r in trail, J r 4 = P r) (cal : TendC F P δ) (coupling : Coupling G g)
    (b : ℝ → S.Field 4) (φ : Test 2) (real_test : ∀ x, φ x = ((φ x).re : ℂ))
    (c : ℂ) (nonzero : c ≠ 0)
    (convergence : Tendsto (fun r => tested (J r 4 (stepField R.family)) (b r) r φ) trail (𝓝 c)) :
    ∃ χ : ℂ →L[ℝ] ℝ, Lower (f:=f) J b φ c χ := by
  obtain ⟨χ,chosen,hc⟩ := choose_component nonzero
  refine ⟨χ,chosen,hc,?_⟩
  have tends := (continuous_abs.tendsto _).comp ((χ.continuous.tendsto _).comp convergence)
  have away := tends.eventually (lt_mem_nhds (half_lt_self hc))
  filter_upwards [away,WilsonMatrixOriginalActionReality.ward F J simple same cal coupling] with r gap fixed
  intro hr
  let cut (N _ : ℕ) : Fin (N+1) := ⟨N,Nat.lt_succ_self N⟩
  have ready := ordered F cut φ real_test χ hr _ (b r) fixed
  refine ⟨gap,ready,?_,?_⟩
  · exact ((continuous_abs.tendsto _).comp (Extraction.Order.along ready)).eventually
      (lt_mem_nhds (lt_trans (show |χ c|/4 < |χ c|/2 by linarith) gap))
  · intro cut' N p hn
    exact measured R cut' _ _ χ _ (dilate_real φ real_test hr) hn

end YM.Integration.WilsonMatrixOriginalSignedPanel
