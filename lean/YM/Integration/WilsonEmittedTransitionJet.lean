import YM.Integration.WilsonEmittedRecordedJet
import YM.Integration.WilsonEmittedChildCatalogue

/-! A polynomial coefficient of the genuine field transition acts on
the actual joint coupling and link jet before its common pole is restored. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedTransitionJet
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Comparison.RG02 AllOrder AllOrder.Floe Laurent PertExtension.Series
open AnalyticBridge.SectorAffine.Offset Comparison.Density WilsonEmittedWordJointFare
open scoped ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
local notation "Chart₀" => Chart G n
def fee (j ℓ : ℕ) (D : ℝ) := (2:ℝ)^j*(‖ContinuousLinearMap.lsmul ℝ ℝ (E:=ℂ)‖*(Render.couple j)^ℓ*D)
theorem marked (ℓ j : ℕ) {h : Chart₀→ℂ} {D : ℝ} (z : Chart₀) (unit : ‖z‖≤1)
    (priced : Through j h z D) :
    Through j (fun v:Chart₀=>v.1^ℓ • h v) z (fee j ℓ D) := by
  let fst := ContinuousLinearMap.fst ℝ ℝ (Directions G n)
  have hf : ‖fst‖≤1 := fst.opNorm_le_bound zero_le_one fun v=>by simpa [fst] using norm_fst_le v
  have one : Through j (fun v:Chart₀=>v.1) z 1 :=
    Through.control (Push.Uniform.allows_linear (L:=fst) hf ((norm_fst_le z).trans unit))
  have serial : Through j (fun v:Chart₀=>v.1^ℓ) z ((Render.couple j)^ℓ) := by
    simpa using (Render.band (x:=z) (s:=range ℓ) (f:=fun _ (v:Chart₀)=>v.1) (fun _ _=>one))
  exact Render.stitch (ContinuousLinearMap.lsmul ℝ ℝ (E:=ℂ)) serial priced

private def duplicate := (ContinuousLinearMap.fst ℝ ℝ (Directions G n)).prod (ContinuousLinearMap.id ℝ Chart₀)
private theorem real (ℓ j : ℕ) (f : Chart₀→ℝ) (hf : ContDiffAt ℝ ω f 0) (A : Directions G n) :
    Assembly.jet (fun z:Chart₀=>z.1^ℓ*f z) j (1,A) =
      if ℓ≤j then Assembly.jet f (j-ℓ) (1,A) else 0 := by
  let Φ (z:ℝ×Chart₀) := z.1^ℓ*f z.2
  have hΦ : ContDiffAt ℝ ω Φ 0 := (contDiffAt_fst.pow ℓ).mul (hf.comp (f:=Prod.snd) (0:ℝ×Chart₀) contDiffAt_snd)
  change Assembly.jet (Φ ∘ duplicate) j (1,A)=_
  rw [Assembly.jet_continuous_right duplicate (hΦ.of_le le_top)]
  change Radial.jet Φ j (1,((1,A):Chart₀))=_
  rw [AllOrder.Floe.favor_exp f hf]
  simp only [one_pow,one_mul]
  rfl

theorem original (ℓ j : ℕ) (f : Chart₀→ℂ) (hf : ContDiffAt ℝ ω f 0) (A : Directions G n) :
    Assembly.jet (fun z:Chart₀=>z.1^ℓ • f z) j (1,A) =
      if ℓ≤j then Assembly.jet f (j-ℓ) (1,A) else 0 := by
  let Φ (z:Chart₀) := z.1^ℓ • f z
  have hΦ : ContDiffAt ℝ ω Φ 0 := (contDiffAt_fst.pow ℓ).smul hf
  have leg (L : ℂ→L[ℝ] ℝ) : L (Assembly.jet Φ j (1,A))=
      L (if ℓ≤j then Assembly.jet f (j-ℓ) (1,A) else 0) := by
    rw [Assembly.jet_apply_left L Φ _ (hΦ.of_le le_top)]
    have rev : L ∘ Φ=fun z:Chart₀=>z.1^ℓ*(L ∘ f) z := by
      funext z
      exact L.map_smul (z.1^ℓ) (f z)
    rw [rev,real ℓ j _ (L.contDiff.contDiffAt.comp 0 hf) A]
    by_cases h : ℓ≤j
    · rw [if_pos h,if_pos h,Assembly.jet_apply_left L f _ (hf.of_le le_top)]
    · simp [h]
  exact Complex.ext (leg Complex.reCLM) (leg Complex.imCLM)

end YM.Integration.WilsonEmittedTransitionJet
end
