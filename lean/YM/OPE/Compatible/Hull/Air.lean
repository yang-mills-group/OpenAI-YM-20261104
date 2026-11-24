import YM.OPE.Compatible.Hull.Loom
import YM.OPE.Compatible.Hull.Bud
import YM.OPE.Compatible.Sward.Lucent
/-!
# Build fixed-height real analytic×smooth LP mark extraction. Uniform Scrape.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{E X F:Type}{n:Side}(o:Site n){b i k r m:ℕ}{C:KernelChoices}
open Finset
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin Module
open Source Labels Source.Drops
section
variable (H:Hol G){d k:ℕ}
abbrev burstQ (H:Hol G)(b:ℕ)(F:Snap G d):Scoop G b:= Exposure b (board (Hig H F))
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 200000
private lemma component_norm {X Y I : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [Fintype I] {k : ℕ} {M : ℝ}
    (f : I → X → Y) (hf : ContDiffAt ℝ k (fun x i => f i x) 0) (hM : 0 ≤ M)
    (h : ∀ i, ‖iteratedFDeriv ℝ k (f i) 0‖ ≤ M) :
    ‖iteratedFDeriv ℝ k (fun x i => f i x) 0‖ ≤ M := by
  apply ContinuousMultilinearMap.opNorm_le_bound hM
  intro v
  have hv : 0 ≤ ∏ j, ‖v j‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM hv)).2
  intro i
  let q : (I → Y) →L[ℝ] Y := ContinuousLinearMap.proj i
  have he := DFunLike.congr_fun (q.iteratedFDeriv_comp_left hf le_rfl) v
  rw [show (iteratedFDeriv ℝ k (fun x j => f j x) 0 v) i = iteratedFDeriv ℝ k (f i) 0 v from he.symm]
  exact ((iteratedFDeriv ℝ k (f i) 0).le_opNorm v).trans (mul_le_mul_of_nonneg_right (h i) hv)

private lemma bundle_bounds {X Y Z I : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [Fintype I] {k : ℕ} {M B : ℝ} (f : I → X → Y) (L : (I → Y) →L[ℝ] Z)
    (hB : 0 ≤ B) (hL : ‖L‖ ≤ B) (hM : 0 ≤ M) (hf : ∀ i, ContDiffAt ℝ k (f i) 0)
    (hf0 : ∀ i, f i 0 = 0) (h : ∀ i, ‖iteratedFDeriv ℝ k (f i) 0‖ ≤ M) :
    let F := L ∘ fun x i => f i x
    ContDiffAt ℝ k F 0 ∧ F 0 = 0 ∧ ‖iteratedFDeriv ℝ k F 0‖ ≤ B*M := by
  let g := fun x i => f i x
  have hg : ContDiffAt ℝ k g 0 := contDiffAt_pi.mpr hf
  have h0 : g 0 = 0 := funext hf0
  exact ⟨L.contDiff.contDiffAt.comp 0 hg, (congrArg L h0).trans L.map_zero,
    (L.norm_iteratedFDeriv_comp_left hg le_rfl).trans
      (mul_le_mul hL (component_norm f hg hM h) (norm_nonneg _) hB)⟩

private lemma bundle_derivative {X Y Z I : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [Fintype I] (f : I → X → Y) (L : (I → Y) →L[ℝ] Z) (hf : ∀ i, DifferentiableAt ℝ (f i) 0)
    (x : X) : fderiv ℝ (L ∘ fun y i => f i y) 0 x = L (fun i => fderiv ℝ (f i) 0 x) := by
  have h := L.hasFDerivAt.comp 0 (hasFDerivAt_pi.mpr fun i => (hf i).hasFDerivAt)
  exact DFunLike.congr_fun h.fderiv x

attribute [local instance] Drops.instNormedSpaceRealSnap

lemma GlassS (H:Hol G)(k d:ℕ): ∃ C:ℝ, ∃ q:ℕ,0≤C ∧ ∀ b:ℕ, ContDiffAt ℝ k (burstQ H b) (0:Snap G d) ∧ burstQ H b (0:Snap G d)=0 ∧ slopeCap k (burstQ H b) (0:Snap G d)≤ C*(1+(b:ℝ))^q:=by
  obtain ⟨C, q, hc, h⟩ := soar H d k
  obtain ⟨g, hg, hV⟩ := strideSize G
  refine ⟨g*C, q, mul_nonneg (zero_le_one.trans hg) hc, fun b => ?_⟩
  rw [mul_assoc]
  exact bundle_bounds (fun (i : TilesB b) => LeapV (d := d) H i.val)
    (strideG G b).toContinuousLinearMap (zero_le_one.trans hg) (hV b).1
    (mul_nonneg hc (by positivity)) (fun i => (h b i).1) (fun i => Leap0 H i) (fun i => (h b i).2)

-- Forest curvature on the exposed field.
lemma Ky (b:ℕ)(x:Snap G d): fderiv ℝ (burstQ H b) 0 x = Packer G b (Exposure _ (Sie x)):=by
  let f (i : TilesB b) : Snap G d → G.Color := LeapV H i.val
  have h (i : TilesB b) : DifferentiableAt ℝ (f i) 0 :=
    ((soar H d 1).choose_spec.choose_spec.2 b i).1.differentiableAt one_ne_zero
  rw [Fort]
  exact (bundle_derivative f (strideG G b).toContinuousLinearMap h x).trans
    (congrArg (strideG G b) (funext fun i => äder H i x))
noncomputable def sprintD (b:ℕ)(θ:ℝ)(A:Snap G d):ℝ→Scoop G b:= θ⁻¹ • (burstQ H b ∘ (θ • flash A))
noncomputable def spanT (b:ℕ)(A:Snap G d):ℝ→ Scoop G b:= (fderiv ℝ (burstQ H b) 0) ∘ flash A
lemma spanI (b:ℕ)(A:Snap G d)(k:ℕ): iteratedDeriv k (spanT H b A) 0= Packer G b (Exposure _ (Sie (iteratedDeriv k (flash A) 0))):=by
        rw [spanT,guiding (fderiv ℝ (burstQ H b) 0) _ k 0 ((flashDiff A).contDiffAt),Ky]
end
end YM.OPE.Spells
