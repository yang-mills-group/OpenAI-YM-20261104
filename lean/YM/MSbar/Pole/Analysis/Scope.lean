import YM.MSbar.Pole.Analysis.Planes
import YM.MSbar.Pole.Analysis.Bottles
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Variants of finite-domain mixed holomorphy used for dimensional integration. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory
open scoped Topology ContDiff Classical
variable {E A : Type} [NormedAddCommGroup E] [NormedAddCommGroup A]
variable [NormedSpace ℝ E] [NormedSpace ℝ A] {f g : E → ℂ}
variable {v w : E} {x : E}
namespace CR
lemma germ (hf : CR v w f x) (he : g =ᶠ[𝓝 x] f) : CR v w g x := by
  unfold CR; rw [he.fderiv_eq]; exact hf
lemma mul (hf : CR v w f x) (hg : CR v w g x)
    (sf : DifferentiableAt ℝ f x) (sg : DifferentiableAt ℝ g x) : CR v w (fun x => f x*g x) x := by
  have he:= sf.hasFDerivAt.mul sg.hasFDerivAt; unfold CR
  change fderiv ℝ (f*g) x w=_*fderiv ℝ (f*g) x v
  rw [he.fderiv]
  change f x * fderiv ℝ g x w + g x * fderiv ℝ f x w = _*(f x*fderiv ℝ g x v+ g x* fderiv ℝ f x v)
  unfold CR at hf hg; rw [hf,hg]; ring
lemma hold (a : ℂ) : CR v w (fun _=>a) x := by simp [CR]
lemma comp (hf : CR v w f x) (sf : DifferentiableAt ℝ f x) {g : ℂ→ℂ} (sg : DifferentiableAt ℂ g (f x)) :
    CR v w (g ∘ f) x := by
  have he := ((sg.hasFDerivAt.restrictScalars ℝ).comp x sf.hasFDerivAt).fderiv
  unfold CR; rw [he]
  change fderiv ℂ g (f x) (fderiv ℝ f x w) = _ * fderiv ℂ g (f x) (fderiv ℝ f x v)
  unfold CR at hf; rw [hf]; exact map_smul (fderiv ℂ g (f x)) Complex.I (fderiv ℝ f x v)
lemma affine {L : E→L[ℝ] ℂ} (hf : L w=Complex.I*L v) (a) : CR v w (fun y => a+L y) x := by
  have he := (L.hasFDerivAt.const_add a (x:=x)) -- syntax
  unfold CR; rw [he.fderiv]; exact hf
lemma pull (hf : A→ℂ) {f : E→A} {d : E→L[ℝ] A} (sf : HasFDerivAt f d x) (sg : DifferentiableAt ℝ hf (f x))
    (h : CR (d v) (d w) hf (f x)) : CR v w (hf ∘ f) x := by unfold CR; rw [(sg.hasFDerivAt.comp x sf).fderiv]; exact h
end CR

lemma compact_packet {T : Set A} {q : Price A} {E'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {f : A→E'}
    (hT : IsCompact T) (h : ∀ x∈T,ContDiffAt ℝ ∞ f x) : Packet T q 1 f := by
  refine ⟨h, fun i => ?_⟩
  have hh : ContinuousOn (iteratedFDeriv ℝ i f) T := fun x hx => ((h x hx).continuousAt_iteratedFDeriv (by exact_mod_cast (show (↑i:ℕ∞)≤⊤ from le_top))).continuousWithinAt
  obtain ⟨M,hM⟩:= hT.bddAbove_image hh.norm
  exact Bills.bounded (C:=max 0 M) (le_max_left ..) (fun x hx => (hM (mem_image_of_mem _ hx)).trans (le_max_right ..))

lemma holWeights {g : ℂ→ℂ} (h : Differentiable ℂ g) {p : Price E} {U : Set E} {L : E→L[ℝ] ℂ} {b : ℂ}
    {R : ℝ} (hp : ∀ x∈U, ‖b+L x‖ ≤ R) : Packet U p 1 (fun x=>g (b+L x)) := by
  have hc : ContDiff ℝ ∞ g := by
    have hc : ContDiff ℂ ∞ g := h.contDiff
    exact hc.restrict_scalars ℝ
  have ht := compact_packet (q:=1) (isCompact_closedBall (0:ℂ) R) (fun _ _ => hc.contDiffAt)
  apply comp_affine_bill L b ht (fun x hx => ?_) (Bills.const _) (Bills.const _)
  exact Metric.mem_closedBall.mpr (by simpa using hp x hx)
end YM.MSbar.Pole
