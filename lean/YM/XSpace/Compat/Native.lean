import YM.XSpace.Compat.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Mesh-integration helpers recovered from the hash-pinned Oct15 source.
The original covariance/symbol/Weight definitions retain their baseline identity.
New helper declarations live only in this compatibility namespace. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Compat.KP
open YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex MeasureTheory Lattice Bloch Laurent Exterior Matrix Precision
open scoped Topology ContDiff BigOperators InnerProductSpace Real ComplexConjugate
variable {ι : Type*} {n : Side} {α Ω η : ℝ}
private lemma pole_ae : ∀ᵐ x : E4, x ∈ whole :=
  mem_ae_iff.mpr (by change volume (({0}ᶜ : Set E4)ᶜ) = 0; rw [compl_compl]; simp)

lemma pore_meas {f : E4 → ℂ} (h : ContinuousOn f whole.look) :
    AEStronglyMeasurable f := by
  rw [← Measure.restrict_eq_self_of_ae_mem (s := whole.look) pole_ae]
  exact h.aestronglyMeasurable whole.ok.measurableSet

lemma compact_house_integrable (f g : ι → E4 → ℂ)
    (hh : ∀ i p, g i p = house p * f i p)
    (h : Weight whole 0 g) (hz : ∀ i, g i 0 = 0) (i : ι) :
    Integrable (g i) := by
  obtain ⟨C,hC,H⟩ := h.quotes 0
  have bound (p : E4) : ‖g i p‖ ≤ C := by
    by_cases hp : p = 0
    · rw [hp,hz,norm_zero]
      exact hC
    simpa using H i p hp
  let R : ℝ := 2*earth+1
  have hi : Integrable ((ball (0:E4) R).indicator (fun _ : E4 => C)) :=
    (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball
  apply hi.mono' (pore_meas (h.smooth i).continuousOn)
  apply Eventually.of_forall
  intro p
  by_cases hp : p ∈ ball (0:E4) R
  · simpa only [indicator_of_mem hp] using bound p
  have hl : R ≤ ‖p‖ := le_of_not_gt (mt mem_ball_zero_iff.mpr hp)
  have hf : house p = 0 := door_shut (by dsimp [R] at hl; linarith)
  simp only [hh i p, hf, zero_mul, norm_zero, indicator_of_notMem hp, le_refl]

variable (A B : List Axis)
def heft := A.length+B.length
lemma pay_all {f : ι→ E4 → ℂ} {i j : ℤ} (h : Weight whole i f) (hg : Weight veranda j f) (hi : j ≤ i) : Weight whole j f :=
  blend ((h.use rake_subset).soften (2*earth) (by positivity [earth_pos]) search_short hi) hg stroll
lemma rebus_paid (a b : X2) (ha : 0<α) (he : 0<η) {k : ℤ} (h : k≤heft A B) : Weight whole k (fun (f : Firm α Ω η) p=>rebus A B f p a b) :=
  pay_all (house_pay A B ha he a b) (veranda_free A B a b) (by unfold sizeL; exact (h.trans_eq (by unfold heft; omega)))
lemma lift_mesh (ha : 0<α) (he : 0<η) (a b : X2) : ∃ C:ℝ,0≤C ∧ ∀ f:Firm α Ω η,∀ n,∀ x:Cover,
    ‖transmits A B n f a b x-retract (fun p=>rebus A B f p a b) (rcast x)‖ ≤ C*(1+‖rcast x‖)/(n.val:ℝ) := by
  let I:=Firm α Ω η; let g (i:I) (p:E4) := rebus A B i p a b
  have hu (k:ℤ) (hk:k≤heft A B) : Weight whole k g:= rebus_paid A B a b ha he hk
  have hh : Weight whole ((0:ℕ):ℤ) g:=hu 0 (by omega); let r (i:I) (p:E4) := record A B i p a b
  obtain ⟨C,hC,H⟩:=mesh_quote r g (fun _ _=>rfl) hh (fun i=> room_none A B i a b) (compact_house_integrable r g (fun _ _ => rfl) hh (fun i => room_none A B i a b))
  refine ⟨‖(↑tally:ℂ)‖*C*(2*Real.pi),by positivity,fun f n x=>?_⟩
  rw [covering]
  unfold retract
  rw [← mul_sub,norm_mul]
  apply (mul_le_mul_of_nonneg_left (H f n (rcast x)) (norm_nonneg _)).trans_eq
  unfold leap
  ring

end YM.XSpace.Compat.KP
end
