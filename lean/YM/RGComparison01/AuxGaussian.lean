import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Lens
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.LogosG

/-!
# Outer-wall purchases for the *formal*, untruncated Gaussian integrals

Enough to control errors from replacing the D-ball coefficients. Only post-L,
at fixed finite demands, can pay with construction currencies. Period invoice
`Bolt` essential. No factor exponential-in-volume paid. Use actual inverse-M
bound (not assuming unit gap uniformly in the stage).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxGaussian
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure Push.AbsoluteSums PhysicalNext.Repeat Lantern
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Q : Matrix ι ι ℝ} {c P D : ℝ}

local notation "μ" => Poll.sweep Q
local notation "Y" => Poll.Body ι
local notation "U" => (closedBall (0:Y) D)ᶜ

def ticket (k : ℕ) (P c : ℝ) := (1+P)^k * (1+P*(2*Real.exp (c*k^2/2)))
lemma book (k : ℕ) (hh : (Fintype.card ι:ℝ) ≤ P) (hq : Q.PosDef)
    (h : ∀ z : ι → ℝ, dotProduct z (Q*ᵥ z) ≤ c*dotProduct z z) :
    let F (z:Y):=(1+‖z‖)^k
    Integrable F μ ∧ ∫ z,F z ∂μ ≤ ticket k P c := by
  intro F; have hQ:= hq.posSemidef
  have hz (i:ι) : |Q i i| ≤ c:= by
    let z : ι→ℝ:=Pi.single i (1:ℝ)
    have he₁ : dotProduct z (Q*ᵥ z) = Q i i:= by simp [z]
    rw [abs_of_nonneg (by rw [←he₁]; simpa only [star_trivial] using hQ.dotProduct_mulVec_nonneg z)]
    have hg:=h z; rw [he₁] at hg; simpa [z] using hg
  obtain ⟨hr,hZ⟩:= Flux.salience Finset.univ hQ hz k
  have hp : 0 ≤ P := (Nat.cast_nonneg _).trans hh; let p:=1+P
  have hv : 1 ≤ p := le_add_of_nonneg_right hp
  let f (z:Y):=1+∑ i:ι,(1+|z i|)^k
  have hB (z:Y) : F z ≤ p^k * f z := by
    cases isEmpty_or_nonempty ι with
    | inl h=>
      rw [Subsingleton.elim z 0]; simpa [F,f] using one_le_pow₀ (n:=k) hv
    | inr hi=>
      obtain ⟨i,hi,H⟩:= Finset.exists_max_image Finset.univ (fun i=> |z i|) Finset.univ_nonempty
      have he: ‖z‖ ≤ p*|z i|:= by
        apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (zero_le_one.trans hv) (abs_nonneg _))).mp
        rw [EuclideanSpace.real_norm_sq_eq, mul_pow]; refine (Finset.sum_le_sum (g:= fun _=> |z i|^2) (fun j h=>?_)).trans ?_
        · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (H j h) 2
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right ((hh.trans (le_add_of_nonneg_left zero_le_one)).trans (le_self_pow₀ hv (by decide))) (sq_nonneg _)
      refine (pow_le_pow_left₀ (by positivity) (b:=p*(1+|z i|)) ?_ k).trans ?_
      · rw [mul_add,mul_one]; exact add_le_add hv he
      rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (by positivity); exact (Finset.single_le_sum (f:=fun i=>(1+|z i|)^k) (fun _ _=> pow_nonneg (add_nonneg zero_le_one (abs_nonneg _)) k) hi).trans (le_add_of_nonneg_left zero_le_one)
  have hf : Integrable f μ := (integrable_const _).add hr
  have hF : Integrable F μ := (hf.const_mul (p^k)).mono' (by unfold F; fun_prop)
    (ae_of_all _ fun i=> by rw [Real.norm_of_nonneg (show 0 ≤ F i by unfold F; positivity)]; exact hB i)
  refine ⟨hF,(integral_mono hF (hf.const_mul _) hB).trans ?_⟩
  rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold f
  rw [integral_add (integrable_const _) hr,integral_const, probReal_univ,one_smul]; refine add_le_add_right (hZ.trans ?_) _
  rw [Finset.card_univ]; exact mul_le_mul_of_nonneg_right hh (by positivity)

lemma shields (k : ℕ) (hh : (Fintype.card ι:ℝ) ≤ P) (hq : Q.PosDef)
    (h : ∀ z : ι → ℝ, dotProduct z (Q*ᵥ z) ≤ c*dotProduct z z)
    {v w : ℝ} (hp : (sweep Q).real (closedBall (0:Y) D)ᶜ ≤ v) (he : 0 < w) :
    ∫ z in (closedBall (0:Y) D)ᶜ, (1+‖z‖)^k ∂μ ≤ v*w⁻¹+w*ticket (k+k) P c:= by
  let F k (z:Y):= (1+‖z‖)^k
  have h' k:= book k hh hq h
  have ht : ∀ z:Y, F k z ≤ w⁻¹+w*F (k+k) z:= by
    intro z; by_cases he': 1 ≤ w*F k z
    · apply le_trans (b:=w*F (k+k) z) _ (le_add_of_nonneg_left (by positivity))
      have hg : F k z ≤ w*F k z*(F k z):= le_mul_of_one_le_left (by unfold F; positivity) he'
      exact hg.trans_eq (by rw [mul_assoc,show F (k+k) z= _ from pow_add ..])
    apply le_trans (b:=w⁻¹) _ (le_add_of_nonneg_right (by unfold F; positivity)); exact le_of_mul_le_mul_left ((le_of_lt (lt_of_not_ge he')).trans_eq (mul_inv_cancel₀ he.ne').symm) he
  have hg : (∫ z in U, F k z ∂μ) ≤ ∫ z in U, w⁻¹+w*F (k+k) z ∂μ:= integral_mono (h' k).1.integrableOn ((integrable_const _).add (((h' (k+k)).1.const_mul w).integrableOn)) ht
  rw [integral_add (integrable_const _) (((h' (k+k)).1.const_mul w).integrableOn),setIntegral_const, integral_const_mul] at hg
  have hz : (∫ z in U, F (k+k) z ∂μ) ≤ ∫ z,F (k+k) z ∂μ := setIntegral_le_integral (h' (k+k)).1 (ae_of_all _ (fun _=> by unfold F; positivity))
  exact hg.trans (add_le_add (mul_le_mul_of_nonneg_right hp (by positivity)) (mul_le_mul_of_nonneg_left (hz.trans (h' _).2) he.le))

lemma walls (G : Gauge) (L : Side) {f : ℝ→ℝ} (hf : Bolt G L f) {c d : ℝ} (hc : 0<c) (h : 0<d) (φ : ℝ) (k : ℕ) :
    ∀ᶠ x in atTop, ∀ (ι:Type) [Fintype ι] [DecidableEq ι] (Q : Matrix ι ι ℝ),
    (Fintype.card ι:ℝ)≤ f x → Q.PosDef →
    (∀ z : ι→ℝ, dotProduct z (Q*ᵥ z)≤ c* dotProduct z z) →
       ∫ z in (closedBall (0:Poll.Body ι) (d * Delay.fineMonitor G L x))ᶜ,
         (1+‖z‖)^k ∂Poll.sweep Q ≤ betaF G x L ^φ := by
  let a:=φ-1; have hv:= Rate.power (G:=G) (L:=L) (a:=2*a) |>.mul (Rate.power (a:=-a)); rw [show 2*a+ -a=a by ring] at hv
  have he : Rate G L 0 (fun x => ticket (k+k) (f x) c) := by
    unfold ticket; exact Brim.bell (Brim.prep ((Rate.const 1).add hf.uses) _) ((Rate.const 1).add (hf.uses.mul_right _))
  have hQ:= (Rate.power (G:=G) (L:=L) (a:=a)).mul he; rw [add_zero] at hQ
  filter_upwards [Delay.shift_pos G L,Lantern.walls G L hf hc h (2*a), hv.add hQ φ (by unfold a; linarith)] with x hx ht he ι _ _ Q h₀ hy hL
  have hh := ht ι Q h₀ hy hL; let w:=betaF G x L; let W:=closedBall (0:Poll.Body ι) (d * Delay.fineMonitor G L x)
  rw [show 1 - (sweep Q).real W = (sweep Q).real Wᶜ by rw [measureReal_compl measurableSet_closedBall, probReal_univ] ] at hh
  have hV : 0 < w:=hx
  apply (shields k h₀ hy hL hh (show 0 < w^a by positivity)).trans
  rw [← Real.rpow_neg hV.le]; exact (le_abs_self _).trans he
end YM.RGComparison01.AuxGaussian
