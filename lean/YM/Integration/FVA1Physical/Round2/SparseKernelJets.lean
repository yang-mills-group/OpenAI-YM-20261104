import YM.Push.LOCAL_SPLITTING.NoiseJet

/-! Relative ordered derivatives of the full shared-tag noise with all
coarse edges conditioned. The price counts only edges on which the
directions move. The background can be any configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Kernel
open Lattice Wilson RG Source MeasureTheory
open scoped Classical BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

private theorem noisy_partition (β : ℝ) (A : Edges c) (Q V : Config G c) :
    noisy S β Finset.univ Q V = noisy S β (Finset.univ \ A) Q V * noisy S β A Q V := by
  unfold noisy
  exact (Finset.prod_sdiff (Finset.subset_univ A)).symm

private theorem inactive_noise (β : ℝ) (A : Edges c) (Q V : Config G c)
    (v : Directions G c) (t : ℝ) (hv : ∀ e∉A, v e=0) :
    noisy S β (Finset.univ \ A) Q (increment V (t • v)) =
      noisy S β (Finset.univ \ A) Q V := by
  unfold noisy
  apply Finset.prod_congr rfl
  intro e he
  simp [increment, hv e (Finset.mem_sdiff.mp he).2]

theorem full_noise_jet (β : ℝ) (A : Edges c) (Q V : Config G c)
    (l : List (Directions G c)) (hl : ∀ v∈l, ∀ e∉A, v e=0) :
    leftDerivs (noisy S β Finset.univ Q) l V =
      noisy S β (Finset.univ \ A) Q V * leftDerivs (noisy S β A Q) l V := by
  induction l generalizing V with
  | nil => exact noisy_partition S β A Q V
  | cons v l ih =>
    simp only [leftDerivs]
    have hv := hl v (by simp)
    have ht := fun w (hw : w∈l) => hl w (List.mem_cons_of_mem _ hw)
    simp_rw [ih _ ht, inactive_noise S β A Q V v _ hv, deriv_const_mul_field]

theorem sparse_noise_bound (β : ℝ) (A : Edges c) (Q V : Config G c) {k : ℕ} {r : ℝ}
    (hr : 0≤r) (l : List (Directions G c)) (hk : l.length≤k)
    (hs : ∀ v∈l, ∀ e∉A, v e=0) (hb : ∀ v∈l, ∀ e∈A, ‖v e‖≤r) :
    ‖leftDerivs (noisy S β Finset.univ Q) l V‖ ≤
      noiseFactor G (β*S.kernel.penalty) k A.card r ^ l.length * noisy S β Finset.univ Q V := by
  rw [full_noise_jet S β A Q V l hs, norm_mul,Real.norm_of_nonneg (noisy_pos ..).le,
    noisy_partition S β A Q V, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (noisy_bound S β A Q V hr l hk hb) (noisy_pos ..).le

theorem sparse_push_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β : ℝ) (A : Edges c) (h : S.patch.Branches S.kernel G) (V : Config G c)
    {k : ℕ} {r a : ℝ} {D : Config G f → ℝ} {F : Config G f → E}
    (hr : 0≤r) (hf : Integrable F (prior G f)) (hd : Integrable D (prior G f))
    (hF : ∀ U, ‖F U‖≤a*D U) (l : List (Directions G c)) (hk : l.length≤k)
    (hs : ∀ v∈l, ∀ e∉A, v e=0) (hb : ∀ v∈l, ∀ e∈A, ‖v e‖≤r) :
    ‖leftDerivs (S.push β F) l V‖ ≤
      (noiseFactor G (β*S.kernel.penalty) k A.card r ^ l.length * a) * S.push β D V := by
  let C := noiseFactor G (β*S.kernel.penalty) k A.card r ^ l.length
  have he U : ‖weights S U (fun Q => leftDerivs (noisy S β Finset.univ Q) l V)‖ ≤
      C*pdf S β Finset.univ U V := by
    unfold pdf weights
    rw [Finset.mul_sum]
    apply (norm_sum_le ..).trans
    apply Finset.sum_le_sum
    intro t _
    rw [norm_mul, Real.norm_of_nonneg (S.likelihood_pos ..), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (sparse_noise_bound S β A _ V hr l hk hs hb) (S.likelihood_pos ..)
  rw [←pass_full, left_pass S β Finset.univ h hf V l, ←pass_full, pass, ← integral_const_mul]
  apply norm_integral_le_of_norm_le ((pdf_integrable S β Finset.univ h V hd).const_mul _)
  exact .of_forall fun U => (norm_smul ..).trans_le ((mul_le_mul (he U) (hF U)
    (norm_nonneg _) ((norm_nonneg _).trans (he _))).trans_eq (by unfold C; ring))
end YM.Push.Local.Kernel
