import YM.MSbar.LocalSD.Target
/-! # conditional *actual* expectation -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bulk
open Lattice Wilson RG Function Filter MeasureTheory PhysicalNext.Repeat.Lotus
open scoped Topology Matrix.Norms.Frobenius Classical
variable {G:Gauge}{c f:Side} {S:StepData c f} {R:Rep G f} (V:Config G c)
variable {σ C δ Λ w v y : ℝ}
def expect (S:StepData c f)(R:Rep G f)(V:Config G c)(g:Config G f→ℝ):= S.push R.beta (g*R.eval) V/ S.push R.beta R.eval V
def chance (S:StepData c f)(R:Rep G f)(V:Config G c)(A:Set (Config G f)):= expect S R V (A.indicator (fun _=>1))
structure Admitted (V:Config G c) (R:Rep G f)(S:StepData c f)(σ C δ Λ w : ℝ) : Prop where
  lawful : R.Lawful σ C Λ δ w
  positive : 0 ≤ R.eval
  mass : 0 < S.push R.beta R.eval V
  kernel : S.IsKernel R.beta G
variable (h:Admitted V R S σ C δ Λ w)
local notation "X"=>expect S R V
include h
lemma nn {g g':Config G f→ℝ} (hf:Envelope g)(hh: Envelope g')(hc: g'≤g) : X g' ≤ X g:=by
   apply div_le_div_of_nonneg_right _ h.mass.le; apply integral_mono (StepData.push_slice h.kernel V _ ((hh.mul (R.envelope h.lawful)).integrable _)) (StepData.push_slice h.kernel V _ ((hf.mul (R.envelope h.lawful)).integrable _)); exact fun i=> smul_le_smul_of_nonneg_left (mul_le_mul_of_nonneg_right (hc i) (h.positive i)) (h.kernel.positive i V)
lemma e_const (i:ℝ): X (fun _=>i)=i :=by
    unfold expect StepData.push; simp only [Pi.mul_apply,smul_eq_mul, mul_left_comm (S.density _ _ _) i, integral_const_mul]; apply mul_div_cancel_right₀; exact h.mass.ne'
lemma e_sum {g g': Config G f→ℝ} (hf:Envelope g)(hh: Envelope g'): X (g+g')=X g+X g' :=by
    unfold expect; rw [add_mul,StepData.push_add h.kernel,Pi.add_apply,add_div]; exact (hf.mul (R.envelope h.lawful)).integrable (prior G _)
    exact (hh.mul (R.envelope h.lawful)).integrable (prior G _) -- goal order
omit h in
lemma e_mul {g: Config G f→ℝ} (i:ℝ): X (i • g)=i* X g:=by unfold expect StepData.push; simp only [Pi.mul_apply,Pi.smul_apply,smul_eq_mul,mul_assoc i,mul_left_comm _ i,integral_const_mul, mul_div_assoc]
lemma c_mono {P Q:Set (Config G f)} (hP:MeasurableSet P)(hQ:MeasurableSet Q)(hp:P⊆Q): chance S R V P ≤ chance S R V Q := by
    have hE (P:Set (Config G f))(hP:MeasurableSet P) : Envelope (P.indicator (fun _=> (1:ℝ))):=Envelope.piece hP (Envelope.const _) (Envelope.const _)
    exact nn V h (hE Q hQ) (hE _ hP) (fun i=> by by_cases h:i∈P; simp [Set.indicator_of_mem,h,hp h]; simp only [Set.indicator_of_notMem h]; exact Set.indicator_nonneg (fun _ _=>zero_le_one) _)
variable {D0: Support f}{κ:Config G f → Config G f}{g:Config G f→ℝ}{a:ℝ}
lemma receipt (hT:Tracks R D0 κ g S a)(K:MergeProof.Menu.Arsenal R) (H: Psalm S R v y)(ht:0≤ y)(hv:flags v V=∅)(hz:∀ U: Config G f,0< R.eval U) : |X (fun U=>g U*(R.eval (κ U)/R.eval U*Real.exp (R.exponent U-R.exponent (κ U))-1))| ≤ y*(R.p.mass D0 (a*2)*Real.exp (D0.card*w)) := by
    unfold expect; rw [abs_div,abs_of_pos h.mass]; apply (div_le_iff₀ h.mass).2
    rw [mul_comm _ (S.push ..)] -- normalized payment
    have hW: (fun U: Config G f=> g U * (R.eval (κ U)/ R.eval U*Real.exp (R.exponent U-R.exponent (κ U))-1))*R.eval=(fun U=>g U * (R.eval (κ U)*Real.exp (R.exponent U-R.exponent (κ U))- R.eval U)):=by funext U; simp only [Pi.mul_apply]; field_simp [(hz U).ne']
    rw [hW]; exact Recenter.accurate hT h.lawful K H h.kernel V hv h.mass.le ht
end YM.MSbar.Bulk
