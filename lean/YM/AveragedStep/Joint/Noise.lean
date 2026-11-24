import YM.AveragedStep.Joint.Read
import YM.UVExt.LinkDisk
import YM.PertExtension.Tails
/-! One-link normalized noise controls can also consume *all* fixed powers
(even with nontrivial tag law outside). The narrow integral supply here is
only used for its scalar ratio bound, no premise about field comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function MeasureTheory Lattice Wilson RG SectorNext.Vacuum
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable (G : Gauge) (K : KernelChoices)
local notation "κ" => K.penalty
-- always use real multiplications; τ=√β and chord*τ
lemma link_power (m : ℕ) : ∃ C:ℝ,0≤C ∧ ∀ᶠ τ:ℝ in atTop,
    (∫ u:G.El,mouth G (κ*τ^2) u * (τ*G.chord u)^m ∂G.probHaar) ≤
      C * linkZ G (κ*τ^2) := by
  obtain ⟨C,hC,H⟩:= PertExtension.Series.Radial.bounded_exp
    (c:=3*κ/8) (by have := K.penalty_pos; positivity) m
  obtain ⟨D,hD,T⟩:= UVExt.link_ratio_bound κ (Next.Foundations.chart G) (Next.Foundations.chart_ok G)
    K.penalty_pos
  refine ⟨C*D,by positivity,?_⟩
  filter_upwards [T,eventually_ge_atTop (0:ℝ)] with τ hτ ht
  have hh(u:G.El): mouth G (κ*τ^2) u*(τ*G.chord u)^m ≤
      C*mouth G (κ*τ^2/4) u := by
    let x:=τ*G.chord u
    have hx:0≤x:=mul_nonneg ht (G.chord_nonneg _)
    calc
      _ = (x^m * Real.exp (-(3*κ/8)*x^2)) * mouth G (κ*τ^2/4) u := by
        unfold mouth; rw [mul_comm (Real.exp ..),mul_assoc,← Real.exp_add]
        have hr:= G.chord_price u
        have hp : G.price u=(G.chord u)^2/2 := by linarith
        congr 2; unfold x; rw [hp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hx (by linarith : x≤1+x) m) (Real.exp_pos _).le).trans (H _ hx)) (Real.exp_pos _).le
  have hi (b:ℝ) : Continuous (mouth G b) := by unfold mouth; fun_prop
  have hM : Integrable (fun u:G.El=>mouth G (κ*τ^2) u*(τ*G.chord u)^m) G.probHaar :=
    (env_continuous ((hi _).mul ((continuous_const.mul G.continuous_chord).pow m))).integrable _
  calc
    _ ≤ ∫ u, C*mouth G (κ*τ^2/4) u ∂G.probHaar := integral_mono hM ((env_continuous (continuous_const.mul (hi _))).integrable _) hh
    _ ≤ _ := by rw [integral_const_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left hτ hC

variable {G} {c f : Side} (S : StepData c f) (β : ℝ)

def linkLaw (u v : G.El) := (S.penaltyZ β G)⁻¹ * S.penaltyWeight β (u*v⁻¹)
lemma penalty_identity (hS:S.kernel=K) : S.penaltyZ β G=linkZ G (κ*β) := by
  unfold StepData.penaltyZ StepData.penaltyWeight linkZ mouth
  simp_rw [hS]; congr 1; funext; congr 1; ring

lemma link_read (Q:G.El) (H:G.El→ℝ) :
    (∫ u:G.El, linkLaw S β u Q * H (u*Q⁻¹) ∂G.probHaar)=
      (S.penaltyZ β G)⁻¹ * ∫ u:G.El,S.penaltyWeight β u*H u ∂G.probHaar := by
  unfold linkLaw; simp_rw [mul_assoc,integral_const_mul]
  exact congr_arg (_ * ·) ((measurePreserving_mul_right G.probHaar Q⁻¹).integral_comp
      ((Homeomorph.mulRight Q⁻¹).measurableEmbedding) (fun u:G.El=>S.penaltyWeight β u*H u))
lemma link_one (Q:G.El) : (∫ v,linkLaw S β v Q ∂G.probHaar)=1 := by
  have h := link_read S β Q (fun _=>1)
  simp only [mul_one] at h
  rw [h,← StepData.penaltyZ,inv_mul_cancel₀ (S.penaltyZ_pos _).ne']

lemma noise_single (Q:Config G c) (e : Edge (Site c)) (H:G.El→ℝ) :
    (∫ V:Config G c,S.noise β Q V*H (V e*(Q e)⁻¹) ∂prior G c)=
     (S.penaltyZ β G)⁻¹ * ∫ u:G.El,S.penaltyWeight β u*H u ∂G.probHaar := by
  let b (i : Edge (Site c)) (u:G.El) := linkLaw S β u (Q i) * if i=e then H (u*(Q i)⁻¹) else 1
  have hb(V:Config G c) : S.noise β Q V*H (V e*(Q e)⁻¹)=∏ i,b i (V i):= by
    simp only [b,Finset.prod_mul_distrib,linkLaw,StepData.noise]
    rw [Finset.prod_ite_eq' Finset.univ _]
    simp
  simp_rw [hb]; rw [prior, integral_fintype_prod_eq_prod b,
    Finset.prod_eq_single_of_mem e (Finset.mem_univ e) (f:=fun i=>∫ u,b i u ∂G.probHaar)]
  · simpa only [b,if_true] using link_read S β (Q e) H
  intro i _ hi
  simpa only [b,if_neg hi,mul_one] using link_one S β (Q i)

/-- Retain the latent prediction on each tag. -/
def scaledNoise (τ : ℝ) (e : Edge (Site c)) : Query S G := fun i x=>
  τ*G.chord (x.2 e*(S.prediction x.1 i e)⁻¹)
lemma noise_admits (τ : ℝ) (e : Edge (Site c)) (h:S.patch.Branches S.kernel G) :
    Admits (scaledNoise (G:=G) S τ e):=by
  intro i
  apply env_comp (g:=fun (x:Board G c f)=> x.2 e*(S.prediction x.1 i e)⁻¹)
    (env_continuous (continuous_const.mul G.continuous_chord))
  exact ((measurable_pi_apply e).comp measurable_snd).mul (((measurable_pi_apply e).comp
    ((S.prediction_meas h i).comp measurable_fst)).inv)
lemma scaledNoise_pos {τ : ℝ} (ht : 0 ≤ τ) (e : Edge (Site c)) (i : S.Choices)
    (x : Board G c f) : 0 ≤ scaledNoise S τ e i x := mul_nonneg ht (G.chord_nonneg _)

-- exact with all size dependence only on the stated single group/kernel,
-- no per-tag probability losses
lemma noise_transfer (τ:ℝ) (e:Edge (Site c)) (h:S.patch.Branches S.kernel G) (m:ℕ) :
    readQ S β (fun i (x:Board G c f)=> scaledNoise S τ e i x ^ m)=
      (S.penaltyZ β G)⁻¹ * ∫ u:G.El,S.penaltyWeight β u*(τ*G.chord u)^m ∂G.probHaar := by
  rw [read_order S β h ((noise_admits S τ e h).npow m)]
  unfold scaledNoise
  let H (u:G.El):=(τ*G.chord u)^m
  let M:ℝ :=(S.penaltyZ β G)⁻¹ * ∫ u:G.El,S.penaltyWeight β u*H u ∂G.probHaar
  change (∑ i,∫ U,S.likelihood U i*(∫ V,S.noise β (S.prediction U i) V*H (V e*(S.prediction U i e)⁻¹) ∂prior G c)∂law G f β) = M
  simp_rw [noise_single S β _ e H,integral_mul_const,← Finset.sum_mul,show (S.penaltyZ β G)⁻¹ * (∫ u:G.El,S.penaltyWeight β u*H u ∂G.probHaar)= M from rfl]
  have ho:= read_one (G:=G) S β h
  rw [read_order S β h Admits.one] at ho
  simp only [Pi.one_apply,mul_one,S.noise_mass] at ho
  rw [ho,one_mul]
end YM.AveragedStep

namespace YM.AveragedStep
open Filter Function MeasureTheory Lattice Wilson RG SectorNext.Vacuum
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable (G : Gauge) (K : KernelChoices)
lemma noise_paid (m:ℕ) : ∃ C:ℝ, 0≤C ∧ ∀ᶠ τ:ℝ in atTop, ∀ {c f:Side} (S:StepData c f),
    S.kernel=K → S.patch.Branches S.kernel G→ ∀ e:Edge (Site c),
    readQ S (τ^2) (fun i (x:Board G c f)=> scaledNoise S τ e i x ^ m) ≤ C := by
  obtain ⟨C,hC,H⟩:=link_power G K m
  refine ⟨C,hC,H.mono ?_⟩
  intro τ he c f S hk hb e
  rw [noise_transfer S _ _ e hb m,← div_eq_inv_mul,div_le_iff₀ (S.penaltyZ_pos (G:=G) _),penalty_identity K S (τ^2) hk]
  unfold mouth at he
  unfold StepData.penaltyWeight; simp_rw [hk,neg_mul,mul_comm (τ^2) K.penalty]
  -- normalized exponent parser -β*κ*t ; - (κ* τ^2)*price
  simpa only [neg_mul] using he
end YM.AveragedStep
