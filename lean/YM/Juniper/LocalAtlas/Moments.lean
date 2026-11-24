import YM.Juniper.LocalAtlas.Taylor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Purple
/-!
 # Uniform moments for auxiliary Poll of arbitrary prescribed order

 Ambient variable *finite Euclidean* dimension ≤ f(t) here. Keep the same
 dependency structure. No determinant or norm-equivalence constants lost.
 Walls consumes `b≈ g_i monitor` equivalent comparing `D≈FiMon`.
 Therefore costs survive the step at all orders. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open MeasureTheory Set Function Filter Matrix Metric ENNReal ProbabilityTheory
open RG Wilson Pressure Lattice Precision Push Push.AbsoluteSums
open PhysicalNext.Repeat Lantern Sienna ConnectedActivityE6 Blaze Brush Poll
open scoped Topology MatrixOrder ContDiff Classical BigOperators ENNReal
variable {ι:Type} [Fintype ι] [DecidableEq ι]
-- `Y` matrix is covariance, not precision.
variable {Y: Matrix ι ι ℝ}{c A : ℝ}(h : Y.PosDef) (hp :∀ z:ι→ℝ, dotProduct z (Y *ᵥ z) ≤ c * dotProduct z z)
local notation "μ" => sweep Y
local notation "X" => Poll.Body ι

def gamut (A c : ℝ)(n : ℕ) := (1+A)^n * (1+A*(2*Real.exp (c*(n:ℝ)^2/2)))

def bill (n : ℕ) (z : Poll.Body ι) := (1+‖z‖)^n
include hp h
private lemma ears (i:ι): |Y i i| ≤ c := by
    let z:ι→ℝ:= Pi.single i (1:ℝ) -- annotate
    have hy : dotProduct z z=1:=by simp [z]
    have hx : dotProduct z (Y *ᵥ z)=Y i i:=by simp [z]
    have hP:= h.posSemidef.dotProduct_mulVec_nonneg z
    rw [abs_of_nonneg ?_]; simpa only [hy,hx,mul_one] using hp z
    simpa [z] using hP
lemma moment (hA : (Fintype.card ι:ℝ) ≤ A) (n : ℕ) :
    Integrable (bill n) μ ∧ ∫ z,bill n z ∂μ ≤ gamut A c n := by
  have hx : 0 ≤ A:= (Nat.cast_nonneg _).trans hA
  let B : X→ℝ:= fun z=> 1+∑ i:ι,(1+|z i|)^n
  obtain ⟨he,hB⟩:= Flux.salience (A:=Y) Finset.univ h.posSemidef (ears h hp) n
  have hG : Integrable B μ:= (integrable_const _).add he
  let U := fun (z:X)=> ((1+A)^n)*B z; have hu : Integrable U μ:= hG.const_mul _
  have hU (z:X): bill n z ≤ U z := by
    cases isEmpty_or_nonempty ι with
    | inl hv =>
      rw [Subsingleton.elim z 0]; simp only [bill,U,B,norm_zero,add_zero,one_pow,Finset.univ_eq_empty,Finset.sum_empty,mul_one]
      exact one_le_pow₀ (by linarith only [hx])
    | inr hv=>
      obtain ⟨i,-,hk⟩:=Finset.exists_max_image Finset.univ (fun i=> |z i|) Finset.univ_nonempty
      let Z:= |z i|
      have ha : 1 ≤ A:= by have h : 1 ≤ Fintype.card ι:= Fintype.card_pos; exact le_trans (by exact_mod_cast h) hA
      have hp : 0 ≤ Z := abs_nonneg _
      have hy : ‖z‖ ≤ A* Z := by
         have hS: ‖z‖^2 ≤ A* Z^2:= by
           rw [EuclideanSpace.real_norm_sq_eq]; unfold Z; refine le_trans ?_ (mul_le_mul_of_nonneg_right hA (sq_nonneg _))
           apply le_trans (b:=∑ _ : ι, |z i|^2); apply Finset.sum_le_sum; intro j _; rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hk _ (Finset.mem_univ j)) _
           simp
         nlinarith only [ha,hS, mul_nonneg hx hp,norm_nonneg z, sq_nonneg (Z),mul_le_mul_of_nonneg_right (le_self_pow₀ (n:=2) ha (by decide)) (sq_nonneg Z)]
      have hh : (1:ℝ)+‖z‖≤(1+A)*(1+Z):=by linarith only [hy,hp,ha]
      unfold bill; refine (pow_le_pow_left₀ (show 0 ≤ 1+‖z‖ by positivity) hh n).trans ?_
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left ((Finset.single_le_sum (f:=fun j:ι=>(1+|z j|)^n) (fun i _=>by positivity) (Finset.mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)
  have hd := hu.mono' (f:=bill n) (by unfold bill;fun_prop) (Eventually.of_forall fun z => (Real.norm_of_nonneg (show 0 ≤ bill n z by unfold bill;positivity)).trans_le (hU z))
  refine ⟨hd,(integral_mono hd hu hU).trans ?_⟩
  unfold U B gamut; rw [integral_const_mul, integral_add (integrable_const _) he,integral_const, probReal_univ,one_smul]; rw [Finset.card_univ] at hB
  exact mul_le_mul_of_nonneg_left (add_le_add_right (hB.trans (mul_le_mul_of_nonneg_right hA (by positivity))) _) (by positivity)

lemma outside (hA : (Fintype.card ι:ℝ) ≤ A) (n : ℕ) (S : Set X) (hS:MeasurableSet S){m ε:ℝ} (hm:(μ).real S ≤ m) (he:0 < ε):
     ∫ z in S,bill n z ∂μ ≤ ε*gamut A c (2*n)+m*ε⁻¹ := by
  let u:=bill (ι:=ι) n; let p:=gamut A c (2*n); let K:=bill (ι:=ι) (2*n); have hyx (x:X):0≤K x:= by unfold K bill; positivity
  have hz:= moment h hp hA (2*n)
  have hv : IntegrableOn K S μ:= hz.1.integrableOn
  calc
   _ ≤ ∫ z in S,ε*K z + ε⁻¹ ∂μ:= setIntegral_mono_on (moment h hp hA n|>.1.integrableOn) ((hv.const_mul _).add (integrable_const _)) hS fun z _=> by
     have hg : bill n z ^ 2= K z:= by dsimp only [bill,K]; rw [←pow_mul, Nat.mul_comm]
     have hx: 0 ≤ bill n z:= by unfold bill; positivity
     have ht: ε* ε⁻¹=1:=mul_inv_cancel₀ he.ne'
     rw [← hg]; nlinarith only [ht,hx,mul_nonneg he.le hx, sq_nonneg (ε*bill n z-1),he]
   _ ≤ _:= by rw [integral_add (hv.const_mul _) (integrable_const _),integral_const_mul,setIntegral_const,smul_eq_mul]; exact add_le_add (mul_le_mul_of_nonneg_left ((setIntegral_le_integral hz.1 (ae_of_all _ hyx)).trans hz.2) he.le) (mul_le_mul_of_nonneg_right hm (by positivity))
end YM.Juniper.LocalAtlas
