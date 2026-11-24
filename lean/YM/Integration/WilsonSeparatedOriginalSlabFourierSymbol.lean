import YM.Integration.WilsonSeparatedOriginalSlabCompactFourier
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! Every spatial derivative of a true multitorus character has the original integer frequency price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabFourierSymbol
open Finset Function UnitAddTorus WilsonSeparatedOriginalSlabFourierOrbit WilsonSeparatedOriginalSlabFourierLattice
open scoped BigOperators Topology Classical ContDiff
variable {J:Type*}[Fintype J]

def seed (t:ℝ):ℂ:=Complex.exp ((t:ℂ)*Complex.I)

private theorem regular:ContDiff ℝ ∞ seed:=(Complex.ofRealCLM.contDiff.mul contDiff_const).cexp

private theorem initial (t:ℝ):HasDerivAt seed (Complex.I*seed t) t:=by
  have entered:=(((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp
  change HasDerivAt (fun x:ℝ=>Complex.exp ((x:ℂ)*Complex.I)) (Complex.I*Complex.exp ((t:ℂ)*Complex.I)) t
  simpa only [id_eq,Complex.ofReal_one,one_mul,mul_comm (Complex.exp _) Complex.I] using entered

private theorem budget (m:ℕ)(x:ℝ):‖iteratedFDeriv ℝ m seed x‖=1:=by
  have both (n:ℕ):iteratedDeriv n seed=fun t=>Complex.I^n*seed t:=by
    induction n with
    | zero=>simp
    | succ n ih=>rw [iteratedDeriv_succ,ih];funext t;rw [((initial t).const_mul (Complex.I^n)).deriv,pow_succ,mul_assoc]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,both,norm_mul,norm_pow,Complex.norm_I,one_pow,one_mul]
  simp [seed,Complex.norm_exp]

def arm (k:J→ℤ):(J→ℝ)→L[ℝ]ℝ:=(2*Real.pi:ℝ) • ∑j:J,(k j:ℝ) • ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:J=>ℝ) j

theorem source (k:J→ℤ)(x:J→ℝ):mFourier k (wrap x)=seed (arm k x):=by
  change (∏i:J, fourier (k i) ((x i:ℝ):UnitAddCircle))=_
  simp_rw [fourier_coe_apply,Complex.ofReal_one,div_one]
  rw [←Complex.exp_sum];unfold seed arm;simp only [smul_apply,_root_.sum_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_sum,Complex.ofReal_intCast,Complex.ofReal_ofNat]
  rw [Finset.mul_sum,Finset.sum_mul];congr 1;apply Finset.sum_congr rfl;intro i _;ring

theorem cost (k:J→ℤ):‖arm k‖≤2*Real.pi*height k:=by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) (zero_le_one.trans (active k)))
  intro x;unfold arm
  simp only [smul_apply,_root_.sum_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,Real.norm_eq_abs]
  rw [abs_mul,abs_of_pos (show 0<2*Real.pi by positivity)]
  rw [mul_assoc (2*Real.pi)];apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    |∑j:J,(k j:ℝ)*x j|≤∑j:J,|(k j:ℝ)*x j|:=Finset.abs_sum_le_sum_abs ..
    _≤∑j:J,|(k j:ℝ)| * ‖x‖:=Finset.sum_le_sum (fun j _=>by rw [abs_mul];exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg _))
    _≤height k*‖x‖:=by rw [←Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)

theorem original (k:J→ℤ)(m:ℕ)(x:J→ℝ):
    ‖iteratedFDeriv ℝ m (fun y:J→ℝ=>mFourier k (wrap y)) x‖≤(2*Real.pi)^m*height k^m:=by
  rw [show (fun y:J→ℝ=>mFourier k (wrap y))=seed ∘ arm k from funext (source k),
    (arm k).iteratedFDeriv_comp_right (contDiff_infty.mp regular m) x (i:=m) le_rfl,←mul_pow]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [budget,one_mul,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact pow_le_pow_left₀ (norm_nonneg _) (cost k) m

end YM.Integration.WilsonSeparatedOriginalSlabFourierSymbol
