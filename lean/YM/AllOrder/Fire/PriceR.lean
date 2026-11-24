import YM.AllOrder.Fire.Dir
import Mathlib.LinearAlgebra.Vandermonde
/-!
# Degree-limited polynomial calculus and purchase of errors post-Π.

Keep growth at ANY center x. No derivatives of sharp projection; only book
polynomials. Inverse Vandermonde controls arbitrary directions; constants needn't
know E or its frame. Helpful in preserving true norm while comparing cropped or
uncropped tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Fire
open Function Finset Laplace.SigmaP PositionX.Jet PertExtension PertExtension.Series PositionX.Gauss Radial MeasureTheory Response Module
open scoped Topology ContDiff BigOperators Classical
variable {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X] {n:ℕ} {f:X→ℝ}
section interpolation
open Matrix
lemma analytic_cost (n:ℕ) : ∃ M: ℝ, 0<M ∧ ∀ (f:ℝ→ℝ), Rank ℝ n f → ∀ (C:ℝ),(∀ i:Fin (n+1), |f i.val|≤C) → ∀ k:Fin (n+1), ‖someJ f k.val‖ ≤ M*C := by
   let F (i:Fin (n+1)):ℝ:=i.val; have hF : Injective F:=fun i j h=>Fin.ext (by unfold F at h; exact_mod_cast h)
   let M:= (vandermonde F)⁻¹; let R: ℝ:=∑ i:Fin (n+1),∑ j: Fin (n+1), |M i j|
   refine ⟨1+R,add_pos_of_pos_of_nonneg one_pos (by unfold R; positivity),fun f h C H k=>?_⟩; let a(i:Fin (n+1)):=someJ f i.val; let b:= f∘ F; have hp: (vandermonde F)*ᵥ a=b:= by
      ext1 i; unfold b; rw [Function.comp_apply, congr_fun (rank_taylor h).2, delay, ← Fin.sum_univ_eq_sum_range]; rfl -- rewrite b
   have hh : a=M*ᵥ b:= by rw [←hp,Matrix.mulVec_mulVec,show M=(vandermonde F)⁻¹ from rfl, Matrix.nonsing_inv_mul (vandermonde F) (isUnit_iff_ne_zero.mpr (det_vandermonde_ne_zero_iff.mpr hF)), Matrix.one_mulVec]
   have hC:= (abs_nonneg _).trans (H k)
   rw [Real.norm_eq_abs]; change |a k|≤ _; rw [hh,Matrix.mulVec, dotProduct]; refine (Finset.abs_sum_le_sum_abs _ _).trans ?_; simp_rw [abs_mul]
   calc _ ≤ ∑ i:Fin (n+1), |M k i| * C:=by gcongr with i; exact H _
        _ ≤ _ := by rw [← Finset.sum_mul]; refine mul_le_mul_of_nonneg_right ?_ hC; exact (Finset.single_le_sum (f:=fun k:Fin (n+1)=>∑ i:Fin (n+1),|M k i|) (fun i _=> by positivity) (mem_univ k)).trans (le_add_of_nonneg_left zero_le_one)
end interpolation
abbrev roi (x:X):=1+‖x‖
def Prices (n:ℕ) (C:ℝ)(f:X→ℝ):Prop:= 0≤C ∧ Rank X n f ∧ ∀ x, |f x|≤C*(1+‖x‖)^n
variable {C : ℝ} (h:Prices n C f)
lemma boost (x:X) (n:ℕ)(z:ℕ)(hz:z ≤ n)(v:X)(h:‖v‖≤1) : roi (x+(z*roi x:ℝ)•v) ≤ (n+1:ℕ) * roi x := by
   dsimp [roi]; have hm := norm_add_le x ((z*roi x:ℝ) • v); rw [norm_smul,Real.norm_of_nonneg (by dsimp [roi]; positivity)] at hm
   calc 1+_ ≤ 1+(‖x‖+(z*roi x:ℝ)*‖v‖):= by gcongr
        _ ≤ 1+(‖x‖+(n*roi x:ℝ)*1):= by gcongr
        _ ≤ _:= by push_cast; dsimp [roi]; ring_nf; exact le_rfl
noncomputable def honor (n:ℕ) := ((analytic_cost n).choose)* (n+1:ℕ)^n -- cast???
lemma honor_pos (n:ℕ): 0<honor n := mul_pos (analytic_cost n).choose_spec.1 (by positivity)
lemma Prices.taper (h:Prices n C f)(x:X)(hx:‖x‖≤1):Prices (n-1) (C*honor n) (diff' x f):=by
 refine ⟨mul_nonneg h.1 (honor_pos _).le,h.2.1.der _,fun z=>?_⟩
 rcases n with _|n; · have he:f=(fun _=>f z):=funext fun i=>h.2.1.asZero rfl i z; unfold diff'; nth_rw 1 [he]; simp only [fderiv_fun_const,Pi.zero_apply,_root_.zero_apply,abs_zero,Nat.zero_sub,pow_zero,mul_one]; exact mul_nonneg h.1 (honor_pos _).le
 let R:=roi z; let M:=n+1; let Q:= (↑(M+1):ℝ); have hh:0<R:=by unfold R roi; positivity
 let w:ℝ→L[ℝ] X:= ContinuousLinearMap.toSpanSingleton ℝ (R • x); let g (t:ℝ):=f (z+w t)
 have he:someJ g 1=R* diff' x f z:= by change someJ (fun t:ℝ=> f (z+t • R • x)) 1=_; rw [← licensed h.2.1.read.smooth.contDiffAt]; simp only [diff',map_smul,smul_eq_mul]
 have hw(i:Fin (M+1)): |g i.val| ≤ C*(Q*R)^M:= calc
   _ ≤ _:= h.2.2 _
   _ ≤ _:= by
      apply mul_le_mul_of_nonneg_left _ h.1; apply pow_le_pow_left₀ (by positivity); unfold Q; rw [show w (i.val:ℝ)= (i.val*R:ℝ) • x from smul_smul ..]; exact boost _ _ _ (Nat.le_of_lt_succ i.isLt) x hx
 let k:= (⟨1,by unfold M; omega⟩ : Fin (M+1)); have hg:= (analytic_cost _).choose_spec.2 g (h.2.1.app w z) _ hw k; change ‖someJ g 1‖ ≤ _ at hg; rw [he,norm_mul,Real.norm_of_nonneg hh.le] at hg; apply le_of_mul_le_mul_left _ hh; refine hg.trans_eq ?_ -- edit
 unfold honor; rw [Nat.add_sub_cancel,mul_pow, show R^M= R^n * R from pow_succ ..]; unfold R Q M; push_cast; dsimp [roi]; ring
end YM.AllOrder.Fire
