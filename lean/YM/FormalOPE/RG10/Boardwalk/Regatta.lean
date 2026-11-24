import YM.FormalOPE.RG10.Boardwalk.Gliss
/-! # Read in $g_X$ power coupling near its nonzero reset slope
 Preserve budget precision $\nu$ step and a polynomial in Z. Uses all orders simultaneously
 only at finite demands through r. If r=0 no slope hypothesis on Cost use (one on comparison
 before invoking refund for r≥1). No claim order convergence. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Boardwalk.Regatta
open Filter Function Finset PowerSeries Clearing Ledger Rates InversionTop
open Carryon PertExtension Position Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric PertExtension.Position Triangle
open scoped Topology BigOperators Classical ContDiff
variable {I : Type*}{l:Filter I}{r n :ℕ}
variable {P:Path l}
-- only real expansions; can convert to complex entry.
variable {p q:I→ Warp}{a: ℝ}
local notation "σ" => Carryon.Warp.Hot
private lemma low (x:Warp)(n k:ℕ)(hk:k<n): coeff k (x.x^n)=0:= by
 have hd : PowerSeries.X^n ∣ x.x^n:= pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr x.atOrigin) _ -- inspect
 exact X_pow_dvd_iff.mp hd k hk
private lemma high (x:Warp)(n:ℕ) : coeff n (x.x^n)=(coeff 1 x.x)^n:= by
 induction n with
 | zero=>simp
 | succ n ih=>
   rw [pow_succ,pow_succ,coeff_mul,Finset.sum_eq_single_of_mem (n,1) (by simp),ih]
   rintro ⟨a,b⟩ h hk; have h' := Finset.HasAntidiagonal.mem_antidiagonal.mp h
   dsimp only at h' ⊢
   rcases lt_trichotomy a n with h|h|h
   · rw [low x n a h, zero_mul]
   · exact False.elim (hk (by simp [h,show b=1 by omega]))
   rw [show b=0 by omega, coeff_zero_eq_constantCoeff_apply, x.atOrigin,mul_zero]
private def early (p:Warp)(n:ℕ):ℝ := ∑ k∈range n, coeff k p.refund.x * coeff n (p.x^k)
private lemma recur (p:Warp)(h:p.Hot)(n:ℕ) : coeff n p.refund.x=(coeff n (PowerSeries.X:fps) - early p n)*((coeff 1 p.x)^n)⁻¹:= by
 let x:= coeff n p.refund.x; let A:= coeff n (PowerSeries.X:fps); let B:= early p n; let C:=(coeff 1 p.x)^n
 have he : coeff n (p.charge p.refund.x)= A:= congr_arg (fun p:Warp=> coeff n p.x) (Carryon.Warp.deposit p h)
 rw [Warp.turning, AlignSeries.subst_finite p.atOrigin, Finset.sum_range_succ, high] at he; change B+ x*C=A at he; have hm : C≠0 := pow_ne_zero _ h; change x=(A-B)*C⁻¹; rw [← div_eq_mul_inv, eq_div_iff hm]; linarith

variable (hp:a ≠ 0)(ht : Tendsto (fun i=> coeff 1 (p i).x) l (𝓝 a))
variable (hz:Posi P r (fun i=>(p i).x) (fun i=>(q i).x))
include hp ht hz
lemma refund (n:ℕ)(hn:n≤r): Fair P (fun i=>coeff n (p i).refund.x) (fun i=>coeff n (q i).refund.x):= by
 induction n using Nat.strong_induction_on with
 | _ n ih=>
   obtain h|h:= Nat.eq_zero_or_pos n
   · subst n; simp only [coeff_zero_eq_constantCoeff_apply, inverse_zero]; exact Fair.fixed _
   let x (p:Warp):= ((coeff 1 p.x)^n)⁻¹; have hz' := hz 1 (Nat.le_trans h hn)
   have hu : Fair P (fun i=>x (p i)) (fun i=> x (q i)) := (hz'.pow n).press (hasStrictFDerivAt_inv (𝕜:=ℝ) (pow_ne_zero n hp)) (ht.pow n) -- inspect specialization
   have he : Fair P (fun i=> early (p i) n) (fun i=>early (q i) n):= Fair.sum _ fun j hj=> (ih j (mem_range.mp hj) ((mem_range.mp hj).le.trans hn)).mul (hz.pow j n hn)
   have hh := isOpen_compl_singleton.mem_nhds (s:=({0}ᶜ:Set ℝ)) hp -- inspect
   apply (((Fair.fixed (coeff n (PowerSeries.X:fps))).minus he).mul hu).fit
   · filter_upwards [ht.eventually hh] with i hi; exact (recur _ hi n).symm
   filter_upwards [(hz'.both _ ht).eventually hh] with i hi; exact (recur _ hi n).symm
end YM.FormalOPE.RG10.Boardwalk.Regatta
