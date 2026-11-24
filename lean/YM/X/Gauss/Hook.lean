import YM.X.Jet.Reach
import YM.X.Gauss.Plausible
/-!
# Leading and first-variation ordinary Hessian report along a shaped section.
Analytic calculus (first two potentially nonzero orders).
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gauss
open Function Set Filter Work.G05 Jet PertExtension PertExtension.Series
open Radial
open scoped BigOperators Classical Topology ContDiff
variable {E F : Type*}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {n i:ℕ} {f g:ℝ→ℝ} {p:E→ℝ} (hp:ContDiffAt ℝ ω p 0)
lemma jo_sum (hf:ContDiffAt ℝ ω f 0)(hg:ContDiffAt ℝ ω g 0) : someJ (f+g) n=someJ f n+someJ g n:= ((Act.add (show Act n f (someJ f) from ⟨hf,fun _ _=> rfl⟩) (show Act n g (someJ g) from ⟨hg,fun _ _=>rfl⟩)).writes n le_rfl)
lemma jo_mul (hf:ContDiffAt ℝ ω f 0)(hg:ContDiffAt ℝ ω g 0): someJ (f*g) n=∑ i∈Finset.range (n+1),someJ f i * someJ g (n-i):= by
   simp only [someJ,iteratedDeriv_mul (hf.of_le (show ↑n≤ω from le_top)) (hg.of_le le_top),smul_eq_mul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; have h:i≤n:= Nat.le_of_lt_succ (Finset.mem_range.mp hi)
   have h₁ : ↑(n.choose i) * (i.factorial:ℝ) * (n-i).factorial =(n.factorial:ℝ):= by exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
   field_simp; rw [←h₁]; ring
lemma jo_shift (hf:ContDiffAt ℝ ω f 0) (k:ℕ) : someJ ((fun r:ℝ=> r^k)*f) n= if k≤n then someJ f (n-k) else 0:= by
    rw [jo_mul (by fun_prop) hf]; have he(i:ℕ): someJ (fun r:ℝ=>r^k) i= if i=k then 1 else 0:= by rw [someJ,iteratedDeriv_fun_pow_zero]; split_ifs with h; subst i; exact inv_mul_cancel₀ (by positivity); simp
    simp only [he]; simp [ite_mul]
lemma jo_one {f:ℝ→F} : someJ f 1=deriv f 0:= by simp [someJ]

variable {w:Word E} {a:ℝ→E} (ha:Act (n+2) a w) (hz:w 0=0)
include hp ha hz
lemma tick_base (ht:∀ j<n,jet p j=0)(hi:i≤n+1): someJ (p ∘ a) i=if i=n then jet p n (w 1) else if i=n+1 then jet p (n+1) (w 1)+ fderiv ℝ (jet p n) (w 1) (w 2) else 0:= by
   let b:=delay w (n+2); let D:=blockTaylor (n+1) p; let s (k:ℕ):= w (k+1); let m:=delay s (n+1)
   have he : b=(fun t:ℝ=> t • m t) := by
      funext t; unfold m b delay; rw [Finset.smul_sum,Finset.sum_range_succ',hz, smul_zero,add_zero]; unfold s; apply Finset.sum_congr rfl; intro m hm; rw [pow_succ', smul_smul]
   have hs(i:ℕ): Tensor.diagonal (Tensor.coeff p i 0)=jet p i:= by ext; simp [Tensor.diagonal,Tensor.coeff,jet]
   have hd:D=jet p n + jet p (n+1):= by unfold D blockTaylor; simp_rw [hs,Finset.sum_range_succ]; rw [Finset.sum_eq_zero, zero_add]; intro b hb; exact ht b (Finset.mem_range.mp hb)
   have hb:Act (n+2) b w:= Act.swell _ le_rfl; have hD0:ContDiff ℝ ω D:= blockTaylor_contDiff (n+1) p _
   have hmc:ContDiff ℝ ω m:= Pert.Position.curve_diff s _; have hm: Act (n+1) m s:= Act.swell _ le_rfl; have hm' : deriv m 0=w 2:= by rw [← jo_one]; exact hm.writes 1 (by omega)
   have h' : someJ (p ∘ a) i=someJ (D ∘ b) i := by
      calc _ = someJ (p ∘ b) i:= ((ha.transit (m:=p) (by rwa [hz])).writes i (by omega)).trans (((hb.transit (m:=p) (by rwa [hz])).writes i (by omega)).symm)
           _ = _:= by
              unfold someJ; simp only [iteratedDeriv_eq_iteratedFDeriv]; congr 2; symm; apply jets_comp (hb.nice.of_le le_top) (hb.nice.of_le le_top) (hD0.contDiffAt.of_le le_top) (by rw [hb.zero,hz]; exact hp.of_le le_top) rfl (fun _ _=>rfl) (by rw [hb.zero,hz]; exact blockTaylor_jets (hp.of_le le_top)) _ hi
   have hjet(k:ℕ): ContDiffAt ℝ ω (jet p k ∘ m) 0:= (Tensor.diag_smooth (Tensor.coeff p k 0) ω|>.contDiffAt|>.congr_of_eventuallyEq (Filter.Eventually.of_forall fun i=> (congr_fun (hs _) i).symm)).comp _ hmc.contDiffAt
   have hne(k:ℕ): jet p k ∘ b=(fun t:ℝ=>t^k)*(jet p k ∘ m):= by
      rw [he]; funext t; rw [comp_apply,jet_smul];rfl
   rw [h',hd, show (jet p n + _) ∘ b=jet p n ∘ b+jet p (n+1) ∘ b from rfl,hne,hne,jo_sum (f:=(fun t:ℝ=>t^n)*(jet p n ∘ m)) (g:=(fun t:ℝ=>t^(n+1))*(jet p (n+1) ∘ m)) ((by fun_prop : ContDiffAt ℝ ω (fun t:ℝ=> t^n) 0).mul (hjet _)) ((by fun_prop : ContDiffAt ℝ ω (fun t:ℝ=> t^(n+1)) 0).mul (hjet _)), jo_shift (hjet _),jo_shift (hjet _)]
   rcases eq_or_lt_of_le hi with h|h
   · subst i; simp only [le_add_iff_nonneg_right, Nat.zero_le, if_true, add_tsub_cancel_left, le_refl, tsub_self,someJ_zero,comp_apply,hm.zero]; rw [if_neg (by omega),jo_one]; change _+jet p (n+1) (w 1)=_
     rw [show deriv (jet p n ∘ m) 0=fderiv ℝ (jet p n) (w 1) (w 2) from ?_,add_comm]
     rw [←show m 0=w 1 from hm.zero, ←hm']; exact ((show DifferentiableAt ℝ (jet p n) (m 0) from (hs n) ▸ ((Tensor.diag_smooth _ 1).differentiable (by simp) _)).hasFDerivAt.comp_hasDerivAt _ ((hmc.differentiable (by simp) _).hasDerivAt)).deriv
   by_cases hp : i=n
   · subst i; rw [if_pos le_rfl, if_neg (by omega), if_pos rfl, Nat.sub_self,someJ_zero]; rw [comp_apply, hm.zero]; exact add_zero _
   have ha : i < n:= by omega
   rw [if_neg ha.not_ge, if_neg h.not_ge, if_neg hp, if_neg h.ne]; exact add_zero _
end YM.PositionX.Gauss
