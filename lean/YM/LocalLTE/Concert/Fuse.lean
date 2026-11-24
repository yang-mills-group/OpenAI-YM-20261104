import YM.LocalLTE.Concert.Budget
/-! # Rebudgeting a given authorization. Exact scaled power preserved on *same* supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay Fan
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B A C:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Push.AbsoluteSums
variable {a b d l x y z:ℝ} (m:ℕ) (hs:Fintype.card V ≤ m)
omit [Fintype V] in
lemma budgetUp (h:B.Radial r a b d l)(hz:a≤x)(hu:b≤y)(he:d*l ≤ z*l) : B.Radial r x y z l:=by
   obtain ⟨hr,h0,hL,⟨s,hS,hT⟩,s',hU,hV⟩:=h
   exact ⟨hr,fun i=> (h0 i).trans hz,hL,⟨s,hS,fun i=> budget_loosen (hT i) hu⟩,s',hU,fun i=>budget_loosen (hV i) he⟩
-- one case.A.General
include hs
lemma oppositeBank (h:B.Radial r a b d l)(s:V→ℝ)(hz:∀ i,0<s i)(hy:1 ≤ κ)(hu:∀ i,s i ≤ κ*r i): B.Radial s (κ*a) (κ^m*b) (κ^m*d) l:=by
   have hh:0≤κ:=zero_le_one.trans hy; let S:= κ^m; have hv:0≤ S:=pow_nonneg hh _
   have he(i:R.Mode): Poly.toll s i ≤ S*Poly.toll r i:=by
      refine (prod_le_prod (fun j _=> (hz j).le) (fun j _=> hu j)).trans ?_; rw [prod_mul_distrib,prod_const]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hy (i.val.card_le_univ.trans hs)) (Poly.worth h.pure _).le
   obtain ⟨hR,h0,hL,⟨p,hp,hP⟩,s',hE,hQ⟩:=h
   refine ⟨hz,fun i=> ?_,hL,⟨p,hp,fun i=>?_⟩,s',hE,fun i=>?_⟩
   · apply le_trans (mul_le_mul_of_nonneg_right (hu i) (norm_nonneg _)) _; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (h0 i) hh
   · refine budget_mono (budget_scale hv (hP i)) (fun i=> ?_) (fun j=>?_)
     · split; exact mul_nonneg (Poly.worth hz _).le (mul_nonneg (Real.exp_nonneg _) (hp i|>.1)); rfl
     split; next h=>rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (he _) (mul_nonneg (Real.exp_nonneg _) (hp j|>.1))
     rw [mul_zero]
   rw [mul_assoc]; refine budget_mono (budget_scale hv (hQ i)) (fun j=> ?_) (fun j=>?_)
   · split; exact mul_nonneg (Poly.worth hz _).le (mul_nonneg (Real.exp_nonneg _) (hE j.1 j.2|>.1)); rfl
   split; next h=>rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (he _) (mul_nonneg (Real.exp_nonneg _) (hE j.1 j.2|>.1))
   rw [mul_zero]
-- actual κ.Paid relative denominator.Division. connection d*g(m)
open Mallow
lemma honours (x t:ℝ)(ht:0≤t)(hx:1≤x)(h:B.Radial (fun _=> Mallow.neat x t) a b d l) : B.Radial (fun _=>1) (x^(t+2)*a) (x^((t+2)*m)*b) (x^((t+2)*m)*d) l:=by
    let κ:= x^(t+2); have hx':0<x:= zero_lt_one.trans_le hx; have he:1≤κ:= Real.one_le_rpow hx (by positivity)
    simp_rw [Real.rpow_mul_natCast hx'.le]; exact Port.oppositeBank B _ m hs h _ (fun _=>zero_lt_one) he (fun i=>le_of_eq (by unfold neat; rw [← Real.rpow_add hx',show t+2+(-t-2)=0 by abel,Real.rpow_zero]))
lemma fenestrated (x t:ℝ)(ht:0≤t)(hx:1≤x)(h:B.Radial (fun _=> neat x t) 0 (x^(-σ)) (x^(-σ)) l)(e:ℝ)(hp: (t+2)*m+(-σ) ≤ -e) (he: x^(-e) ≤ d): B.Radial (fun _=>1) 0 d d l:=by
   have hh:= Port.honours B m hs x t ht hx h; rw [mul_zero,← Real.rpow_add (by positivity)] at hh
   have ht':= le_trans (Real.rpow_le_rpow_of_exponent_le hx hp) he; exact Port.budgetUp B _ hh le_rfl ht' (mul_le_mul_of_nonneg_right ht' h.factor.le)
end YM.LocalLTE.Port
