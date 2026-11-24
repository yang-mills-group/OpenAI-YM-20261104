import YM.MSbar.Heath.Shaft
import YM.MSbar.Heath.Far
import YM.MSbar.LocalSD.Escrow
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V:Config G n}{x:Site n}{R:Rep G n}
variable {k:ℕ}(q:ℕ→Atom G k)(p:BudgetPoint)(j:Site n){σ C Λ δ w:ℝ}(hx:Stab x U V)
open Finset
include hx
set_option maxHeartbeats 350000 in
lemma additive_var (A:Activities G n)(h:A.Valid p δ w): |A.additive p U-A.additive p V| ≤ δ * (2*Real.exp (p.supportExponent*10))*((2*(4*p.B+2)+1:ℝ)^4* meter p.supportExponent):=by
    obtain ⟨b,hb,hP⟩:= h.boundE; let t:=2*Real.exp (p.supportExponent*10); let α:=p.supportExponent; have hL:0 < α:=p.exponent_pos; let m:=4*p.B+2; have hm:0 < m:=by dsimp only [m]; omega
    let R(i:ℕ):=A.reg i; let f i y:= A.regularOccurrence p i y; let w(j: Site n):= Heath.wick m p.supportExponent x j * t; have hw j :0 ≤ w j:=by unfold w t Heath.wick; positivity
    have hs j : SumBudget (fun i=>if (R i).site=j then w j* p.mass (R i).support (b i) else 0) (w j*δ):=by
       convert budget_scale (hw j) (hP j) using 1; funext i; split; congr 1; rw [mul_zero]
    let v j i:= if (R i).site=j then w j*p.mass (R i).support (b i) else 0
    have hz := budget_over Finset.univ v (fun j=> w j*δ) (fun j _=> hs j)
    have he i : |f i U-f i V| ≤ ∑ j,v j i:=by
       have h₀ (V: Config G n): |f i V|≤ b i :=by
          unfold f Activities.regularOccurrence; by_cases hh: Healthy p.threshold (R i).support V; exact (congr_arg abs (masked_eq _ _ _ _ hh)).trans_le ((hb i).2 _ hh [] (Nat.zero_le _) (by simp)); rw [masked_ne _ _ _ _ (show ¬Healthy p.threshold (R i).support V from hh),abs_zero]; exact (hb i).1
       let P:=R i; by_cases hh:x∉ inspected P.support
       · have hp:f i U=f i V :=by
            have hz : UsesFinal p.threshold P.support (f i):=by
               refine fun U V hc he=> ?_; have hh : Healthy p.threshold P.support V ↔ Healthy p.threshold P.support U:=by unfold Healthy; rw [disjoint_iff_inter_eq_empty,← he,disjoint_iff_inter_eq_empty] -- check order
               by_cases hx: Healthy p.threshold P.support U
               · unfold f Activities.regularOccurrence; rw [masked_eq _ _ _ _ hx, masked_eq _ _ _ _ (hh.mpr hx), (h.regular.smooth i).sites U V hc]
               unfold f Activities.regularOccurrence; rw [masked_ne _ _ _ _ hx, masked_ne _ _ _ _ (hh.not.mpr hx)]
            exact (UsesFinal.allReads _ _ (f i) hz) U V (hx _ hh)
         rw [hp,sub_self,abs_zero]; exact hz.1 _
       obtain ⟨y,hy,H⟩:= halo_spec.mp (Next.Scheduling.flag_layer _ (not_not.mp hh)); let c:= coverNumber p.B P.support; let k':=separation x P.site/m
       have ht:= Corona.extent P.support p.B hy P.anchor
       have hi: separation x P.site ≤ m*(c+10):=by rw [separation_comm y x] at H; refine (separation_triangle x y P.site).trans ((Nat.add_le_add H ht).trans ?_); unfold m; dsimp only [c]; ring_nf; omega
       have hg : (k':ℝ) ≤ (c:ℝ)+10:=by exact_mod_cast ((Nat.div_le_div_right hi).trans_eq (Nat.mul_div_cancel_left _ hm))
       have hm : 2 ≤ w P.site*Real.exp (p.supportExponent * c):=by
          unfold w Heath.wick t; rw [mul_left_comm, mul_assoc 2, ← Real.exp_add,← Real.exp_add]; apply le_mul_of_one_le_right zero_le_two; apply Real.one_le_exp; linarith only [mul_le_mul_of_nonneg_left hg hL.le]
       refine (abs_sub _ _).trans ((add_le_add (h₀ _) (h₀ _)).trans ?_); unfold v; simp only [Finset.sum_ite_eq, mem_univ, ↓reduceIte]; unfold BudgetPoint.mass; rw [← two_mul, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hm (hb i).1
    have hu:=Activities.ESeries h
    refine (cherished (fun i=> f i U) (fun i=> f i V) (fun i=>∑ j,v j i) (hu.summable U) (hu.summable V) hz he).trans ?_
    unfold w; simp_rw [← Finset.sum_mul]; have hi := wick_pays hL m hm x; have ht : 0≤t := by unfold t; positivity
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi ht) (show 0 ≤ δ from budget_nonneg (hP x))).trans_eq _; unfold t m; push_cast; ring
end YM.MSbar.Heath
