import YM.OPE.Compatible.Karls.Bent
/-! # homogeneous crowns, going backwards. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{m k i:ℕ}{q:ℝ}(p:E→L[ℝ] E)
local notation "X!"=> E→L[ℝ] E
open Filter Finset
open Quit.PriceZ
-- unselected ω.Unique.Theta.
variable [FiniteDimensional ℝ E]
open Set Filter
lemma temple_l (V:ℕ→ Dice E)(A:E→ℝ) (h:∀ v,Tendsto (fun i=>V i v v) atTop (𝓝 (A v)))(x:ℕ→ E)(l:E)(S:ℕ→ℕ)(hp:Tendsto S atTop atTop)(hv:Tendsto x atTop (𝓝 l)): Tendsto (fun i=> V (S i) (x i) (x i)) atTop (𝓝 (A l)):=by
   let g:= Module.finBasis ℝ E; let k:= Module.finrank ℝ E; let Y(i:ℕ): Dice E:= (2:ℝ)⁻¹ • (V i+(V i).flip); have ht(i v):Y i v v=V i v v:=by unfold Y; simp; ring
   have hx(i u v):2*Y i u v=V i (u+v) (u+v)-V i u u-V i v v:=by unfold Y; simp; ring
   let B(a b):= (A (a+b)-A a-A b)* (2:ℝ)⁻¹; have he(u v): Tendsto (fun i=> Y i u v) atTop (𝓝 (B u v)):=by
       unfold B; apply (( ((h (u+v)).sub (h u)).sub (h v)).mul_const _).congr; intro i; rw [← hx]; ring
   let p(i:Fin k)(u:E):= g.equivFun u i; have hz(i:ℕ)(u:E):V i u u= ∑ a,∑ b,p a u*p b u*Y i (g a) (g b):=by
      let f(a):=p a u • g a; have hh: u=∑ a,f a:=(g.sum_equivFun u).symm
      rw [← ht]; conv_lhs => rw [hh]
      simp only[map_sum,_root_.sum_apply]; apply Finset.sum_congr rfl; intro i hi; refine Finset.sum_congr rfl fun b _=>?_ ; unfold f; simp only [map_smul,_root_.smul_apply,smul_eq_mul]; unfold Y; simp; ring -- sum duplicates
   let b:=∑ i,∑ j,p i l*p j l*B (g i) (g j); have hC(x:ℕ→ E)(u:ℕ→ℕ)(hp:Tendsto u atTop atTop)(hx:Tendsto x atTop (𝓝 l)): Tendsto (fun i=> V (u i) (x i) (x i)) atTop (𝓝 b):=by
       simp_rw [hz]; have ha:Tendsto (fun i=>g.equivFun (x i)) atTop (𝓝 (g.equivFun l)):= g.equivFun.toLinearMap.continuous_of_finiteDimensional.continuousAt.tendsto.comp hx; have hv(a): Tendsto (fun i=>p a (x i)) atTop (𝓝 (p a l)):= tendsto_pi_nhds.mp ha a; exact tendsto_finsetSum _ (fun i hi=>tendsto_finsetSum _ (fun j _=> ((hv i).mul (hv j)).mul ((he ..).comp hp)))
   rw [tendsto_nhds_unique (h l) (hC (fun i=>l) (id) tendsto_id tendsto_const_nhds)]; exact hC x S hp hv
lemma temple (V:ℕ→Dice E)(f:E→ℝ)(hp:∀ i: E,Tendsto (fun j=> V j i i) atTop (𝓝 (f i)))(hs:∀ i:E,i≠0→0 < f i):∀ᶠ j in atTop,∀ i:E,i≠0→0 < V j i i:=by
   by_contra! h
   have hf:∀ j:ℕ, ∃ i:ℕ,j ≤ i ∧ ∃ x: E, ‖x‖=1 ∧ V i x x ≤ 0:=by
        intro j; obtain ⟨i,H,x,hx,hV⟩:= frequently_atTop.mp h j
        let v:=‖x‖; have ht:v>0:= norm_pos_iff.mpr hx; refine ⟨i,H,v⁻¹ • x,?_ ,?_⟩
        · rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le), inv_mul_cancel₀ ht.ne']
        · simp only [map_smul,_root_.smul_apply,smul_eq_mul]; exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) hV)
   choose n H x hx hz using hf; have he:= (isCompact_sphere (0:E) 1).isSeqCompact; obtain ⟨p,hp',φ,hφ,hP⟩:= he (x:=x) (fun i=>by rw [Metric.mem_sphere,dist_zero_right]; exact hx i); have hN:p≠0:=by rintro rfl; simp at hp'
   have ht:=tendsto_atTop_mono H tendsto_id; exact not_lt_of_ge (le_of_tendsto' (temple_l V f hp _ _ _ (ht.comp hφ.tendsto_atTop) hP) fun i=>hz (φ i)) (hs p hN)
end YM.OPE.Hark
