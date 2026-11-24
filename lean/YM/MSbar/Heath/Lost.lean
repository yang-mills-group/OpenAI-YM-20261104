import YM.MSbar.Heath.Breath
import YM.SectorNext.VACUUM_NORMALIZATION.Noise

/-! Using the GOOD output ledger, control even to orientations not connected to
identity. Do this before taking logs of U. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{c f:Side}{U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v x δ w:ℝ}
open Finset
open YM.MSbar.Bulk SectorNext.Vacuum
variable (S:StepData c f) (p:Edge (Site c))(q:G.El)(X:Config G c)
   {g:Config G f→ℝ}
def spun (x : ℝ) (W:Config G c)(b:Edge (Site c)):= (S.penaltyZ x G)⁻¹ * S.penaltyWeight x (W b * (X b)⁻¹)
private lemma bills (V:Config G c) : (∫ k,S.noise x X (update V p k)∂G.probHaar)=∏ i∈univ.erase p, spun S X x V i:=by
   let r:=∏ i∈univ.erase p, spun S X x V i
   let b(k:G.El):= S.penaltyWeight x (k*(X p)⁻¹)
   have h(k) : S.noise x X (update V p k)=((S.penaltyZ x G)⁻¹ * b k)*r:=by
       unfold StepData.noise; rw [← mul_prod_erase _ _ (mem_univ p),Function.update_self]; exact congr_arg _ (prod_congr rfl (fun i hi=>by rw [update_of_ne (ne_of_mem_erase hi)];rfl))
   have hg : (∫ u:G.El,b u∂G.probHaar)= S.penaltyZ x G:=by
       have h := (measurePreserving_mul_right G.probHaar (X p)⁻¹).integral_comp ((Homeomorph.mulRight (X p)⁻¹).measurableEmbedding) (S.penaltyWeight x); exact h
   simp_rw [h,integral_mul_const,integral_const_mul,hg,inv_mul_cancel₀ (S.penaltyZ_pos _|>.ne'),one_mul];rfl
lemma cord (hp:a≤G.chord (V p * (X p)⁻¹)) (he:0 ≤ a) (hz:0 ≤ x): S.noise x X V ≤ Real.exp (shellBill G S x-x*S.kernel.penalty*a^2/2)*∫ k,S.noise x X (update V p k)∂G.probHaar :=by
    rw [bills]; unfold StepData.noise; rw [← mul_prod_erase _ _ (mem_univ p)]; apply mul_le_mul_of_nonneg_right
    · let u := V p*(X p)⁻¹; have hh : a^2 ≤ 2*G.price u:= (pow_le_pow_left₀ he hp _).trans_eq (G.chord_price _)
      rw [sub_eq_add_neg,Real.exp_add]; apply mul_le_mul
      · exact (inv_anti₀ (Real.exp_pos _) (pZ_lo (G:=G) S x)).trans (by rw [← Real.exp_neg,neg_neg])
      · unfold StepData.penaltyWeight; apply Real.exp_monotone; have he:=mul_le_mul_of_nonneg_left hh (show 0≤x*S.kernel.penalty from mul_nonneg hz S.kernel.penalty_pos.le); linarith only [he]
      exact (Real.exp_pos _).le; exact (Real.exp_pos _).le
    exact Finset.prod_nonneg fun i _=> mul_nonneg (inv_pos.mpr (S.penaltyZ_pos _)).le (Real.exp_pos _).le
private lemma continuous_noise (S:StepData c f) (V X:Config G c) {u:Edge (Site c)}(h:Continuous (fun i:G.El=> Function.update V u i)) : Continuous (fun i:G.El=> S.noise a X (Function.update V u i)):= by
    change Continuous ((fun p:Config G c×Config G c=> S.noise a p.1 p.2) ∘ (fun i:G.El=> (X,update V u i))); exact (S.noise_cont (G:=G) a).comp ((show Continuous (fun _:G.El=> X) from continuous_const).prodMk h)
variable {P:Rep G c}(h:Admitted V R S σ C δ T w)
    {κ σ' C' w' T' δ':ℝ}(ht:P.Lawful σ' C' T' δ' w')
variable (hw:V∈ calm G c v) (hζ:v≤P.p.threshold)(hv:0<v)(hc:Decent P.clip P.p)
local notation "W"=> fun k=>update V p k
include h ht hw hζ
variable (hk: P.eval=S.push R.beta R.eval)
include hv hk hc
lemma lost (H:Set (Config G f))(hH:MeasurableSet H)(hb:0 ≤ P.beta)(hd : S.patch.Branches S.kernel G) (ha : ∀ x∈H,∀ k:S.Choices, S.likelihood x k≠0→ a ≤ G.chord (V p*(S.prediction x k p)⁻¹)) (he:0≤a)(hz:0≤R.beta) : chance S R V H ≤ Real.exp (ankle P.p P.clip σ' C' δ' T' v w' P.beta)* Real.exp (shellBill G S R.beta - R.beta*S.kernel.penalty*a^2/2):=by
   let q:=R.beta; let b:=Real.exp (shellBill G S q-q*S.kernel.penalty*a^2/2);have hy:0≤b:= (Real.exp_pos _).le
   have hWC : Continuous (fun k:G.El=> update V p k):=continuous_pi (fun i=> by
       by_cases hi:i=p
       · subst i; simp_rw [Function.update_self]; exact continuous_id
       simp_rw [update_of_ne hi]; exact continuous_const)
   have hu (x: Config G f)(ht:x∈H): S.density q x V ≤ b*∫ k:G.El,S.density q x (W k)∂G.probHaar:=by
       unfold StepData.density; rw [integral_finsetSum, Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; rw [integral_const_mul,mul_left_comm]
       by_cases hv:S.likelihood x i=0
       · simp only [hv,zero_mul,le_refl]
       exact mul_le_mul_of_nonneg_left (cord S p _ (ha x ht i hv) he hz) (S.likelihood_pos _ _)
       intro i h'; let u(k:G.El):= S.noise q (S.prediction x i) (update V p k)
       have hg:Continuous u:=continuous_noise S V (S.prediction x i) hWC
       have hh: Integrable u G.probHaar:= hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); exact hh.const_mul _
   let Y(x:Config G f×G.El):= S.density q x.1 (W x.2)* R.eval x.1; have hY : Integrable Y ((prior G f).prod G.probHaar):=by
       refine Envelope.integrable ?_ _; let z (u:Config G f×G.El):= S.density q u.1 (W u.2)
       have hm: Measurable z:= by
          change Measurable ((fun s:Config G f×Config G c=> S.density R.beta s.1 s.2)∘(fun v:Config G f×G.El=> (v.1,W v.2))); exact h.kernel.meas.comp ((measurable_fst (α:=Config G f)).prodMk (hWC.measurable.comp measurable_snd))
       obtain ⟨B,hB⟩:=h.kernel.bound
       obtain ⟨ha,hA⟩:=(R.envelope h.lawful)
       obtain ⟨D,hD⟩:= hA
       exact (show Envelope z from ⟨hm,B,fun i=>Real.norm_of_nonneg (h.kernel.positive ..) |>.trans_le (hB ..)⟩).mul ⟨ha.comp measurable_fst,D,fun i=>hD _⟩
   let Q:= H.indicator (fun _=> (1:ℝ)); let A:= S.push q R.eval V; let D:= Real.exp (ankle P.p P.clip σ' C' δ' T' v w' P.beta)
   have hj: S.push q (Q*R.eval) V ≤∫ x: Config G f,b* (∫ v, Y (x,v) ∂G.probHaar) ∂ prior G f:=by
       apply integral_mono (StepData.push_slice h.kernel _ _ ?_) (Integrable.const_mul hY.integral_prod_left _) -- order
       · intro i; dsimp only; rw [Pi.mul_apply]; by_cases hv:i∈H
         · rw [show Q i=1 from Set.indicator_of_mem hv _,one_mul]
           apply le_trans (mul_le_mul_of_nonneg_right (hu _ hv) (h.positive _)) (le_of_eq ?_)
           dsimp only [Y]; rw [integral_mul_const,mul_assoc]
         rw [show Q i=0 from Set.indicator_of_notMem hv _,zero_mul,smul_zero]; exact mul_nonneg hy (integral_nonneg fun i=>mul_nonneg (h.kernel.positive _ _) (h.positive _))
       exact (show Envelope (Q*R.eval) from Envelope.mul (Envelope.piece (p:=fun i=>i∈ H) hH (Envelope.const _) (Envelope.const _)) (R.envelope h.lawful)).integrable _
   have hx(k:G.El) : (∫ x : Config G f, Y (x,k)∂ prior G f) ≤ A*D :=by
       change S.push q R.eval (update V p k) ≤ A*D; unfold A; unfold q D; rw [← hk]; exact tavern ht hv hw (stitch p V k) hb hc hζ -- notation
   rw [integral_const_mul, ← integral_prod Y hY, integral_prod_symm _ hY] at hj
   change S.push q _ V / A ≤ D*b; rw [div_le_iff₀ h.mass]; apply hj.trans
   have hs:= integral_mono hY.integral_prod_right (integrable_const (μ:=G.probHaar) _) hx
   refine (mul_le_mul_of_nonneg_left (show _≤ A*D from hs.trans_eq (by simp)) hy).trans_eq (by ring)
end YM.MSbar.Heath
