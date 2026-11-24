import YM.MSbar.Transfer.Primary
import Mathlib.Analysis.Real.Pi.Bounds

/-! Toll for high positive dimensional counts. Kept kernels on compact connecting region. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Transfer
open Complex Metric Filter Set MeasureTheory Function
open Dim Dim.Dual
open scoped Topology ContDiff BigOperators Classical
variable {j m k n : ℕ} {t z : ℂ} {K T : ℝ} {X Y: Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma γ_cost (m:ℕ)(z:ℂ)(h : m < z.re) : ‖Γ (z-m)‖ ≤ ‖z‖^m * ‖Γ z‖ := by
    have hp : 0 < (z-m).re:= by simpa
    have he : 1 ≤ Real.pi:= by linarith [Real.pi_gt_three]
    have hE : 0 < Real.pi:=Real.pi_pos
    induction m with
    | zero => simp
    | succ m ih =>
       let w:=z-(m+1:ℕ); have hw:w+1=z-m:=by unfold w; push_cast; ring
       have hh: Γ w= (w / (↑Real.pi:ℂ))*Γ (w+1):=by
           unfold Γ; have h':w≠0:= fun h' => (by change 0< w.re at hp; simp [h'] at hp)
           have hP : (↑Real.pi:ℂ)≠0:= by exact_mod_cast hE.ne'
           rw [Gamma_add_one _ h', Complex.cpow_add _ _ hP, cpow_one]; field_simp
       have ht : ‖w/(↑Real.pi:ℂ)‖≤ ‖z‖:=by
          rw [norm_div, Complex.norm_real,Real.norm_of_nonneg hE.le]; apply (div_le_iff₀ hE).mpr
          refine le_trans ?_ (le_mul_of_one_le_right (norm_nonneg z) he)
          unfold w; apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
          simp only [Complex.sq_norm,normSq_apply,sub_re,sub_im,natCast_re,natCast_im,sub_zero]; push_cast at h ⊢; nlinarith [Nat.cast_nonneg m (α:=ℝ)]
       have hM:m<z.re:=lt_trans (Nat.cast_lt.mpr (Nat.lt_succ_self _)) h
       change ‖Γ w‖ ≤ _; rw [hh,hw,norm_mul]; exact (mul_le_mul ht (ih hM (by simpa)) (norm_nonneg _) (norm_nonneg _)).trans_eq (by rw [pow_succ]; ring)
lemma exponential (K : ℝ) : ∃ A:ℕ, ∀ m:ℕ,∀ z:ℂ,m+1< z.re → ∀ u∈ collar m K,
     ‖weight (z-m) u‖ ≤ Real.exp (A*z.re) :=by
    let C:= 1+K^2; have hc:1≤C:= by unfold C; nlinarith [sq_nonneg K]
    have hC:0<C:=zero_lt_one.trans_le hc
    obtain ⟨A,hA⟩:=exists_nat_ge (Real.log C); refine ⟨A,fun m z hz u hu=> ?_⟩
    let v:=u.2; let s:=z-m-1; have he:0<s.re:= by unfold s; simp; linarith
    have hp : 0≤ v:=hu.2.1
    change ‖(v:ℂ)^s‖≤_
    rcases eq_or_ne v 0 with h|h
    · rw [h, ofReal_zero, zero_cpow (by intro h; simp [h] at he),norm_zero]; exact (Real.exp_pos _).le
    rw [norm_cpow_eq_rpow_re_of_pos (lt_of_le_of_ne hp h.symm)]
    have hr:0≤z.re:=by linarith [Nat.cast_nonneg m (α:=ℝ)]
    calc _ ≤ C^z.re:= (Real.rpow_le_rpow hp ((show v ≤ K^2 from hu.2.2).trans (by unfold C; linarith)) he.le).trans (Real.rpow_le_rpow_of_exponent_le hc (by unfold s; simp; linarith [Nat.cast_nonneg m (α:=ℝ)]))
         _ ≤ _ := by rw [Real.rpow_def_of_pos hC]; gcongr

lemma plate_market {F:ℂ × (X × Hat (m+1)) →ℂ} (h:Market j F) (hp : ∀ z x,Packed m K fun y=>F (z,x,y)) :
   Market (1+j) (fun p:ℂ×X => plate p.1 (fun t=>F (p.1,p.2,t))) := by
   let S:= collar m K;have hS : IsCompact S:= collar_compact ..
   have hK:=hS.image seed_c; obtain ⟨A,hA⟩:=exponential K
   intro Xs hc; obtain ⟨T,C,ht,hC,n,N,h⟩:= (h _ (hc.prod hK)).books (m+2)
   let c:=volume.real S; have hy:0 ≤ c:= ENNReal.toReal_nonneg
   refine ⟨T,c*C,A+n,m+N,mul_nonneg hy hC,fun z hz x hx=> ?_⟩
   have he:m+1< z.re := by linarith
   have hp':1<(z-m).re:=by simp; linarith
   let L:=Real.exp (A*z.re) * toll j n N C z
   have hw:0≤L:=mul_nonneg (Real.exp_pos _).le (toll_nn hC)
   dsimp only; rw [lifted (hp z x) hp',norm_mul]
   let g (u:Cells m):= F (z,x,seed u); change ‖Γ (z-m)‖ * ‖∫ u in S,weight (z-m) u*g u‖ ≤ _
   haveI:IsFiniteMeasure (volume.restrict S):= ⟨by rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top⟩
   calc
    _ ≤ (‖z‖^m * ‖Γ z‖)*(c*L):= by
      refine mul_le_mul (γ_cost m z (by linarith)) ?_ (norm_nonneg _) (by positivity)
      change _ ≤ c*L; rw [show c*L=∫ _ in S,L from (by rw [setIntegral_const]; rfl)]
      apply norm_integral_le_of_norm_le (integrable_const _); filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
      rw [norm_mul]; exact mul_le_mul (hA m z he u hu) (h z hz _ ⟨hx,mem_image_of_mem _ hu⟩) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by unfold c L toll; simp only [pow_add,Nat.cast_add,add_mul,Real.exp_add,pow_one]; ring

lemma Market.average [MeasurableSpace Y] [BorelSpace Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y] {μ:Measure Y} [IsLocallyFiniteMeasure μ] {K:Set Y}(hc:IsCompact K) {F : ℂ × (X × Y)→ℂ} (H: Market j F) : Market j (fun x:ℂ×X=> ∫ y in K,F (x.1,x.2,y) ∂μ):=by
   intro W hW; obtain ⟨t,C,ht,hC,m,n,h⟩:= (H _ (hW.prod hc)).books 0
   haveI:IsFiniteMeasure (μ.restrict K):= ⟨by rw [Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
   refine ⟨t,μ.real K*C,m,n,mul_nonneg ENNReal.toReal_nonneg hC, fun z hz x hx=>?_⟩
   dsimp only; rw [← pay_rate,show μ.real K*_=(∫ y in K, toll j m n C z ∂μ) from (by rw [setIntegral_const]; rfl)]
   exact norm_integral_le_of_norm_le (integrable_const _) ((ae_restrict_mem hc.measurableSet).mono fun y hy=> h z hz _ ⟨hx,hy⟩)
end YM.MSbar.Transfer
