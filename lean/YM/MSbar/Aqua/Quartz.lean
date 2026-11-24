import YM.MSbar.Aqua.Vine
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Work.G05
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {g h:E→F}{D B r:ℝ} {k q p: ℕ}
local notation "Ψ"=> iteratedFDeriv ℝ
lemma rod (n:ℕ)(l:List E)(x:E)(hf:ContDiffAt ℝ n g x)(he:l.length≤n): roc g l x=iteratedFDeriv ℝ l.length g x (l.get) :=by
    induction l generalizing x with|nil=>change g x= Ψ 0 g x (@List.get E []); rw [iteratedFDeriv_zero_apply]
                                       |cons a T ih=>
       have hh:T.length<n:=by rw [List.length_cons] at he; omega
       let L := ContinuousMultilinearMap.apply ℝ (fun _ :Fin T.length=>E) F T.get; let V:= iteratedFDeriv ℝ T.length g
       have hv: roc g T=ᶠ[𝓝 x] L ∘ V:= (hf.eventually (by simp)).mono (fun y hx=> ih y hx hh.le)
       rw [roc,hv.fderiv_eq, fderiv_comp _ L.differentiableAt (hf.differentiableAt_iteratedFDeriv (by exact_mod_cast hh)),L.fderiv]; change (fderiv ℝ (Ψ T.length g) x a) T.get = Ψ (T.length+1) g x ((a :: T).get); rw [iteratedFDeriv_succ_apply_left]; rfl
open Metric
lemma remQ (he: p+1 ≤ k) (hf:ContDiffAt ℝ k g 0) : ∃ r B:ℝ,0 < r∧ 0≤B ∧ ∀ i≤k, ∀ x:E, ‖x‖<r→ ContDiffAt ℝ k (g-blockTaylor p g) x ∧ ‖iteratedFDeriv ℝ i (g-blockTaylor p g) x‖ ≤ B*‖x‖^(p+1-i):=by
   let W:= g-blockTaylor p g; let c(i:ℕ) := ‖Ψ i W 0‖ ; let B := 1+∑ i∈range (k+1), c i; have h₀ : ContDiffAt ℝ k W 0:= hf.sub ((blockTaylor_contDiff p g _|>.contDiffAt)); have hB:0 ≤ B:=add_nonneg zero_le_one (Finset.sum_nonneg (fun i _ => norm_nonneg _))
   have hX:∀ᶠ x:E in 𝓝 0,∀ i∈ Finset.range (k+1),‖Ψ i W x‖ ≤ B:= (Finset.range _).eventually_all.mpr (fun i hi=>(h₀.continuousAt_iteratedFDeriv (k:=i) (by exact_mod_cast Nat.lt_succ_iff.mp (mem_range.mp hi))).norm.tendsto.eventually (ge_mem_nhds (show ‖Ψ i W 0‖<B from lt_of_le_of_lt (Finset.single_le_sum (f:=c) (fun j _=>norm_nonneg _) hi) (lt_add_of_pos_left (∑ j∈ Finset.range _, c j) zero_lt_one))))
   obtain ⟨r,hr,hZ⟩:= Metric.mem_nhds_iff.mp (hX.and (h₀.eventually (by simp)))
   have hz(x:E)(hx:‖x‖ < r) : (∀ i∈ Finset.range (k+1),‖Ψ i W x‖ ≤ B)∧ContDiffAt ℝ k W x:= hZ (mem_ball.mpr (by simpa only [dist_zero_right] using hx))
   refine ⟨r,B,hr,hB,fun i hi x hx=>⟨(hz x hx).2,?_⟩⟩; by_cases h:p+1 < i; rw [Nat.sub_eq_zero_of_le h.le,pow_zero,mul_one]; exact hz x hx|>.1 i (mem_range.mpr (by omega))
   let R:= ‖x‖; let t:= Metric.closedBall (0:E) R; have hu(y:E)(h:y∈t) : ‖y‖≤ ‖x‖:=by simpa only [t,R,mem_closedBall,dist_zero_right] using h
   have hq(i:ℕ)(hi:i≤p+1)(y:E)(hp:y∈t):‖Ψ i W y‖ ≤ B*‖x‖^(p+1-i):=by
        induction hi using Nat.decreasingInduction generalizing y with
        | self=>rw [Nat.sub_self,pow_zero,mul_one]; exact hz y ((hu y hp).trans_lt hx)|>.1 _ (mem_range.mpr (by omega))
        | of_succ i hi ih=>
           let V:= Ψ i W; have hv(z:E)(hd:z∈t): DifferentiableAt ℝ V z:= (hz z ((hu z hd).trans_lt hx)).2.differentiableAt_iteratedFDeriv (by exact_mod_cast (show i<k from by omega))
           have hA := (convex_closedBall (0:E) R).norm_image_sub_le_of_norm_fderiv_le hv (fun z hd => (show ‖fderiv ℝ V z‖≤ B*‖x‖^(p+1-(i+1)) from (by have ht:= ih z hd; rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, LinearIsometryEquiv.norm_map] at ht; exact ht))) (mem_closedBall_self (norm_nonneg _)) hp
           have he' : V 0=0:=by unfold V W; rw [iteratedFDeriv_sub_apply (hf.of_le (by exact_mod_cast hi.le.trans he)) (blockTaylor_contDiff p g _|>.contDiffAt),blockTaylor_jets (hf.of_le (by exact_mod_cast (show p ≤ k from by omega))) i (by omega),sub_self]
           rw [he',sub_zero,sub_zero] at hA; exact hA.trans ((mul_le_mul_of_nonneg_left (hu y hp) (by positivity)).trans_eq (by rw [show p+1-i= (p+1-(i+1))+1 from (by omega),pow_succ,mul_assoc]))
   exact hq i (by omega) x (mem_closedBall_zero_iff.mpr le_rfl)
end YM.MSbar.Aqua
