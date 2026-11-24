import YM.MSbar.Spruce.Pull
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Spruce
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Measuring
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Lodge Lapaz Analysis Kelvin
section
variable {ι σ τ: Type} [Fintype σ] [DecidableEq σ] [Fintype ι][DecidableEq ι]
variable (F:View σ→ℝ)(p k:ℕ){A: View σ}{c:Side}{l:σ→Site c} -- c undecl
variable {t a b w :ℝ}{g:ℝ→ℝ}(hF:∀ i∈Metric.closedBall (0:View σ) w,ContDiffAt ℝ (↑k) F i)
local notation "K"=> Metric.closedBall (0:View σ) w
variable (hp:Hat k w b g)(hk:2 ≤ k)(ht:∀ i<2,JetTab l a p w (Metric.closedBall 0 w) F i t)(hw:1≤w)(ha:0≤ a)(hb:1≤b)
include hF hp hk ht hw hb ha
local notation "Q"=> F ∘ Clamp g
private lemma moreB {j:σ}(x:View σ)(i:σ)(hv:i≠j): buoy (fun x:Positions σ=> deriv g (x i)) x [j]=0:=by
     let f:= (ContinuousLinearMap.apply ℝ ℝ (1:ℝ)); have hD : ContDiffAt ℝ (↑(1:ℕ)) (deriv g) (x i):=by
         exact f.contDiff.contDiffAt.comp _ (hp.smooth.contDiffAt.fderiv_right (by exact_mod_cast hk))
     let L:View σ→L[ℝ]ℝ:= ContinuousLinearMap.proj i; change fderiv ℝ ((deriv g) ∘ L) x _ = _; rw [fderiv_comp x (hD.differentiableAt (by norm_num)) L.differentiableAt,L.fderiv]; change fderiv ℝ (deriv g) _ (Uniform.bolt j i)= _; rw [show Uniform.bolt j i=0 from (by simp [bolt,hv]),map_zero]
local notation "O!"=> @Lodge.Clamp σ g
lemma tides: FetchD l a (t*(b+b^2)) (F ∘ Clamp g):=by
    have h : Hat 2 w b g:=⟨hp.value,hp.honest,hp.smooth.of_le (Nat.cast_le.mpr hk),fun i j hj=>hp.head i j (hj.trans hk)⟩; have hz:0≤w:= zero_le_one.trans hw; let G:= F ∘ Clamp g
    have hh : Vase F 2 t w:=cs ht (fun i he=>(hF i he).of_le (by exact_mod_cast hk)) hw ha (by omega); have hU:=wax h hh hz hb
    have hv(i:View σ) : ContDiffAt ℝ (↑(2:ℕ)) F (Clamp g i):=hh.smooth _ (peak h hz _)
    have hP(j)(x:View σ): buoy G x [j]= deriv g (x j)*buoy F (Clamp g x) [j]:= congr_fun (budgetC h hv j (by omega)) x
    have hE(j)(x:View σ):|buoy F (Clamp g x) [j]|≤ t:=hh.part _ (peak h hz _) [j] (by simp) (by simp); have hA(x:View σ)(i:σ) : |deriv g (x i)|≤b:=road h [] (by simp)
    have ht':0 ≤ t:= hh.pos_; have hb':0 ≤ b:= zero_le_one.trans hb; let K':= t*(b+b^2); have hs:∀ i:σ,∀ x:View σ, |glance G [i] x|≤ K':=by
         intro i x; rw [← budP G [i] 2 _ (hU.2.contDiffAt) (show [i].length≤2 by simp),hP]; rw [abs_mul]; exact (mul_le_mul (hA x i) (hE i x) (abs_nonneg _) hb').trans ((mul_comm _ _).trans_le (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) ht'))
    refine ⟨⟨hU.2.of_le (by norm_num),hU.1.1 [] (by simp),fun i=>⟨K',hs i⟩⟩,fun i=>hU.2.contDiffAt,mul_nonneg ht' (add_nonneg hb' (sq_nonneg _)),hs,?_⟩
    intro i; obtain ⟨G',hm,he⟩:= ht 1 (by omega)|>.sold
    have he₀ (j:σ):Eve a (l i) (l j) ≤ swipe l a p [i,j]:=by
         let U:= [i,j]; have hi:=curve (W:=Whisk.zone l ∅ U) (x:=l i) (y:=l j) (by simp [U,Whisk.zone]) (by simp [U,Whisk.zone]); refine le_trans ?_ (w_more hi ha p); exact le_mul_of_one_le_left (Real.exp_pos _|>.le) (one_le_pow₀ (by simp))
    let v(j):=b^2*G' [i,j]; let f(j):=if i=j then b*t else 0; refine ⟨fun j=> f j+v j, ?_,?_⟩
    · intro x j; let L(x:View σ):=deriv g (x i); let H:= fun x:View σ=> buoy F x [i]; have hf :ContDiffAt ℝ (↑(1:ℕ)) L x:=by
          let f:= fderiv ℝ g; let hG : ContDiffAt ℝ (↑(1:ℕ)) (deriv g) (x i) := (ContinuousLinearMap.apply ℝ ℝ (1:ℝ)).contDiff.contDiffAt.comp _ (h.smooth.contDiffAt.fderiv_right (by norm_num)); exact hG.comp x (contDiffAt_apply ℝ ℝ i _)
      have hH(x:View σ) : ContDiffAt ℝ (↑(1:ℕ)) H (Clamp g x):= Lis.smooth 2 1 (([i]:List σ).map Uniform.bolt) (hv x) (by simp)
      let H':= H ∘ Clamp g; have hφ(x:View σ) : ContDiffAt ℝ (↑(1:ℕ)) H' x:=(hH x).comp _ (hut h|>.contDiffAt.of_le (by norm_num))
      have hu : glance G [i,j] x= buoy L x [j]*H' x+deriv g (x i)*(deriv g (x j)*buoy F (Clamp g x) [i,j]):=by
          let h': Hat 1 w b g:= ⟨h.value,h.honest,h.smooth.of_le (by norm_num),fun i j hj=>h.head i j (by omega)⟩; rw [←budP G [i,j] 2 _ hU.2.contDiffAt (show [i,j].length≤2 by simp),Lodge.recur h hv x i [j] (by simp)]; change buoy (L*H') x [j]= _; rw [paisley 1 L H' x _ hf (hφ _) (by simp), List.length_cons,twilled,Fintype.sum_bool]; change buoy L x [j]* H' x+ L x*buoy H' x [j]=_; rw [show buoy H' x [j]=_ from congr_fun (budgetC h' hH j (by omega)) x]; congr 2
          exact congr_arg (deriv g (x j)*·) (show buoy H _ [j]=_ from (Lis.takeG 2 (hv x) ([Uniform.bolt j]) (Uniform.bolt i) (by simp)).symm) -- may fail
      have hB: |buoy L x [j]| ≤ b :=road hp _ (by simpa); have hz : |buoy F (Clamp g x) [i,j]| ≤ G' [i,j]:= (le_mul_of_one_le_right (abs_nonneg _) (show 1 ≤ w^(1+1) from one_le_pow₀ hw)).trans (hm _ (by simp) |>.2 _ (peak h ‹0 ≤w› _)); change |glance G [i,j] x|≤ _; rw [hu]; refine (abs_add_le ..).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; by_cases h':i=j; · unfold f; rw [if_pos h']; exact mul_le_mul hB (hE i x) (abs_nonneg _) hb'
        rw [show buoy L _ _= _ from moreB F p k hF hp hk ht hw ha hb x i h',abs_zero,zero_mul]; exact (if_neg h').symm.le
      rw [abs_mul,abs_mul]; exact (mul_le_mul (hA _ _) (mul_le_mul (hA _ _) hz (abs_nonneg _) hb') (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hb').trans_eq (by unfold v; ring)
    · simp_rw [add_mul,sum_add_distrib]; have hξ : (∑ j:σ, v j *Eve a (l i) (l j)) ≤ b^2*t:=by
          unfold v; simp_rw [mul_assoc]; rw [← Finset.mul_sum]; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); refine (sum_le_sum (fun j _=> mul_le_mul_of_nonneg_left (he₀ j) (hm _ (by simp) |>.1))).trans (he i)
      unfold f; simp only [ite_mul,zero_mul,Finset.sum_ite_eq,mem_univ,if_true]; have hp:Eve a (l i) (l i)=1:=by simp [Eve]
      rw [hp,mul_one]; linarith only [hξ]
end
end YM.MSbar.Spruce
