import YM.MSbar.Rolling.Tapes
import YM.Work.G05.Taylor
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Rolling
open Function Filter MeasureTheory Set Cacao Tensor
open scoped Topology Classical BigOperators ContDiff
variable {E F : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{f:E→F}{n:ℕ}
open Metric Work.G05
local notation "J"=> iteratedFDeriv ℝ
local notation "k!"=> n+1
lemma tips (hf:ContDiffAt ℝ (↑(n+1:ℕ)) f 0)(p:∀ m,m≤ n → J m f 0=0) : ∃ r C:ℝ,0<r ∧ 0≤C ∧ ∀ x:E,x∈closedBall 0 r→‖f x‖ ≤ C*‖x‖^(n+1):=by
    let s:=n+1; let C:= ‖J s f 0‖+1
    obtain ⟨r,hr,h₀⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp ((hf.eventually (by simp)).and ((hf.continuousAt_iteratedFDeriv (k:=s) le_rfl).norm.tendsto.eventually (eventually_lt_nhds (show _<C by unfold C; linarith))))
    let B(t:ℝ):=closedBall (0:E) t
    have H C x (h:C≤r) (he:x∈B C) :=h₀ (closedBall_subset_closedBall h he)
    refine ⟨r,C,hr,(by unfold C; positivity),fun x hx=>?_⟩
    let K:=‖x‖; have hk:K ≤ r:= by simpa using hx
    have he(m)(hm:m≤s) (y)(hy:y∈ B K) : ‖J m f y‖ ≤ C*K^(s-m):=by
       induction hm using Nat.decreasingInduction generalizing y with
       | self=> rw [Nat.sub_self,pow_zero,mul_one]; exact (H _ _ hk hy).2.le
       | of_succ m h ih=>
          let F:= J m f; have hv(z:E)(he:z∈B K): DifferentiableAt ℝ F z := (show ContDiffAt ℝ (↑(n+1:ℕ)) f z from (H _ _ hk he).1).differentiableAt_iteratedFDeriv (by exact_mod_cast h)
          have hx(z:E)(he:z∈B K) : ‖fderiv ℝ F z‖ ≤ C*K^(s-(m+1)):=by
              have ht:= ih z he; rw [iteratedFDeriv_succ_eq_comp_left,comp_apply,LinearIsometryEquiv.norm_map] at ht; exact ht
          have hp:= (convex_closedBall (0:E) K).norm_image_sub_le_of_norm_fderiv_le (f:=F) hv hx (mem_closedBall_self (norm_nonneg _)) hy; rw [show F 0=0 from p m (by omega),sub_zero,sub_zero] at hp
          have hF:‖y‖ ≤ K:= by simpa only [B, mem_closedBall,dist_zero_right] using hy
          refine hp.trans ((mul_le_mul_of_nonneg_left hF (by unfold C K; positivity)).trans_eq ?_); rw [show s-m=s-(m+1)+1 by omega,pow_succ,mul_assoc]
    refine (norm_iteratedFDeriv_zero (𝕜:=ℝ)).symm.trans_le ?_; simpa only [Nat.sub_zero] using he 0 (by omega) x (mem_closedBall.mpr (by rw [dist_zero_right]))
lemma taylorQuote (hf:ContDiffAt ℝ (↑(n+1:ℕ)) f 0) : ∃ r C:ℝ,0<r∧0≤C∧∀ x:E,x∈ closedBall 0 r→ ‖f x - blockTaylor n f x‖ ≤ C *‖x‖^(n+1):=by
    have ht := (blockTaylor_contDiff n f (↑(n+1:ℕ))).contDiffAt (x:=0)
    have hv:= hf.of_le (m:=↑n) (by exact_mod_cast Nat.le_succ _); let g:=blockTaylor n f; have hG : ContDiffAt ℝ (↑(n+1:ℕ)) (f-g) 0:=hf.sub ht -- Pi
    exact tips hG (fun m hm=>by change J m (f-g) 0=0; rw [iteratedFDeriv_sub_apply,show J m g 0=J m f 0 from blockTaylor_jets hv m hm,sub_self]; exact hv.of_le (Nat.cast_le.mpr hm); exact (blockTaylor_contDiff n f ..).contDiffAt)
private noncomputable def bud {σ : Type}[Fintype σ](i:σ): View σ:= Pi.single i 1
private lemma scene {σ:Type}[Fintype σ](x:View σ) : (∑ i,x i • bud i)=x:=by
    ext i; rw [Finset.sum_apply, Finset.sum_eq_single i]; simp [bud]; exact fun j _ hx=> by simp [bud,hx,hx.symm]
    simp
variable {σ:Type}[Fintype σ]
open MvPolynomial
noncomputable def potter (f: View σ→ℝ)(n:ℕ): Pot σ:=∑ v:Fin n→σ,(∏ i, MvPolynomial.X (v i)) * MvPolynomial.C (Tensor.coeff f n 0 (fun j=>bud (v j)))
lemma pots (f:View σ→ℝ)(x:View σ)(n:ℕ): eval x (potter f n)=Tensor.diagonal (Tensor.coeff f n 0) x:=by
    unfold potter Tensor.diagonal;let k:=Tensor.coeff f n 0; let g(i:Fin n)(j:σ):= x j • bud j
    simp only [map_sum,map_mul,map_prod,eval_X,eval_C]; change ∑ _,_= k _; rw [show k (fun _=>x)= _ from congr_arg k (funext (fun i=>show x=∑ j,g i j from (scene x).symm)), ContinuousMultilinearMap.map_sum k g]; apply Finset.sum_congr rfl; intro i _; unfold g; rw [k.map_smul_univ (fun j=>x (i j)) (fun j=>bud (i j))]; rfl
lemma potsD (f:View σ→ℝ)(n:ℕ): (potter f n).totalDegree ≤ n:=by
    refine totalDegree_finsetSum_le fun i _=> (totalDegree_mul _ _).trans ?_; rw [totalDegree_C,Nat.add_zero]; simpa only [totalDegree_X,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul, mul_one] using totalDegree_finsetProd Finset.univ (fun j=> MvPolynomial.X (R:=ℝ) (i j)) -- syntax.fintype
open Price Bakery Portal
noncomputable def singularity (f:View σ→ℝ)(b:ℕ): PowerSeries (Pot σ):= PowerSeries.mk (fun i=>potter f (i+b))
lemma drives (f:View σ→ℝ)(n:ℕ)(x:ℝ)(v:View σ):taste n (picture v (singularity f 0)) x= blockTaylor n f (x•v):=by
    unfold taste picture singularity blockTaylor; rw [Finset.sum_apply]; apply Finset.sum_congr rfl; intro i hi; rw [Tensor.homogeneous,PowerSeries.coeff_map,PowerSeries.coeff_mk,pots];rfl
-- ∃ gives logs with integer N even for vector moving cost. Specialize divided formulas using low jets
variable {V:Type*}{X:ℝ→V→Prop}
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
lemma prop (f:View σ→ℝ)(x:ℝ→V→View σ)(n:ℕ)(h: Price X 0 x)(ht :ContDiffAt ℝ (↑(n+1:ℕ)) f 0):Price X (n+1) (fun t y=> f (t•x t y) - taste n (picture (x t y) (singularity f 0)) t):=by
    obtain ⟨r,C,hR,hC,hb⟩:=taylorQuote ht
    have hp:Price X 1 (fun t y=> t•x t y):=(xunit X).val h
    have hv:= hp.reach r hR (by omega); obtain ⟨N,h⟩:=hp
    apply fixed (N*(n+1)) C; filter_upwards [width,h,hv] with t ⟨hc,hx,hd⟩ he hP y hy; let z:= t• x t y
    have he': z∈closedBall 0 r:= mem_closedBall.mpr (show dist z 0≤ _ from (dist_zero_right _).trans_le (hP y hy|>.le))
    rw [drives]; exact (hb z he').trans (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) (he y hy) _).trans_eq (by ring)) hC)
end YM.MSbar.Rolling
