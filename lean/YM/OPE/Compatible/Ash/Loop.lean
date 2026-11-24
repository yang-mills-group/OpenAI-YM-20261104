import YM.OPE.Compatible.Ash.Leaf
/-! # Solve dilation. No logs in macro evaluation. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{z:(i:ℕ)→Site (U.M i)}{s:ℝ}{n i m:ℕ}
variable {M:Type*}[NormedAddCommGroup M][NormedSpace ℝ M]
def Sake {E:Type*}[Norm E](U:Gloam)(m:ℕ)(f:ℕ→E):Prop := ∃ c≥0,∀ i,‖f i‖ ≤ c*(U.h i)^m
def coral (U:Gloam)(n:ℕ)(x:M):ℕ→M:=fun i=> U.h i^n • x
def billX (U:Gloam)(f:ℕ→M)(n:ℕ):ℕ→M:=fun i=>∑ j∈Finset.range n,coral U j (f j) i
def Cleared (U:Gloam)(p:ℕ→M):Prop:=∀ m>0,∃ f, Sake U m (p-billX U f m)
variable {E:Type*}
omit [NormedSpace ℝ M] in
lemma coseal {f:ℕ→ M}(h:∀ᶠ i in atTop, ‖f i‖ ≤ s*U.h i^m)(hs:0≤s):Sake U m f:=by
   obtain ⟨b,h⟩:=eventually_atTop.mp h; let c(i):=‖f i‖/(U.h i)^m; have hh(i):0≤c i:= by have h:=U.h_pos i; unfold c; positivity
   let A:=∑ i∈Finset.range b,c i; have he:0 ≤ A:=Finset.sum_nonneg (fun i _=> hh i); refine ⟨A+s,add_nonneg he hs,fun i=>?_⟩; have hv:=U.h_pos i; rw [← div_le_iff₀ (pow_pos hv _)]; change c i ≤ _; by_cases ht:b ≤ i
   · exact (div_le_iff₀ (pow_pos hv _)).mpr (h i ht) |>.trans (le_add_of_nonneg_left he)
   exact (Finset.single_le_sum (f:=c) (fun i _=> hh i) (Finset.mem_range.mpr (not_le.mp ht))).trans (le_add_of_nonneg_right hs)
def snowC (U:Gloam)(n:ℕ):ℕ→ℝ
 | 0=>1
 | i+1=>snowC U n i*(1-U.q'^i/U.q'^n)
lemma ice_char (x:M): glide U.q' m (coral U n x) i=coral U n (snowC U n m • x) i:=by
   induction m generalizing i with
   | zero=> simp only [glide, crimp,coral,snowC,one_smul]
   | succ m ih=>
     change glide U.q' m _ _ - U.q'^m • glide U.q' m _ _=_; rw [ih,ih (i:=i+1)]
     dsimp only [coral,snowC]; rw [U.h_succ]; simp_rw [smul_smul]; rw [← sub_smul]; congr 1; rw [div_pow]; ring
lemma snowC_pos (U:Gloam)(hh:m≤n):0<snowC U n m:=by
   induction m with
   | zero=> exact zero_lt_one
   | succ m ih=>
     rw [snowC]; have ht:=U.qsub; refine mul_pos (ih (by omega)) (sub_pos.mpr ((div_lt_iff₀ (pow_pos (by linarith only [ht]) _)).mpr ?_)); rw [one_mul]; exact pow_lt_pow_right₀ ht hh
variable [CompleteSpace M]{p:ℕ→M}{y:M}
lemma fluted (hp:Sake U m (fun i=> p i-U.q'^n • p (i+1)))(hh:n<m):∃ a:M, Sake U m (p-coral U n a):=by
   let f(i):=(U.h i^n)⁻¹ • p i; obtain ⟨C,hC,L⟩:=hp; let r:=U.q'^n/U.q'^m; have hz:=U.qsub; have hZ:0<U.q':=zero_lt_one.trans hz; let A:=C*(U.h 0^m/U.h 0^n)
   have hr:r<1:=(div_lt_one (pow_pos hZ _)).mpr (pow_lt_pow_right₀ hz hh); have hf(i): A*r^i=C*U.h i^m/U.h i^n:=by
      change _=C*((U.nb i)⁻¹)^m/(_)^n; change _=C*((U.nb i)⁻¹)^m/((U.nb i)⁻¹)^n; rw [U.n_eq]; unfold A r; change C*((U.nb 0)⁻¹^m/(U.nb 0)⁻¹^n)*_= _; rw [div_pow]; simp_rw [mul_inv,mul_pow,show ∀ j:ℕ,(U.q'^i)⁻¹^j=(U.q'^j)⁻¹^i from fun j=>by rw [inv_pow (U.q'^j),inv_pow, ←pow_mul,←pow_mul,mul_comm i]]; simp only [inv_pow]; unfold Gloam.nb sizeR; field_simp
   have H(i): dist (f i) (f (i+1))≤ A*r^i:=by
      have ht:=U.h_pos i; rw [hf,dist_eq_norm, show f i-f (i+1)=(U.h i^n)⁻¹ • (p i-U.q'^n • p (i+1)) from by unfold f; rw [U.h_succ,div_pow,inv_div,smul_sub,smul_smul]; rw [inv_mul_eq_div]]
      rw [norm_smul,Real.norm_of_nonneg (by positivity)]; have h := mul_le_mul_of_nonneg_left (L i) (show 0≤(U.h i^n)⁻¹ from by positivity); rw [← inv_mul_eq_div]; exact h
   obtain ⟨a,ha⟩:=cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric _ _ hr H)
   refine ⟨a,C/(1-r),by positivity,fun i=>?_⟩; have hx:=dist_le_of_le_geometric_of_tendsto r A hr H ha i; have he:=U.h_pos i; rw [hf,dist_eq_norm] at hx; have hh : p i=U.h i^n • f i:=by dsimp only[f]; rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
   rw [Pi.sub_apply,coral, hh,←smul_sub,norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left hx (by positivity)).trans (le_of_eq (by field_simp))
lemma censed (hw:m≤ n)(h:Sake U n (glide U.q' m p)):∃ f:ℕ→M,Sake U n (p-billX U f m):=by
   induction m generalizing p with
   | zero=> exact ⟨0,by rw [show billX U (0:ℕ→M) 0=0 from funext fun i=>by simp [billX],sub_zero]; exact h⟩
   | succ m ih=>
     obtain ⟨b,h⟩:=fluted h hw -- change
     let x: M:= (snowC U m m)⁻¹ • b
     let q:= coral U m x
     have he : glide U.q' m (p-q)= glide U.q' m p-coral U m b:= by
        funext i; rw [sub_eq_add_neg, glide_add,glide_neg,show glide U.q' m q i=_ from ice_char (i:=i) x]; rw [show snowC U m m • x=b from by rw [show x=_ from rfl,smul_smul,mul_inv_cancel₀ (snowC_pos U (le_refl m)).ne',one_smul]];exact (sub_eq_add_neg ..).symm
     rw [←he] at h; obtain ⟨f,H⟩:=ih (by omega) h; refine ⟨Function.update f m x,?_⟩
     rw [show (p-billX U (Function.update f m x) (m+1))=(p-q)-billX U f m from funext fun i=>?_ ]
     focus exact H
     simp only [Pi.sub_apply,billX,Finset.sum_range_succ,Function.update_self]; rw [add_comm _ (coral ..),←sub_sub]; congr 1; exact Finset.sum_congr rfl (fun j hj=>by rw [Function.update_of_ne (Nat.ne_of_lt (Finset.mem_range.mp hj))])
lemma clear_jointX (hh:Drone U z)(hv:z 0≠0)(D:List Axis)(a:Cover): Cleared U (fun i=>joint (U.h i) D (z i+wrap _ a)):=by -- section
    intro j hj; obtain ⟨C,hC,H⟩:=macro_tax hh hv D a j hj; exact censed (le_refl _) (coseal H hC)
end YM.OPE.Balsam
