import YM.OPE.Compatible.Ash.Loop
/-!
# Elementary expansion operations including geometric turn
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Pert.Band Pert.Full
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{s:ℝ}{n i m:ℕ}
variable {M E:Type*}[NormedAddCommGroup M][NormedSpace ℝ M][NormedAddCommGroup E][NormedSpace ℝ E]{f g:ℕ→M}
omit [NormedSpace ℝ M] in
lemma Sake.fuse (hf:Sake U m f)(hg:Sake U m g): Sake U m (f+g):=by
    obtain ⟨C,H,h⟩:=hf; obtain ⟨D,K,k⟩:=hg; refine ⟨C+D,add_nonneg H K,fun i=>?_⟩; rw [Pi.add_apply,add_mul]; exact (norm_add_le ..).trans (add_le_add (h i) (k i))
lemma Sake.glu (L:M→L[ℝ]E)(hf:Sake U m f): Sake U m (L ∘ f):=by
   obtain ⟨C,H,h⟩:=hf; refine ⟨‖L‖*C,by positivity,fun i=>?_⟩; rw [Function.comp_apply,mul_assoc]; exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_mul_of_nonneg_left (h i) (norm_nonneg _))
omit [NormedSpace ℝ M] in
lemma Sake.flop (hf:Sake U m f)(hk:m>0): Tendsto f atTop (𝓝 0):=by -- omit
   obtain ⟨C,H,h⟩:=hf; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero (fun i=> norm_nonneg _) h ?_; simpa only [zero_pow (ne_of_gt hk),mul_zero] using! ((U.h_null.pow m).const_mul C)
lemma van (f:ℕ→M): Tendsto (billX U f (m+1)) atTop (𝓝 (f 0)):=by
   induction m with
   | zero=> rw [show billX U f (0+1)=(fun _=> f 0) from funext fun i=> by simp [billX,coral]]; exact tendsto_const_nhds
   | succ m ih=>
     rw [show billX U f (m+1+1)=billX U f (m+1)+coral U (m+1) (f (m+1)) from funext fun i=>Finset.sum_range_succ ..]; simpa only [zero_pow (by omega : m+1≠0),zero_smul,add_zero] using! (ih.add ((U.h_null.pow (m+1)).smul_const (f (m+1))))
omit [NormedSpace ℝ M] in
lemma Sake.down (hf:Sake U m f)(he:n≤ m) : Sake U n f:=by -- omit
   obtain ⟨C,hC,H⟩:=hf; apply coseal _ hC
   filter_upwards [U.h_null.eventually (ge_mem_nhds zero_lt_one)] with i hi
   exact (H i).trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (U.h_pos _).le hi he) hC)
omit [NormedSpace ℝ M] in
lemma sake_zero (U:Gloam)(m:ℕ):Sake U m (0:ℕ→M):=⟨0,le_rfl,fun i=>by simp⟩ -- omit
lemma cleared_zero (U:Gloam):Cleared U (0:ℕ→M):= fun i _=> ⟨0,by rw [show billX U (0:ℕ→M) i=0 from funext fun j=>by simp [billX,coral], sub_self]; exact sake_zero ..⟩
lemma Cleared.fuse (hf:Cleared U f)(hg:Cleared U g):Cleared U (f+g):=by
   intro i hi; obtain ⟨a,A⟩:=hf i hi; obtain ⟨b,B⟩:=hg i hi; refine ⟨a+b,?_⟩; rw [show billX U (a+b) i=billX U a i+billX U b i from funext fun j=> by simp only [billX,Pi.add_apply,coral,smul_add,Finset.sum_add_distrib],show f+g-(billX U a i+billX U b i)=(f-billX U a i)+(g-billX U b i) from by abel]; exact A.fuse B
lemma Cleared.glu (L:M→L[ℝ]E)(hf:Cleared U f):Cleared U (L ∘ f):=by
   intro i hi; obtain ⟨a,A⟩:=hf i hi; refine ⟨(L ∘ a),?_⟩; rw [show ((L ∘ f)-billX U (L ∘ a) i)=(L ∘ (f-billX U a i)) from funext fun j=>by simp only[billX,Function.comp_apply,Pi.sub_apply,coral,map_sub,map_sum,map_smul]]; exact A.glu L
lemma Cleared.tally {I:Type*}(t:Finset I)(a:I→ℕ→M)(ha:∀ i∈t,Cleared U (a i)):Cleared U (∑ i∈t, a i):=by
   induction t using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact cleared_zero _
   | @insert i t hh ih=> rw [Finset.sum_insert hh]; exact (ha i (Finset.mem_insert_self ..)).fuse (ih (fun _ hp=>ha _ (Finset.mem_insert_of_mem hp)))
lemma Cleared.always {x:M}:Cleared U (fun _=>x):=by
   intro j hj; obtain ⟨i,hi⟩:=Nat.exists_eq_add_one.mpr hj; subst j; refine ⟨Pi.single 0 x,?_⟩; rw [show (billX U (Pi.single 0 x) (i+1))=(fun _=>x) from funext fun j=>?_ ,sub_self]; exact sake_zero ..
   unfold billX; rw [Finset.sum_eq_single 0]; rw [Pi.single_eq_same]; simp [coral]
   · intro b _ hh; simp [Pi.single_eq_of_ne hh,coral]
   simp
lemma Cleared.cost (h:Cleared U f):Sake U 0 f:=by
   obtain ⟨a,h⟩:=h 1 zero_lt_one; rw [show f=(f-billX U a 1)+billX U a 1 from by abel]; apply Sake.fuse (h.down (by omega)); exact ⟨‖a 0‖,by positivity,fun i=>by simp [billX,coral]⟩
-- solve geometric differences with power prefactor
variable [CompleteSpace M]
lemma gap (hd:n>0)(hc: Cleared U g)(x:M)(hq:Tendsto f atTop (𝓝 x))(he:∀ i,f i-f (i+1)=U.h i^n • g i):Cleared U (fun i=>(U.h i^n)⁻¹ • (f i-x)):=by
   intro k hk; obtain ⟨a,hp⟩:= hc k hk
   let r(j:ℕ):=1-(U.q'^ (n+j))⁻¹; have hr(j):0<r j:= by unfold r; apply sub_pos.mpr; exact (inv_lt_one_of_one_lt₀ (one_lt_pow₀ U.qsub (by omega)))
   let b(j:ℕ):=(r j)⁻¹ • a j
   let G(i):= (U.h i)^n • billX U b k i
   have hy(i): G i-G (i+1)=U.h i^n • billX U a k i:=by
      unfold G billX; rw [Finset.smul_sum,Finset.smul_sum,Finset.smul_sum,← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j hj; simp only[coral,b,smul_smul,U.h_succ,div_pow]; rw [←sub_smul]; congr 1; let R:=r j; have H:U.q'^ (n+j) ≠ 0:=by have h:=U.qsub; positivity
      have hi:=U.h_pos i; have hR:=hr j; calc _ = (U.h i^n*U.h i^j)*(r j*R⁻¹) := by unfold r; rw [pow_add, mul_inv]; unfold R;unfold r; rw [pow_add,mul_inv]; ring
                                               _ = _:=by rw [show r j*R⁻¹=1 from mul_inv_cancel₀ (hr j).ne',mul_one]
   obtain ⟨C,hC,H⟩:=hp; let p(i):=f i-x-G i
   have eg:Sake U (k+n) (fun i=>p i-U.q'^0 • p (i+1)):=by
       refine ⟨C,hC,fun i=>?_⟩; have hx:p i-p (i+1) = U.h i^n • (g i-billX U a k i):=by rw [show p i-p (i+1)=(f i-f (i+1))-(G i-G (i+1)) from by unfold p;abel, he, hy, smul_sub]
       simp only [pow_zero,one_smul,hx,norm_smul,Real.norm_of_nonneg (pow_nonneg (U.h_pos _).le _),pow_add]; exact (mul_le_mul_of_nonneg_left (H i) (pow_nonneg (U.h_pos _).le _)).trans (le_of_eq (by ring))
   obtain ⟨v,hv⟩:=fluted eg (by omega); have hv':coral U 0 v=(fun _=>v):=by funext i;simp [coral]
   have hp:Tendsto G atTop (𝓝 0):=by obtain ⟨j,hq⟩:=Nat.exists_eq_add_one.mpr hk; unfold G; rw [hq]; simpa only [zero_pow (by omega:n≠0),zero_smul] using! (U.h_null.pow n|>.smul (van (U:=U) b (m:=j)))
   have hh:Tendsto p atTop (𝓝 0):=by simpa using! ((hq.sub (tendsto_const_nhds (x:=x))).sub hp)
   have hv0:v=0:=by
      have hx:=hv.flop (by omega); rw [hv'] at hx; have H:=tendsto_nhds_unique hx (hh.sub (g:=fun _=>v) tendsto_const_nhds); simpa using H.symm
   rw [hv0,show coral U 0 0=(0:ℕ→M) from by funext i;simp [coral],sub_zero] at hv
   obtain ⟨B,hB,h⟩:=hv; refine ⟨b,B,hB,fun i=>?_⟩; have hi:=U.h_pos i
   change ‖(U.h i^n)⁻¹ • (f i-x)-billX U b k i‖≤ _; rw [show (U.h i^n)⁻¹ • (f i-x)-billX U b k i=(U.h i^n)⁻¹ • p i from by unfold p G; rw [smul_sub _ (f i-x),smul_smul,inv_mul_cancel₀ (by positivity),one_smul],norm_smul,Real.norm_of_nonneg (by positivity)]
   exact (mul_le_mul_of_nonneg_left (h _) (inv_nonneg.mpr (pow_nonneg hi.le _))).trans (le_of_eq (by rw [pow_add]; field_simp))
end YM.OPE.Balsam
