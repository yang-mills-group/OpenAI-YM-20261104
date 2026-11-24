import YM.FormalBulk08.Sable.Stay

/-! Newton estimator in true polynomial norms. Far pays
one copy of the rescaled joint max! -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Grail Work.F03 Work.F05 Work.F08
-- limited names
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{I J:Type}[Fintype I][Fintype J] {u m n r d:ℕ}{η σ C:ℝ}{L:Side}
lemma hat_pulp (p:Grades I):∃ C:ℝ,0≤C ∧ ∀ x:Wand I, |Chapel.hat p x| ≤ C*(1+(size x:ℝ))^upper p:= by
   have hh (i:I)(k:ℕ): ∃ A:ℝ,0≤A ∧ ∀ x:Wand I,|Ring.choose (x i:ℝ) k|≤ A*(1+(size x:ℝ))^k:= by
       induction k with
       | zero=> exact ⟨1,zero_le_one,fun x=>by simp⟩
       | succ k h=>
         obtain ⟨A,hA,H⟩:=h
         refine ⟨|(k+1:ℝ)⁻¹| *A*(1+k),by positivity,fun w=>?_⟩
         rw [Chapel.rise_hat _ k,abs_mul,abs_mul]
         have hv: |(w i:ℝ)|≤ (size w:ℝ):= by rw [←Int.cast_abs,←Int.natCast_natAbs]; exact_mod_cast (Finset.single_le_sum (f:=fun i:I=>(w i).natAbs) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i))
         have ht: |(w i:ℝ)-(k:ℝ)| ≤ (1+k)*(1+(size w:ℝ)):= by apply (abs_sub (w i:ℝ) _).trans; rw [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) k)];nlinarith only [hv,mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (Nat.cast_nonneg (size w))]
         exact (mul_le_mul_of_nonneg_left (mul_le_mul (H w) ht (abs_nonneg _) (by positivity)) (abs_nonneg _)).trans_eq (by rw [pow_succ];ring)
   choose Q hQ HQ using hh; refine ⟨∏ i,Q i (p i),Finset.prod_nonneg (fun _ _=> hQ ..),fun w=>?_⟩;unfold Chapel.hat; rw [Finset.abs_prod]; apply (Finset.prod_le_prod (fun _ _=> abs_nonneg _) (fun i _=>HQ i (p i) w)).trans_eq; rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum];rfl
variable (hs:0<η) (hc:0≤C)
include hs hc
-- plain far price with native strips for each leg.
lemma unhatched (u:ℕ)(S:Cross L I J)(k:ℕ)(H:gauss S η C k)(x:Biglot I)(t:chain I m)(w:cloud m)(a:J):
    Knoxville (grain (fame _) 1) u (piz L x a) (candor S x.1 t w) (Real.exp u * ((1+m*((size w:ℝ)/(L.val:ℝ)+8))^u) * ((sack u η*(Fintype.card J*(C*(L.val:ℝ)⁻¹)))^m)):= by
   let f i:=snake x.1 t w i; let v:=piz L x a; let D:=grain (fame J) 1; let Y i:=Bank.scroll L I (f i); let l:ℝ:=L.val; have hl:0<l:=by unfold l; positivity
   have he : S.strip η (C*l⁻¹):= by have ht:= H [] (Nat.zero_le k);rw [advanceC,List.length_nil,add_zero,pow_one] at ht;exact ht
   have hz:=sack_pos u hs; let F (i:Fin m)(v:Biglot J):=(baili _ _ u 1).capsule (Y i) v*‖merit S (f i) v‖ₑ; let W:=sack u η*(Fintype.card J*(C*l⁻¹)); have hW:0≤W:=by unfold W; positivity
   let a' i:=piz L (f i) a
   let k':ℝ:=size w;have hk: 0≤k':=Nat.cast_nonneg _
   let B:= Real.exp u * ((1+m*(k'/l+8))^u); have hB:0≤ B:=by unfold B; positivity
   have hh (z: chain (Biglot J) m): penon D v u (candor S x.1 t w) z≤ ENNReal.ofReal B* ∏ i:Fin m,F i (z i):= by
       have he' := (baili J J u 1).carried (Fin.cons v a' : chain (Biglot J) (m+1)) (Fin.cons v z); rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_zero] at he'; simp only [baili, ENNReal.ofReal_one,one_mul, Fin.cons_succ,sub_self, show size (0:Cover)=0 by simp [Laurent.size],plum_self,Nat.cast_zero,mul_zero,Gorge.shine,Real.exp_zero] at he' -- unk size
       let r:= herb (fame _) v a'; have hx : (r:ℝ)≤ m*(k'/l+8):= by
           refine (by exact_mod_cast throne (fame J) v a': (r:ℝ)≤ (↑(∑ i:Fin m, (fame _).d (a' i) v):ℝ)).trans ?_; rw [Nat.cast_sum]; have hm :(m:ℝ)*(k'/l+8)=∑ _i:Fin m,(k'/l+8):= by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
           rw [hm]; apply Finset.sum_le_sum;intro i _; let d:ℕ:= (fame _).d (a' i) v
           have hP : ↑(capD (f i).1 x.1) ≤ k':= by dsimp only [f,snake,capD]; rw [add_sub_cancel_left]; exact Nat.cast_le.mpr (atom_size w i)
           have he : d*l ≤ k'+8*l:= (parent_less (L:=L) (f i) x).trans (add_le_add_left hP _); exact ((le_div_iff₀ hl).mpr he).trans_eq (by rw [add_div,mul_div_cancel_right₀ _ hl.ne'])
       have hz : Gorge.shine (u:ℝ) (herb D v a') ≤ ENNReal.ofReal B:= by unfold D herb Gorge.shine;rw [plume];apply ENNReal.ofReal_le_ofReal; refine (grain_up ..).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le); unfold gauge;simp only [NNReal.coe_one,one_mul]; exact pow_le_pow_left₀ (by positivity) (add_le_add_right hx _) _
       let V i:= (baili _ _ u 1).capsule (Y i) (z i)
       have hV : Gorge.shine u (herb D v z)≤ ENNReal.ofReal B * ∏ i: Fin m, V i:= by
          refine le_trans ?_ (mul_le_mul_left hz _); exact he'
       unfold penon; refine (mul_le_mul_left hV _).trans_eq ?_
       have ht (T:Finset (Fin m)): ‖∏ i∈T,merit S (f i) (z i)‖ₑ= ∏ i∈T,‖merit S (f i) (z i)‖ₑ:= by induction T using Finset.induction_on with
                                                                                                                                     | empty=>simp
                                                                                                                                     | insert i T hv ih=>rw [Finset.prod_insert hv,Finset.prod_insert hv,enorm_mul, ih]
       unfold F; change _ * ‖∏ i:Fin m,merit S (f i) (z i)‖ₑ=_;rw [ht,Finset.prod_mul_distrib, mul_assoc]
   refine ⟨mul_nonneg hB (pow_nonneg hW _),?_⟩; rw [ENNReal.ofReal_mul hB]; refine (ENNReal.tsum_le_tsum hh).trans ?_; rw [ENNReal.tsum_mul_left, eun_tsum,ENNReal.ofReal_pow hW]
   apply mul_le_mul_right; exact (Finset.prod_le_prod' (s:=Finset.univ) (f:=fun i=>∑' a,F i a) (g:=fun _=> ENNReal.ofReal W) fun i _=> (sea_counts _ he hs (mul_nonneg hc (inv_nonneg.mpr hl.le)) le_rfl).rows (Y i)).trans (by simp)
lemma gala_local (u:ℕ)(S:Cross L I J)(k:ℕ)(H:gauss S η C k)(he:Odd L.val)(x:Biglot I)(t:chain I m)(w:cloud m)(a:J)(hw:size w≤L.val)(j: List (Fin m× Axis))(hp:j.length≤k) : Knoxville (grain (fame _) 1) u (piz L x a) (gang (candor S x.1 t) j w)
   (sack u η * ((Real.exp (η*9)*(Fintype.card J*C))^m) * (L.val:ℝ)⁻¹^(m+j.length)):= by
    have ht:= glutton hs.le hc S k H he x t L.val (0,a) j hp w hw
    apply (sack_to u hs (ε:=1) le_rfl ht).mono; unfold gold; have hl: 0 < (L.val:ℝ):=by positivity
    rw [div_self hl.ne',show (1:ℝ)+8=9 by norm_num]; apply le_of_eq; rw [pow_add]; ring
end YM.FormalBulk08.Sable
