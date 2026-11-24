import YM.OPE.Compatible.Grotto.Tin
/-!
# Stationary frame.T op. groove closure
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> (S! →L[ℝ] S!)
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
lemma closedGroove {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](T:Cuts d μ v b F G)(p:ℕ→ F→L[ℝ] F)(v':F→L[ℝ] F)(hp:Tendsto p atTop (𝓝 v'))(hv:∀ i,Grooved T (p i)):Grooved T v':=by
    have he(w:F):Tendsto (fun i=>p i w) atTop (𝓝 (v' w)):=((show Continuous (fun x:F→L[ℝ] F=> x w) from by fun_prop).continuousAt).tendsto.comp hp; refine ⟨fun i hi w hh=> ?_,fun i hi w hh=>?_,fun w hh=>?_, le_of_tendsto' hp.norm (fun i=>(hv i).cap)⟩
    · exact (T.sealing i hi).mem_of_tendsto (he w) (.of_forall fun j=> (hv j).leaves i hi w hh)
    · apply tendsto_nhds_unique ( (T.Tap i).continuous.continuousAt.tendsto.comp (he w)); apply Tendsto.congr' _ tendsto_const_nhds; exact .of_forall fun j=> ((hv j).tempo i hi w hh).symm
    exact le_of_tendsto' (he w|>.norm) fun j=>(hv j).march w hh
lemma closedAssist (p:ℕ→ L!)(f:L!)(hp:Tendsto p atTop (𝓝 f))(hv:∀ i,Assist T (p i)): Assist T f:=by
     have he(v:S!): Tendsto (fun i=> p i v) atTop (𝓝 (f v)):=((show Continuous (fun x:L! => x v) from by fun_prop).continuousAt).tendsto.comp hp; refine ⟨fun i v h j hj=>?_,fun i=> closedGroove _ (fun j=>stride (p j) i) _ ?_ (fun j=> (hv j).gait i)⟩
     · apply tendsto_nhds_unique ((show Continuous (fun w:S!=>w j) from continuous_apply _).continuousAt.tendsto.comp (he v)); exact Tendsto.congr' (.of_forall fun b=> ((hv b).arum i v h j hj).symm) tendsto_const_nhds
     have h:Continuous (fun t:L!=>stride t i):=by unfold stride; fun_prop
     exact h.continuousAt.tendsto.comp hp
-- generic Station of Wealth
open Drift
variable {A D:Type}[NormedAddCommGroup A]{a w:D→ℝ}
lemma Roof [CompleteSpace A](ha:1 ≤ a)(F:D→ℕ→A)(S:D→ℕ→D)(hs:∀ i j n,F (S i j) n=F i (j+n))(hb:∀ i j,a (S i j)=a i)(ht:0 ≤ x)(hx:x<1)
    (Z: Wealth (fun i:(D×D)×ℕ=>F i.1.1 i.2-F i.1.2 i.2) (fun i=>max (a i.1.1) (a i.1.2)) (fun i=> x^i.2)) [Nonempty D]:∃ X,TameP x a 1 (fun i j=> F i j-X)∧∀ i,Tendsto (F i) atTop (𝓝 X) :=by
          obtain ⟨c,hc,k,H⟩:= Z; have hu(j i n):dist (F i n) (F j n) ≤ c*(max (a i) (a j))^k*x^n:=by rw [dist_eq_norm]; exact H ((i,j),n)
          have hy(i)(n m:ℕ)(h:n≤m): dist (F i n) (F i m) ≤ c*(a i)^k*x^n:=by
               have hh:=hu (S i (m-n)) i n; rw [hs,hb,max_self,Nat.sub_add_cancel h] at hh; exact hh
          have hp(i):CauchySeq (F i):=by
               have ht:=tendsto_pow_atTop_nhds_zero_of_lt_one ht hx|>.const_mul (c*a i^k); simp only [mul_zero] at ht; rw [Metric.cauchySeq_iff']; intro ε he; obtain ⟨N,hN⟩:=eventually_atTop.1 (ht.eventually (gt_mem_nhds he)); exact ⟨N,fun i' hi=>by rw [dist_comm];exact lt_of_le_of_lt (hy i N i' hi) (hN N le_rfl)⟩
          let j:=Classical.arbitrary D; obtain ⟨X,HX⟩:= cauchySeq_tendsto_of_complete (hp j); have hn(i):Tendsto (F i) atTop (𝓝 X):=by
               have hT:= tendsto_pow_atTop_nhds_zero_of_lt_one ht hx|>.const_mul (c*(max (a i) (a j))^k); simp only [mul_zero] at hT
               have hh:= squeeze_zero (fun i=>dist_nonneg) (fun n=> hu j i n) hT -- squeeze implicits
               apply Metric.tendsto_nhds.2; intro ε he; filter_upwards [hh.eventually (gt_mem_nhds (half_pos he)),Metric.tendsto_nhds.1 HX (ε/2) (half_pos he)] with n H hx; exact (dist_triangle .. |>.trans_lt ((add_lt_add (show dist (F i n) (F j n)< _ from H) hx).trans_eq (add_halves ε)))
          refine ⟨X,⟨(fun i=> c*(a i)^k),⟨c,hc,k,fun i=>?_⟩,fun i n=>?_⟩,hn⟩
          · rw [Pi.one_apply,mul_one,Real.norm_of_nonneg (mul_nonneg hc (pow_nonneg (zero_le_one.trans (ha i)) _))]
          change ‖F i n-X‖≤ _; rw [← dist_eq_norm]; exact le_of_tendsto (Tendsto.dist tendsto_const_nhds (hn i)) (Eventually.mono (eventually_ge_atTop n) fun j h=> hy i n j h)
end YM.OPE.Hark
