import YM.MSbar.Sat.Latch
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{c f n:Side}{S:StepData c f} {U W:Config G f}{V:Config G c}{R:Rep G f}{σ C T a v y δ w D b u t:ℝ}
open Finset YM.MSbar.Bulk SectorNext.Vacuum Precision Tree Pressure Pressure.Stores Push.Uniform
-- true evaluator need know *next* op; S.kernel uniform.View alignment irrelevant, β-clock.
structure Quasi (g:Config G f→ℝ)(C:ℝ) : Prop where
    cost : 0≤C
    positive (U : Config G f):0≤g U
    shift (p:Edge (Site f))(U:Config G f)(V: G.El) : g (update U p V) ≤ Real.exp (C*G.chord (V*(U p)⁻¹))*g U
-- dual orientation apply to many changed links. 
variable {g:Config G f→ℝ}(h:Quasi g C)(a: Finset (Edge (Site f)))
include h
lemma Quasi.assemble {B:ℝ} (he:∀ i,i∉ a→ U i=W i)(hd:∀ i∈a, G.chord (U i *(W i)⁻¹) ≤ B) : g U ≤ Real.exp (C*B*a.card)*g W:=by
    induction a using Finset.induction generalizing U with
    | empty=> rw [show U=W from funext fun i=> he i (by simp)]; simp
    | insert i s hi ih=>
       let V:=update U i (W i); have hp : update V i (U i)=U:=by ext1 j; by_cases he:j=i; subst j; simp; simp [V, update_of_ne he]
       have hz:= h.shift i V (U i); rw [hp] at hz; have hv : g V≤ Real.exp (C* B*s.card)*g W:=ih (U:=V) (fun j hj=> by by_cases ht:j=i; subst j; simp [V]; simp_rw [V, update_of_ne ht]; exact he j (by simp [ht,hj])) (fun j hj=> by rw [show V j=U j from update_of_ne (ne_of_mem_of_not_mem hj hi) _ _]; exact hd j (mem_insert_of_mem hj))
       have hx : V i=W i:= update_self ..; apply hz.trans; rw [hx]; apply le_trans (mul_le_mul ?_ hv (h.positive V) (by positivity : 0≤Real.exp (C*B))) _
       · exact Real.exp_monotone (mul_le_mul_of_nonneg_left (hd _ (mem_insert_self ..)) h.cost)
       apply le_of_eq; rw [← mul_assoc, ← Real.exp_add,card_insert_of_notMem hi]; push_cast; ring
omit h
lemma noisy_push (i:Side){A: StepData f i} {Q: Config G i→ℝ} {β:ℝ}(he:A.patch.Branches A.kernel G)(hc:0 ≤ β)(hh:Integrable Q (prior G i))(hr:∀ U,0≤Q U): Quasi (A.push β Q) (β*A.kernel.penalty*2):=by
   have hb:=A.kernel.penalty_pos; let b:= β*A.kernel.penalty; refine ⟨by positivity,fun U=> integral_nonneg (fun V=> mul_nonneg (A.density_positive ..) (hr _)),fun p U V=>?_⟩
   let Z:=update U p V; let d:= G.chord (V*(U p)⁻¹); let e:=b*2*d
   have hp(X:Config G f) : A.noise β X Z ≤ Real.exp e*A.noise β X U:=by
      let s (T:G.El) := A.penaltyWeight β (T*(X p)⁻¹); let r:ℝ:= (A.penaltyZ β G)⁻¹
      have hx : s V≤ Real.exp e*s (U p):=by
          unfold s StepData.penaltyWeight; rw [← Real.exp_add]; apply Real.exp_monotone; have h:=price_compare (V*(X p)⁻¹) (U p*(X p)⁻¹); rw [show V*(X p)⁻¹*(U p*(X p)⁻¹)⁻¹=V*(U p)⁻¹ by group] at h
          have hz:= mul_le_mul_of_nonneg_left (abs_le.mp h|>.1) (mul_nonneg hc hb.le); unfold e b d; linarith
      let g W j:= r*A.penaltyWeight β (W*(X j)⁻¹); let B:=∏ i∈univ.erase p, g (U i) i
      have he(T:Config G f)(hT:∀ j,j≠p→ T j=U j): A.noise β X T=(r*s (T p))*B:=by
          unfold StepData.noise; rw [← mul_prod_erase _ _ (mem_univ p)]; apply congr_arg; unfold B; exact prod_congr rfl fun j hj=> by rw [hT j (ne_of_mem_erase hj)]
      rw [he Z (fun j hj=> update_of_ne hj V U),he U (fun _ _=>rfl), show Z p = V from update_self ..,← mul_assoc]; have ht:0≤r:= (inv_pos.mpr (A.penaltyZ_pos _)).le; exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hx ht).trans_eq (mul_left_comm ..)) (Finset.prod_nonneg fun i _=> mul_nonneg ht (Real.exp_pos _|>.le))
   let K(X):= A.push β Q X; have ht:= A.isKernel he β; have hz(W:Config G i):A.density β W Z ≤ Real.exp e*A.density β W U:=by
      unfold StepData.density; rw [Finset.mul_sum]; exact sum_le_sum fun i _=> (mul_le_mul_of_nonneg_left (hp _) (A.likelihood_pos ..)).trans_eq (mul_left_comm ..)
   unfold StepData.push; rw [← integral_const_mul]; refine integral_mono (StepData.push_slice ht Z Q hh) ((StepData.push_slice ht U Q hh).const_mul _) (fun W=>?_); exact (mul_le_mul_of_nonneg_right (hz W) (hr W)).trans_eq (mul_assoc ..)
end YM.MSbar.Heath
