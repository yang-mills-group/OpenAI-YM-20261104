import YM.LocalLTE.Units.Ray
/-! Extend polynomial truncation value on asymmetric Dart. Accuracy expression numerator candle. Does not differentiate original integral or tail on contour. Buys later heights. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Cabana
open Function Filter Set Metric Tensor PhysicalNext.Repeat ConnectedActivityE6.Blaze Brush
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {i j d m:ℕ} {x c:E} {r s R a M L:ℝ} {f:E → ℝ}
lemma Darts (p:Dart c r x): segment ℝ 0 x ⊆ setOf (Dart c r):=by
  rintro y ⟨α,b,hα,hb,h,rfl⟩; obtain ⟨w,⟨hw,hW⟩,he⟩:=p
  simp only [smul_zero,zero_add]; refine ⟨b*w,⟨mul_nonneg hb hw,mul_le_one₀ (by linarith) hw hW⟩,?_⟩; rw [mul_assoc, mul_smul,← smul_sub,norm_smul,Real.norm_of_nonneg hb]; exact mul_le_mul_of_nonneg_left he hb
lemma means (hr:0 < r) (ha:‖c‖+r ≤ a) (hM:0 ≤ M) (hp:∀ x,Dart c r x → ContDiffAt ℝ i f x) (he:∀ x,Dart c r x  →  ‖iteratedFDeriv ℝ i f x‖  ≤  M) (x:E) (hx:Dart c r x) : ‖f x-Cabana.actual (fun j:Fin i=>coeff f j.val 0) x‖ ≤  M*a^i:=by
  have hX : ‖x‖ ≤ a:=by
    obtain ⟨z,hz,h⟩:=hx
    apply le_trans (by nth_rw 1 [← sub_add_cancel x (z • c)]; exact norm_add_le .. : ‖x‖  ≤  ‖x-z • c‖+‖z • c‖) -- edit
    rw [norm_smul,Real.norm_of_nonneg hz.1]; exact le_trans (add_le_add (h.trans (mul_le_of_le_one_left hr.le hz.2)) (mul_le_of_le_one_left (norm_nonneg _) hz.2)) ((add_comm ..).trans_le ha)
  have hA:0 ≤ a:=(norm_nonneg _).trans hX
  let g:= f-stem i f; let Q:=segment ℝ 0 x; have h0 : (0:E)∈Q:= left_mem_segment ..; have hc:= hp 0 (Darts hx h0)
  have hg :∀ j:ℕ,j ≤ i  →  ∀ y∈Q, ‖iteratedFDeriv ℝ j g y‖  ≤  M*a^(i-j):=by
    intro j hj; induction hj using Nat.decreasingInduction with
    | self=> intro y hy; rw [show g= _ from (rfl : g=f-stem i f),iteratedFDeriv_sub_apply (hp y (Darts hx hy)) (stem_contDiff _ _|>.contDiffAt),highJet hc le_rfl le_rfl,sub_zero,Nat.sub_self,pow_zero,mul_one]; exact he y (Darts hx hy)
    | of_succ j hj ih=>
      intro y hy; let v:=iteratedFDeriv ℝ j g; change ‖v _‖ ≤ _
      have ht:v 0=0:= by unfold v g; rw [iteratedFDeriv_sub_apply (hc.of_le (by exact_mod_cast hj.le)) (stem_contDiff _ _|>.contDiffAt),firstJet hc hj le_rfl,sub_self]
      have hq:‖v y-v 0‖ ≤  M*a^(i-(j+1))*‖y-0‖:= (convex_segment ..).norm_image_sub_le_of_norm_fderiv_le (fun y hy=> ((ContDiffAt.sub (hp y (Darts hx hy)) (stem_contDiff _ _|>.contDiffAt)).differentiableAt_iteratedFDeriv (show (↑j:WithTop ℕ∞)  <  ↑i from by exact_mod_cast hj))) (fun y hy=> norm_fderiv_iteratedFDeriv.trans_le (ih y hy)) h0 hy
      have hW:‖y‖ ≤ a := mem_closedBall_zero_iff.mp (((convex_closedBall (0:E) a).segment_subset (mem_closedBall_self hA) (mem_closedBall_zero_iff.mpr hX)) hy)
      rw [ht,sub_zero,sub_zero] at hq
      exact hq.trans ((mul_le_mul_of_nonneg_left hW (by positivity)).trans_eq (by conv_rhs=> rw [show i-j=i-(j+1)+1 from by omega,pow_succ,← mul_assoc]))
  have hst: stem i f = actual (fun j:Fin i=>coeff f j.val 0) := by unfold stem actual; exact (Fin.sum_univ_eq_sum_range (fun j:ℕ=> Tensor.diagonal (coeff f j 0)) i).symm
  have hv:= hg 0 (Nat.zero_le _) x (right_mem_segment ..); unfold g at hv; rwa [norm_iteratedFDeriv_zero,Nat.sub_zero,hst] at hv

-- off value bound uses lemmas above. Exact RHS Purchase.
lemma resurrect (i j:ℕ)(hh:j < i):∃ L:ℝ,0 ≤ L ∧ ∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E],∀ (f:E → ℝ)(x c:E)(r a M V:ℝ), 0 < r  →  ‖c‖+r ≤ a  →  0 ≤ M →  0 ≤ V →  (∀ y, Dart c r y →  ContDiffAt ℝ (↑i) f (y+x) ∧ ‖iteratedFDeriv ℝ i f (y+x)‖ ≤ M ∧ ‖f (y+x)‖ ≤ V)  → 
    Brush j (L*(V+M*a^i)) r⁻¹ f x:=by
  choose L hL H using (charter i); let A:=∑ k:Fin i,(Nat.factorial k.val:ℝ)* L k; have hA : 0 ≤ A:= Finset.sum_nonneg fun i _=> mul_nonneg (by positivity) (hL _)
  refine ⟨A,hA,fun E _ _ f' x c r a M V hr ha hM hV h=>?_⟩; have hA':0 ≤ a:= le_trans (by positivity) ha
  have hy : Dart c r 0:= ⟨0,⟨le_rfl,zero_le_one⟩,by simp⟩; have hx:ContDiffAt ℝ (↑i) f' x := (zero_add x) ▸ (h 0 hy).1
  let g (y:E):= f' (y+x); let P:Pkt E i:= fun k=> coeff g k.val 0
  have hg (y:E) (hy:Dart c r y):ContDiffAt ℝ (↑i) g y:= (h _ hy).1.comp (f:=fun z=> z+x) _ (contDiffAt_id.add contDiffAt_const)
  let B:= V+M*a^i; have hB:B ≥ 0:=add_nonneg hV (mul_nonneg hM (pow_nonneg hA' _))
  have hP (y:E)(he:Dart c r y): ‖Cabana.actual P y‖  ≤  B:= by
    have hp := Cabana.means hr ha hM hg (fun x hx=> by unfold g; rw [iteratedFDeriv_comp_add_right]; exact (h x hx).2.1 -- edit
      ) y he
    refine le_trans (b:= ‖g y‖+‖g y-Cabana.actual P y‖) ?_ (add_le_add (h y he|>.2.2) hp); rw [norm_sub_rev]; exact norm_le_insert' _ _ -- edit
  refine ⟨hx.of_le (by exact_mod_cast hh.le),inv_nonneg.mpr hr.le,fun i' he=>?_⟩; let k:Fin i:=⟨i',he.trans_lt hh⟩
  let t:= (Nat.factorial i':ℝ); have ht:0 < t:= Nat.cast_pos.mpr (Nat.factorial_pos ..)
  have hp := H k E P c r B (fun n=> coeff_symm ((hg 0 hy).of_le (show (↑n.val:WithTop ℕ∞) ≤  ↑i from by exact_mod_cast n.2.le))) hr hB hP
  have hX: t • P k=iteratedFDeriv ℝ i' f' x:= by unfold P; dsimp only [Tensor.coeff]; rw [smul_smul,mul_inv_cancel₀ ht.ne',one_smul]; unfold g; rw [iteratedFDeriv_comp_add_right,zero_add] -- edit
  unfold normJ; rw [← hX,norm_smul,Real.norm_of_nonneg ht.le]; rw [mul_assoc]
  apply (mul_le_mul_of_nonneg_left hp ht.le).trans; change t*(L k*B*r⁻¹^k.val)  ≤  A*(B*_); rw [mul_assoc (L k),← mul_assoc]; exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun k=> (Nat.factorial k.val:ℝ)*L k) (fun i _=> mul_nonneg (Nat.cast_nonneg _) (hL _)) (Finset.mem_univ k)) (by positivity)
end YM.LocalLTE.Cabana
