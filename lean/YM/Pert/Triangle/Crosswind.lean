import YM.Pert.Triangle.Mollify
/-! Nonzero projected overlap at separated positions by averaging independently over two bulk locations with the same temporary compact envelope. Diagonal singularity is NOT treated as a pointwise square integral; uses Fubini on two independent points. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Pert.Triangle
open Maxwell Analysis Set Function Metric Filter TopologicalSpace MeasureTheory
open scoped ContDiff Topology RealInnerProductSpace Classical
lemma coordLower {w : E4} (hw : w∈birth) {x} (hx : x∈stub) : 0 < (w-x) (0:Axis) := by
  let r := (3:ℝ) • along
  have h := mem_ball_iff_norm.mp hw
  have hu := mem_closedBall_zero_iff.mp hx -- name?
  have e : r 0 = 3 := by norm_num [r]
  have bounds (u : E4) : |u 0| ≤ ‖u‖ := by simpa only [basis_inner,basis_norm,one_mul] using (abs_real_inner_le_norm (basis 0) u)
  have he:= bounds (w-r)
  have hv := bounds x
  change |w 0-r 0| ≤ _ at he
  change 0<w 0-x 0
  rw [e] at he
  change ‖w-r‖<1 at h
  linarith [neg_abs_le (w 0 - 3),le_abs_self (x 0)]
lemma flowPos {w:E4} (hw : w∈birth) {x} (hx : x∈stub) : 0 < flow (0:Axis) (w-x) := by
  have ht := coordLower hw hx
  have q : w-x≠0 := by
    intro h
    exact (lt_irrefl (0:ℝ)) (by rw [h] at ht; exact ht)
  unfold flow
  rw [first_Green q]
  have h := normal_pos
  have h' := norm_pos_iff.mpr q
  have : 0 < normal := normal_pos
  rw [show ∀ a b c : ℝ,-(-2*a*b*c)=2*a*b*c from fun _ _ _=>by ring]
  exact mul_pos (mul_pos (mul_pos (by norm_num) this) ht) (pow_pos (inv_pos.mpr (sq_pos_of_pos h')) 2)
lemma positive_test {f : E4→ℝ} {s : Set E4} (hf : Integrable f volume) (hn : 0 ≤ f) (hs : volume s ≠ 0) (hy : ∀ x∈s, f x ≠ 0) : 0 < ∫ x, f x := lt_of_le_of_ne (integral_nonneg hn) (by
  intro hi
  have := (integral_eq_zero_iff_of_nonneg hn hf).mp hi.symm
  exact hs (measure_mono_null (t:= {x | f x ≠ 0}) (fun x hx=>hy x hx) (mem_ae_iff.mp this)))
lemma witnessPositive (w) (hw : w∈birth) : 0 < mean 0 w := positive_test (rockPay _ w) (fun x=>by rw [Pi.zero_apply]; unfold rock; dsimp; split_ifs with hx; exact (flowPos hw hx).le; rfl) stubPositive (fun x hx=>by unfold rock;rw [if_pos hx]; exact (flowPos hw hx).ne')
-- product norm integrals already justified in Mollify
def pulse (xy:E4 × E4) (w : E4) := ∑ a:Axis, squaredIntegrand a (xy,w)
def overlap (x y:E4) := ∫ w, ∑ a:Axis,flow a (w-x) * flow a (w-y)
def overlapAux (xy : E4 × E4) := if xy.1∈stub ∧ xy.2∈stub then overlap xy.1 xy.2 else 0
lemma momentPay (a : Axis) : Integrable (fun w=> (mean a w)^2) volume := by
  have h := squarePay a |>.integral_prod_right
  simpa only [outerSquare] using h
lemma pulseOverlap (xy:E4 × E4) : ∫ w:E4, pulse xy w = overlapAux xy := by
  unfold overlapAux; split_ifs with h
  · apply congrArg _; funext w
    unfold pulse squaredIntegrand; simp_rw [rock,if_pos h.1,if_pos h.2]
  have he : pulse xy =0 := funext fun w=> by
       unfold pulse squaredIntegrand
       rcases not_and_or.mp h with h|h
       · rw [Finset.sum_eq_zero]; rfl; intro a _; rw [rock, if_neg h,zero_mul]
       rw [Finset.sum_eq_zero]; rfl; intro a _; nth_rw 2 [rock]; rw [if_neg h,mul_zero]
  simp_rw [he,Pi.zero_apply,integral_zero]
lemma pulseFubini : (∫ xy : E4 × E4, overlapAux xy ∂volume.prod volume) = (∫ w, ∑ a:Axis, (mean a w)^2 ∂volume) := by
  have hr a := (squarePay a)
  have H := integral_integral_swap (f:=pulse) (show Integrable (Function.uncurry pulse) ((volume.prod volume).prod volume) from (by convert! (integrable_finsetSum Finset.univ (fun a _=> show Integrable (squaredIntegrand a) ((volume.prod volume).prod volume) from squarePay a)) using 1))
  calc
    _ = (∫ xy : E4 × E4, (∫ w:E4,pulse xy w ∂volume) ∂volume.prod volume) := by congr 1;funext; exact (pulseOverlap _).symm
    _ = _ := H.trans (show (∫ w:E4, (∫ xy : E4 × E4,pulse xy w ∂volume.prod volume)) = _ from (by
       congr 1; funext w
       unfold pulse
       rw [integral_finsetSum]
       · exact Finset.sum_congr rfl fun _ _=>outerSquare _ _
       exact fun a _=>(rockPay a w).mul_prod (rockPay a w)))
lemma overlap_exists_nonzero : ∃ x∈stub, ∃ y∈stub, x≠y ∧ (∫ w, ∑ a:Axis,flow a (w-x) * flow a (w-y)) ≠ 0 := by
  have h : 0 < ∫ w, ∑ a:Axis, (mean a w)^2 := positive_test (integrable_finsetSum _ fun a _=> momentPay a) (fun w=> Finset.sum_nonneg (fun a _=>sq_nonneg _))
       birthPositive (fun w hw=> ne_of_gt (Finset.sum_pos' (fun _ _=>sq_nonneg _) ⟨0,Finset.mem_univ _,sq_pos_of_pos (witnessPositive w hw)⟩))
  have e : ∃ xy : E4 × E4, xy.1≠xy.2 ∧ overlapAux xy≠0 := by
    by_contra hr
    push_neg at hr
    have s : ∀ᵐ xy ∂(volume.prod volume), (xy : E4 × E4).1≠xy.2 := (Measure.ae_prod_iff_ae_ae (μ:=volume) (ν:=volume) (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr ((Eventually.of_forall fun x=> (volume.ae_ne x).mono (fun y hy=> Ne.symm hy)))
    have he : overlapAux =ᵐ[volume.prod volume] 0 := s.mono (fun xy h=> by rw [hr xy h,Pi.zero_apply])
    rw [← pulseFubini] at h -- defeq?
    exact h.ne' ((integral_congr_ae he).trans (by simp))
  obtain ⟨⟨x,y⟩,he,hi⟩ := e
  by_cases H : x∈stub ∧ y∈stub
  · rw [overlapAux, if_pos H] at hi
    exact ⟨x,H.1,y,H.2,he,hi⟩
  exact False.elim (hi (if_neg H))
end YM.Pert.Triangle
