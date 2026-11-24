import YM.Trace.Fock.Elimination
noncomputable section
set_option maxHeartbeats 600000
set_option autoImplicit false
namespace YM.Trace.Shell
open YM Filter MeasureTheory Complex Set Function Boundary
open scoped Pointwise Topology ENNReal BigOperators InnerProductSpace
variable {m n : ℕ} (f : Test4) (v : Test4→L[ℂ] Sum m) (hv : FieldImage v) (hf : CC f) (hq : subquartic f v)
include hv hf hq
lemma subbound_cell (k : @Angle m (n+1)) : ∃ C≥(0:ℝ), (n+1≥4→C=0) ∧ ∀ t≥1,
   (∫ p, ‖componentFn k (v (normalized f t) (n+1)) p‖^2∂νpow (n+1)) ≤ C*t^6 := by
 obtain ⟨q,c,hc,h⟩:=quotient_bound v hv k
 let w := beamLip f c hc
 let s := degrees q (n+1)
 have H : Tendsto (fun θ:ℝ=> θ⁻¹^4 * ‖linePoly s (n+1) w θ‖) atTop (𝓝 0) := squeeze_zero' (.of_forall (fun _=>mul_nonneg (by positivity) (norm_nonneg _))) ((eventually_gt_atTop (0:ℝ)).mono (fun t (ht:t>0)=> mul_le_mul_of_nonneg_left (linePoly_le f c v hv k hf hc h ht) (by positivity))) hq
 obtain ⟨C,hC,hz,hP⟩:=char_deg w s H
 by_cases h1:n+1≥4
 · refine ⟨0,le_rfl,fun _=>rfl,fun t ht=> le_of_eq ?_⟩
   have h:= linePoly_component f c v hv k hf hc h (zero_lt_one.trans_le ht)
   rw [← h,hz h1,norm_zero]; ring
 exact ⟨C^2,by positivity,fun hi=> h1 hi |>.elim,fun t ht=> by rw [← linePoly_component f c v hv k hf hc h (zero_lt_one.trans_le ht),show t^6=(t^3)^2 from by ring, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hP _ ht) _⟩
lemma zerothConstant (t : ℝ) (ht : 0 < t) : v (normalized f t) 0 = v f 0 := Lp.ext (by
 filter_upwards [fullWave_of_CC v hv f hf 0,fullWave_of_CC v hv (normalized f t) (normalized_CC hf _) 0] with x hx ht'
 rw [hx,ht',show total x=0 by simp [total],plus_normalized f ht,smul_zero])
lemma sector_coarsened (n : ℕ) : ∃ C≥(0:ℝ), (n≥4→C=0) ∧ ∀ t≥1, ‖v (normalized f t) n‖^2 ≤ C*t^6 := by
 cases n with
 | zero =>
     exact ⟨‖v f 0‖^2,by positivity, by omega,fun t ht=> by rw [zerothConstant f v hv hf hq _ (by linarith)]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht (n:=6))⟩
 | succ n =>
    choose C hc hz hk using subbound_cell (n:=n) f v hv hf hq
    refine ⟨∑ k:@Angle m (n+1), C k, Finset.sum_nonneg (fun k _=> hc _),fun h0=> Finset.sum_eq_zero (fun k _=>hz _ h0),fun t ht=>?_⟩
    rw [assembled_sq f v hv,Finset.sum_mul]; exact Finset.sum_le_sum (fun k _=>hk k t ht)

lemma square_subpower : ∃ C≥(0:ℝ), ∀ r≥1, ‖v (normalized f r)‖^2 ≤ C*r^6 := by
 choose B hB hz hk using fun n=>sector_coarsened f v hv hf hq n
 refine ⟨∑ i∈Finset.range 4, B i, Finset.sum_nonneg (fun i _=>(hB i)),fun t ht=> ?_⟩
 have eq (z : Sum m) : ‖z‖^2=∑' n, ‖z n‖^2 := by
     convert lp.norm_rpow_eq_tsum (p:=2) (by simp) z using 2 <;> norm_num [Real.rpow_two]
 rw [eq,tsum_eq_sum (s:=Finset.range 4) ?_,Finset.sum_mul]; exact Finset.sum_le_sum (fun k _=>hk k t ht)
 intro i hi; exact le_antisymm ((hk _ _ ht).trans_eq (by simp [hz _ (show i≥4 by simpa using hi)])) (sq_nonneg ..)
end YM.Trace.Shell
