import YM.Frontier6.Normal.Taylor

/-! Prices polynomial/Taylor clipped terms *on the current shell*, allowing
arbitrary finite constants across arity etc. Gives far powers and also bounds
at the central scale to use for the near Taylor gain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Filter Set MeasureTheory Tensor Metric
open scoped Topology ContDiff BigOperators Classical
variable {X:Type*} [NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]

def diagonalL (i l:ℕ)(x:X): Tensor.T X ℂ i →L[ℝ] Tensor.T X ℂ l:=
    LinearMap.toContinuousLinearMap
      { toFun := fun v=> iteratedFDeriv ℝ l (Tensor.diagonal v) x
        map_add':= fun a b=> by change iteratedFDeriv ℝ l (Tensor.diagonal a + Tensor.diagonal b) x=_; exact iteratedFDeriv_add_apply (diag_smooth ..|>.contDiffAt) (diag_smooth ..|>.contDiffAt)
        map_smul':= fun c a=> by change iteratedFDeriv ℝ l (c • Tensor.diagonal a) x= c • _; exact iteratedFDeriv_const_smul_apply (hf:=(diag_smooth a l|>.contDiffAt)) }
lemma diagonal_charge (R:ℝ)(i j:ℕ) : ∃ C:ℝ,0 ≤ C ∧ ∀ A:T X ℂ i,
   Estimate j 1 (Tensor.diagonal A) (closedBall (0:X) R) (C*‖A‖):=by
  let _:= FiniteDimensional.proper ℝ X
  let I:= T X ℂ i; let W:=Module.finBasis ℝ I; let Z:= Fin (Module.finrank ℝ I)
  let L:=closedBall (0:X) R
  have ht(j:ℕ)(a:I): ∃ C:ℝ,0 ≤ C∧ ∀ x∈ L, ‖diagonalL i j x a‖ ≤ C:=by
     rcases L.eq_empty_or_nonempty with h|h; · exact ⟨1,by simp,fun x hx=>(notMem_empty x (h ▸ hx)).elim⟩
     have he:Continuous (fun x:X=> ‖diagonalL i j x a‖):=((diag_smooth a ∞).continuous_iteratedFDeriv (natural_le j)).norm
     obtain ⟨x,hx,H⟩:= (isCompact_closedBall ..).exists_isMaxOn h he.continuousOn; exact ⟨_,norm_nonneg _,fun y hy=> H hy⟩
  choose C hC h using fun (q:Fin (j+1))(i:Z)=> ht q (W i)
  let v(z:Z):= LinearMap.toContinuousLinearMap (W.coord z)
  obtain ⟨B,hB,hv⟩:= ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr fun q:Fin (j+1)=> eventually_ge_atTop (∑ z:Z,‖v z‖* C q z))).exists
  refine ⟨B,hB,fun A l hl x hx=>?_⟩
  let q:Fin (j+1):=⟨l,by omega⟩
  rw [one_pow,one_mul]; change ‖diagonalL i l x A‖ ≤ _; nth_rw 1 [← W.sum_repr A]; rw [map_sum]
  refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun z:Z=> (‖v z‖* C q z)*‖A‖) (fun z _=>?_)) ?_)
  · rw [map_smul,norm_smul]; exact (mul_le_mul ((v z).le_opNorm A) (h q z x hx) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by ring)
  rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hv q) (norm_nonneg _)

lemma fragment_estimate (j i:ℕ)(R:ℝ) (hR:0≤R):∃ C:ℝ,0 ≤ C ∧∀ (f:X→ℂ)(t P s:ℝ),0<t→0<s→ Charge i t f P→
     Estimate j s (fragment i f) (closedBall (0:X) (R*s)) (C*P*(s/t)^i):=by
   obtain ⟨C,hC,H⟩:=diagonal_charge (X:=X) R i j
   let K:=(i.factorial:ℝ)⁻¹; have hK:0 ≤ K:=by unfold K; positivity
   refine ⟨C*K,mul_nonneg hC hK,fun f t P s ht hs he l hl x hx=> ?_⟩
   let A:= Tensor.coeff f i 0
   have hA : ‖A‖ ≤ K*P / t^i:= by
      unfold A coeff; rw [norm_smul,Real.norm_of_nonneg hK]; apply (le_div_iff₀ (pow_pos ht _)).mpr
      calc
       _ = K * (t^i * _) := by ring -- unfolding?
       _ ≤ K * P := mul_le_mul_of_nonneg_left (he i le_rfl 0 (mem_univ _)) hK
   let y:= s⁻¹ • x; have hy:s • y=x:= smul_inv_smul₀ hs.ne' x
   have hi:y∈closedBall (0:X) R:=by simp only [y,mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg (inv_pos.mpr hs).le,← div_eq_inv_mul]; exact (div_le_iff₀ hs).mpr (mem_closedBall_zero_iff.mp hx)
   have hE:= congr_arg norm (homogeneous_jet l i s y A); rw [hy,norm_smul,norm_smul,Real.norm_of_nonneg (pow_pos hs i).le,Real.norm_of_nonneg (pow_pos hs l).le] at hE
   change s^l * ‖iteratedFDeriv ℝ l (Tensor.diagonal A) x‖ ≤ _; rw [← hE]
   have hf:= H A l hl y hi; rw [one_pow,one_mul] at hf
   refine le_trans (mul_le_mul_of_nonneg_left (hf.trans (mul_le_mul_of_nonneg_left hA hC)) (pow_nonneg hs.le _)) (le_of_eq ?_)
   rw [div_pow]; ring

omit [FiniteDimensional ℝ X] in
lemma estimates_sum {I:Type*}(j:ℕ)(f:I→ X→ℂ){u:Finset I}(hf:∀ i:I, Smooth (f i)) (L:Set X) (C:I→ℝ) {s:ℝ}(hs:0 ≤ s)(h:∀ i∈u,Estimate j s (f i) L (C i)): Estimate j s (∑ i∈u, f i) L (∑ i∈u,C i):=by
   induction u using Finset.induction_on with
   | empty=> intro i hi x hx; simp
   | insert i u hi ih=>
     rw [Finset.sum_insert hi, Finset.sum_insert hi]; refine Estimate.add (h i (by simp)) (ih fun k hk=>h k (Finset.mem_insert_of_mem hk)) (hf i) ?_ hs
     rw [show (∑ i ∈ u, f i)=(fun x=> ∑ i ∈ u,f i x) from funext fun x=> Finset.sum_apply ..]; exact ContDiff.sum (fun i _=> hf i)
lemma plan_estimate (j i:ℕ)(R:ℝ) (hR:0≤R):∃ C:ℝ,0 ≤ C ∧∀ (f:X→ℂ)(t P s B:ℝ),0<t→0<s→1≤B→s≤B*t→ Charge i t f P→
     Estimate j s (plan i f) (closedBall (0:X) (R*s)) (C*P*B^i):=by
   choose C hC H using fun q:Fin (i+1)=>fragment_estimate (X:=X) j q R hR
   refine ⟨_,show 0 ≤ ∑ q,C q from Finset.sum_nonneg fun q _=> hC q,fun f t P s B ht hs hB hb h=>?_⟩
   rw [Finset.sum_mul,Finset.sum_mul]
   refine estimates_sum j (fun q : Fin (i+1)=>fragment q.val f) (fun _=>fragment_smooth _) _ (fun q=> C q * P * B^i) hs.le fun q _=>Estimate.down_cost (H q f t P s ht hs (Estimate.lower h (by omega))) (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hC q) h.nonneg))
   exact le_trans (pow_le_pow_left₀ (div_nonneg hs.le ht.le) ((div_le_iff₀ ht).2 hb) q.val) (pow_le_pow_right₀ hB (by omega))
end YM.Frontier6.Normal
