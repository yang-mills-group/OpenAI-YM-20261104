import YM.FormalBulk08.Dawn.Loft

/-!
Zero-center Taylor prices in test norm, including a quantitative remainder
without order loss, for any fixed horizon q≤D. Use for ANY presented
real test of the stated C^D. Power indexing for basis projections below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Dawn
open Filter Set Function Tensor Lattice Maxwell
open scoped Topology BigOperators Classical ContDiff
variable {D : ℕ} {L : Side} (x : Site L)(f : Garden D)

-- power coefficient(s). Taylor kernel subtracted about fine root 0 after pull.
def dawn (j:ℕ): Garden D:=⟨diagonal (coeff f.val j 0),diag_smooth (coeff f.val j 0) D⟩
def sunset (q:ℕ): Garden D:=f-∑ i∈Finset.range q,dawn f i

lemma halo_done (g:Garden D)(k:Brush D):halo g k 0=k.1.val.factorial • (coeff g.val k.1 0 (basis ∘ k.2)) := by
   unfold halo coeff; rw [_root_.smul_apply,← Nat.cast_smul_eq_nsmul ℝ]; rw [smul_smul,mul_inv_cancel₀ (by positivity),one_smul]
lemma sunset_low (q:ℕ)(k:Brush D)(hp:q≤D)(he:k.1.val<q) : (portrait D (sunset f q)).val k origin=0 := by
   suffices hK : ∀ z, (portrait D (sunset f q)).val k origin=z→ z=0 from hK _ rfl
   intro z hz; rw [←hz,sunset,map_sub,map_sum,Submodule.coe_sub, AddSubmonoidClass.coe_finsetSum, Pi.sub_apply, Finset.sum_apply, ContinuousMap.sub_apply]
   rw [show (∑ c ∈ Finset.range q,((portrait D (dawn f c)).val k)) origin = ∑ c∈Finset.range q, (portrait D (dawn f c)).val k origin from (by simp)]
   rw [Finset.sum_eq_single k.1.val,sub_eq_zero]; swap
   · intro a ha h
     change halo _ k 0=0
     rw [halo_done]; unfold dawn; dsimp only
     have hh:=Tensor.coeff_symm (f:=f.val) (x:=0) (j:=a) (show ContDiffAt ℝ _ _ _ from (show ContDiff ℝ a f.val from (show ContDiff ℝ D f.val from f.property).of_le (Nat.cast_le.mpr ((Finset.mem_range.mp ha).le.trans hp))).contDiffAt)
     rw [Free.coeff_diagonal_ne _ hh h.symm];simp
   swap; · simp [he]
   change halo f k 0=halo _ k 0; rw [halo_done,halo_done,show coeff (dawn f k.1).val k.1.val 0=coeff f.val k.1.val 0 from Free.coeff_diagonal _ (Tensor.coeff_symm (tends f k.1).contDiffAt)]
lemma sunset_high (q:ℕ)(k:Brush D)(hp:q≤D)(he:q≤k.1.val)(x:Pier) : (portrait D (sunset f q)).val k x=(portrait D f).val k x := by
   unfold sunset; rw [map_sub,map_sum,Submodule.coe_sub, AddSubmonoidClass.coe_finsetSum, Pi.sub_apply, Finset.sum_apply,ContinuousMap.sub_apply]
   rw [show (∑ c∈Finset.range q, ((portrait D (dawn f c)).val k)) x = ∑ c∈Finset.range q, (portrait D (dawn f c)).val k x from (by simp),Finset.sum_eq_zero,sub_zero]; intro i hi; change iteratedFDeriv ℝ k.1.val (diagonal (coeff f.val i 0)) _ _=0
   have ht:=Finset.mem_range.mp hi
   rw [diag_free _ (Tensor.coeff_symm (f:=f.val) (j:=i) ((show ContDiff ℝ D f.val from f.property).contDiffAt.of_le (Nat.cast_le.mpr (ht.le.trans hp)))) (ht.trans_le he)]; rfl
lemma sunset_bill (hL:2≤L.val) (q:ℕ)(hp:q≤D) : ‖portrait D (sunset (bowl x f) q)‖≤32^q*(scale L ^ q * ‖portrait D f‖) := by
   have hb : 0≤scale L:=scale_pos.le
   refine fog _ _ _ hp (by positivity) (fun k hk p=>?_) (sunset_low (bowl x f) q · hp)
   rw [sunset_high _ q k hp hk,berry _ k f p hL, norm_mul, Real.norm_of_nonneg (pow_nonneg hb _)]
   exact mul_le_mul (pow_le_pow_of_le_one hb scale_small hk) (le_panel ..) (norm_nonneg _) (pow_nonneg hb _)

-- quantitative bill on each *homogeneous* part. profile Q validated once.
lemma dawn_bill (hL:2≤L.val)(j : ℕ)(hp:j<D) : ‖portrait D (dawn (bowl x f) j)‖≤
      (32^j+32^(j+1)) * (scale L ^ j * ‖portrait D f‖) := by
    let g := bowl x f
    have he : dawn g j = sunset g j - sunset g (j+1) := by rw [sunset,sunset,Finset.sum_range_succ];abel
    change ‖portrait _ (dawn g j)‖ ≤ _; rw [he,map_sub,add_mul]; apply (norm_sub_le ..).trans; apply add_le_add (sunset_bill x f hL _ hp.le)
    exact (sunset_bill x f hL _ hp).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one scale_pos.le scale_small j.le_succ) (norm_nonneg _)) (by positivity))
end YM.FormalBulk08.Dawn
