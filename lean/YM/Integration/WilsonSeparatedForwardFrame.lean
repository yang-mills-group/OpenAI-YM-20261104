import YM.PhysMS.Frame.Step

/-! Move the *same* physical field to the coarser measuring frame.
The nonnegative free grades make this direction cost only an arbitrarily
small power of the length ratio.  The complete output remains present. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedForwardFrame
open Filter Set Spec Climb Trace.Pilot PhysMS
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {q : Extraction.Order} {S : Table C.book}

private theorem shrink (d : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ t ∈ Ioc (0:ℝ) 1, ∀ v : (Bel C.book).Field d,
      ‖Pert.Scale.gear C.labels d t v‖ ≤ M*‖v‖ := by
  let B := Extra.FD.recorded C.labels d
  let c i := ‖B.b i‖*‖(B.b.coord i).toContinuousLinearMap‖
  refine ⟨∑ i,c i,Finset.sum_nonneg (fun i _=>by unfold c; positivity),?_⟩
  intro t ht v
  rw [Finset.sum_mul]
  nth_rw 1 [← B.b.sum_repr v]
  rw [map_sum]
  apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i _=>?_)
  rw [map_smul,Pert.Scale.rare,norm_smul,norm_smul,Complex.norm_pow,Complex.norm_real,
    Real.norm_of_nonneg ht.1.le]
  change ‖B.b.coord i v‖*(t^(B.w i).1*‖B.b i‖) ≤ c i*‖v‖
  calc
    _ ≤ (‖(B.b.coord i).toContinuousLinearMap‖*‖v‖)*(1*‖B.b i‖) :=
      mul_le_mul ((B.b.coord i).toContinuousLinearMap.le_opNorm v)
        (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.1.le ht.2) (norm_nonneg _))
        (mul_nonneg (pow_nonneg ht.1.le _) (norm_nonneg _))
        (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (norm_nonneg _))
    _ = _ := by unfold c; ring

private theorem step (F : Final C q S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J) :
    ∃ K : ℝ, 1≤K ∧ ∀ c : ℝ, 0<c → ∀ᶠ r in trail, ∀ t ∈ Icc c 1, ∀ x : S.Field d,
      ‖(J r d).symm x‖ ≤ K*‖(J (t*r) d).symm x‖ := by
  obtain ⟨B,hB,h⟩ := Frame.comparison F d J H
  obtain ⟨M,hM,afford⟩ := shrink (C:=C) d
  refine ⟨max 1 (M*B),le_max_left ..,fun c cp=>?_⟩
  filter_upwards [h c cp] with r guard t ht x
  have tp := cp.trans_le ht.1
  let b := Frame.cocycle d J r t tp
  let v := (J (t*r) d).symm x
  have same : (J r d).symm x = Pert.Scale.gear C.labels d t (b v) := by
    apply (J r d).injective
    rw [LinearEquiv.apply_symm_apply,Frame.cocycle_value d J v t r tp,LinearEquiv.apply_symm_apply]
  rw [same]
  calc
    _ ≤ M*‖b v‖ := afford t ⟨tp,ht.2⟩ _
    _ ≤ M*(B*‖v‖) := mul_le_mul_of_nonneg_left ((guard t ht).1 v) hM
    _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg _)

/-- Every sufficiently small outer measuring length works for all smaller
inner lengths, all physical fields simultaneously, and their differences.
The constant and the outer threshold precede the choice of physical field. -/
theorem between (F : Final C q S) (d : ℕ) (J : ℝ → tower S) (H : Leading F J)
    {ε : ℝ} (εpos : 0<ε) :
    ∃ K : ℝ, 1≤K ∧ ∀ᶠ τ in trail, ∀ t ∈ Ioc (0:ℝ) 1, ∀ x : S.Field d,
      ‖(J τ d).symm x‖ ≤ K*t^(-ε)*‖(J (t*τ) d).symm x‖ := by
  obtain ⟨K,hK,paid⟩ := step F d J H
  obtain ⟨c,cp,c1,fee⟩ := ((show ∀ᶠ c:ℝ in trail,0<c from self_mem_nhdsWithin).and
    (((gt_mem_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
       (@nhdsWithin_le_nhds ℝ _ (0:ℝ) (Ioi (0:ℝ)))).and
      ((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr εpos)).eventually_ge_atTop K))).exists
  change c<1 at c1
  change K≤c^(-ε) at fee
  obtain ⟨s,sp,within⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (paid c cp)
  refine ⟨K,hK,?_⟩
  filter_upwards [show ∀ᶠ r in trail,r∈Ioc (0:ℝ) s from
    mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨s,sp,subset_refl _⟩] with τ τs t ht x
  let A (u:ℝ) := ‖(J u d).symm x‖
  have near (b:ℝ) (hb:b∈Ioc (0:ℝ) 1) : b*τ∈Ioc 0 s :=
    ⟨mul_pos hb.1 τs.1,(mul_le_of_le_one_left τs.1.le hb.2).trans τs.2⟩
  have go (m:ℕ) (b:ℝ) (hb:b∈Ioc (0:ℝ) 1) (hm:c^m≤b) :
      A τ ≤ K*b^(-ε)*A (b*τ) := by
    induction m generalizing b with
    | zero =>
      rw [pow_zero] at hm
      obtain rfl : b=1 := le_antisymm hb.2 hm
      simpa using le_mul_of_one_le_left (norm_nonneg _) hK
    | succ m ih =>
      by_cases hcb : c≤b
      · calc
          _ ≤ K*A (b*τ) := within τs b ⟨hcb,hb.2⟩ x
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans hK)
            (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb.1 hb.2 (neg_nonpos.mpr εpos.le))) (norm_nonneg _)
      have hu : b/c∈Ioc (0:ℝ) 1 := ⟨div_pos hb.1 cp,(div_le_one cp).mpr (not_le.mp hcb).le⟩
      have hprevious := ih (b/c) hu (by rw [le_div_iff₀ cp]; exact hm)
      have unroll : c*((b/c)*τ)=b*τ := by field_simp
      have one : A ((b/c)*τ) ≤ K*A (b*τ) := by
        rw [←unroll]
        exact within (near _ hu) c ⟨le_rfl,c1.le⟩ x
      have coff : 0≤ K*(b/c)^(-ε) := mul_nonneg (zero_le_one.trans hK) (Real.rpow_nonneg hu.1.le _)
      calc
        _ ≤ (K*(b/c)^(-ε))*(K*A (b*τ)) := hprevious.trans (mul_le_mul_of_nonneg_left one coff)
        _ ≤ (K*(b/c)^(-ε))*(c^(-ε)*A (b*τ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right fee (norm_nonneg _)) coff
        _ = _ := by
          have id : (b/c)^(-ε)*c^(-ε)=b^(-ε) := by
            rw [←Real.mul_rpow hu.1.le cp.le,div_mul_cancel₀ _ cp.ne']
          linear_combination K*A (b*τ)*id
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one ht.1 c1
  exact go m t ht hm.le

end YM.Integration.WilsonSeparatedForwardFrame
