import YM.OPE.Compatible.Hull.Hat
/-! # generic germ threshold slope. Adapted LeadingLine.Prices.shore reused. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Source Labels Source.Drops Lattice Wilson RG Asymptotics Filter Set Function
open scoped Classical Topology Matrix.Norms.Frobenius BigOperators ContDiff

section
variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]


private lemma hears (L : E →L[ℝ] V) {n : ℕ} (hn : 1 < n) (x : E) : slopeCap n L x=0 := by
  obtain ⟨v,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
  unfold slopeCap; rw [← norm_iteratedFDeriv_fderiv,show fderiv ℝ L=(fun _ => L) from funext fun x=> L.fderiv,iteratedFDeriv_const_of_ne (show v≠0 by omega)]; simp

lemma Price_S (S : ℝ → E) (i : ℕ) (hz : S 0=0) (h : ContDiffAt ℝ i S 0) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ F : E→ V, ∀ (M t : ℝ), 0 ≤ M → F 0=0 → 0 < t → t ≤ 1 →
      (∀ k,k ≤ max 1 i → slopeCap k F 0 ≤ M) → ContDiffAt ℝ (max 1 i:ℕ) F 0 →
        let A:= fderiv ℝ F 0
        let p:= A∘S
        let W:= t⁻¹ • (F∘(t • S))
        ‖iteratedDeriv i p 0‖≤ M*C ∧ ContDiffAt ℝ i W 0 ∧ ‖iteratedDeriv i (W-p) 0‖ ≤ M*C*t := by
  let R (p : OrderedFinpartition i):=∏ j, ‖iteratedDeriv (p.partSize j) S 0‖
  let L:= ‖iteratedDeriv i S 0‖
  let C:= L+∑ j,R j
  have hl (p : OrderedFinpartition i) : 0 ≤ R p := by dsimp only [R]; positivity
  have hu : 0≤L := norm_nonneg _
  have hv' : 0 ≤ ∑ j,R j := Finset.sum_nonneg fun _ _ => hl _
  refine ⟨C,add_nonneg hu hv',fun F M t hm hF ht h₁ hw hp => ?_⟩
  intro A p W
  let Y:=F-⇑A
  have ho : slopeCap 0 Y 0=0 := by unfold Y; rw [slope0, Pi.sub_apply,hF,map_zero]; simp
  have hY : ∀ k,k ≤ i → ContDiffAt ℝ k Y 0 := fun k hi=> (hp.sub A.contDiff.contDiffAt).of_le (by exact_mod_cast hi.trans (le_max_right 1 _))
  have hA : slopeCap 1 Y 0=0 := by
    unfold slopeCap; rw [norm_iteratedFDeriv_one]; change ‖fderiv ℝ (F-⇑A) _‖=_
    rw [fderiv_sub (hp.differentiableAt (by exact_mod_cast (show max 1 i ≠0 by omega))) A.differentiableAt, A.fderiv]; simp [A]
  have he (j : ℕ) (hi : 1 < j) (hh : j ≤ i) : slopeCap j Y 0≤ M := by
    unfold slopeCap Y; rw [iteratedFDeriv_sub_apply (hp.of_le (by exact_mod_cast hh.trans (le_max_right 1 _))) A.contDiff.contDiffAt]
    apply (norm_sub_le ..).trans; rw [show ‖iteratedFDeriv ℝ j A 0‖=0 from hears A hi _, add_zero]; exact hw _ (by omega)
  have hV : (t • S) 0=0 := by simp [hz]
  have hp' : ContDiffAt ℝ i (t•S) 0 := (contDiffAt_const (c:=t)).smul h
  have hf : W-p=t⁻¹ • (Y∘(t • S)) := by funext s; simp only [W,p,Y, Pi.sub_apply, comp_apply,Pi.smul_apply,smul_sub,A.map_smul,smul_smul,inv_mul_cancel₀ ht.ne',one_smul]
  have ho' : ContDiffAt ℝ i (Y ∘ (t • S)) 0 := (hV ▸ hY i le_rfl : ContDiffAt ℝ i Y _).comp _ hp'
  refine ⟨?_,?_,?_⟩
  · unfold p; rw [guiding A S i 0 h]; apply (A.le_opNorm _).trans; refine mul_le_mul ?_ (le_add_of_nonneg_right hv') (norm_nonneg _) hm
    unfold A; rw [← norm_iteratedFDeriv_one F]; exact hw _ (le_max_left ..)
  · have hc : ContDiffAt ℝ i F ((t • S) 0) := hV ▸ hp.of_le (by exact_mod_cast le_max_right 1 i)
    exact (contDiffAt_const (c:=t⁻¹)).smul (ContDiffAt.comp _ hc hp')
  rw [hf, iteratedDeriv_const_smul ho',norm_smul,Real.norm_of_nonneg (inv_pos.mpr ht).le, ← div_eq_inv_mul, div_le_iff₀ ht,
    iteratedDeriv_vcomp_eq_sum_orderedFinpartition (show ContDiffAt ℝ i Y ((t • S) 0) from hV ▸ hY i le_rfl) hp' le_rfl,hV]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ p : OrderedFinpartition i, M*t^2*R p := by
      apply Finset.sum_le_sum; intro p _
      let v:= p.length; apply (ContinuousMultilinearMap.le_opNorm ..).trans
      by_cases hh : 1 < v
      · rw [mul_assoc]; refine mul_le_mul (he _ hh p.length_le) ?_ (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hm
        have hB j : ‖iteratedDeriv (p.partSize j) (t • S) 0‖ ≤ t* ‖iteratedDeriv (p.partSize j) S 0‖ := by
          rw [iteratedDeriv_const_smul (h.of_le (by exact_mod_cast p.partSize_le j)),norm_smul,Real.norm_of_nonneg ht.le]
        apply le_trans (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => hB j))
        rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht.le h₁ hh) (hl p)
      · have hv : slopeCap v Y 0=0 := by rcases show v=0∨v=1 by omega with h|h<;> simp only [h,ho,hA]
        rw [show ‖iteratedFDeriv ℝ p.length Y 0‖=0 from hv, zero_mul]; exact mul_nonneg (mul_nonneg hm (sq_nonneg _)) (hl p)
    _ ≤ _ := by rw [← Finset.mul_sum]; unfold C; nlinarith only [mul_nonneg (mul_nonneg hm hu) (sq_nonneg t)]
end
end YM.Next.Rank.Spindle
