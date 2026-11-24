import YM.MS.MomOrigin
import YM.MS.SymbolParts

/-! Momentum vanishing for fixed local Taylor jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Scale
open Set Function Real Filter
open scoped Topology ContDiff
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F}
lemma flat_right {S : Scale ι} (h : ∀ i, 1≤ S.length i) (j: ℕ) (hf : f.HasTemperateGrowth)
    (hv : ∀ k < j, iteratedFDeriv ℝ k f 0 = 0) : Bound S (fun _=> f) fun i=> (S.length i ^ j)⁻¹ := by
   refine ⟨fun _ => hf.1,?_⟩
   have H (k : ℕ) (hk : j ≤ k) : S.full.Part S (fun _=>f) (fun i _=> (S.length i ^ j)⁻¹) k := by
      obtain ⟨b,C,hC,hp⟩ := hf.norm_iteratedFDeriv_le_uniform k
      refine ⟨C+1,by positivity,b, fun i p _=>?_⟩
      specialize hp k le_rfl p; apply hp.trans
      have hL := h i
      have he : 1 + ‖p‖ ≤ S.full.cheap i p := calc
          _ ≤ S.weight i p := add_le_add_right (le_mul_of_one_le_left (norm_nonneg p) hL) _ -- orientation
          _ ≤ _ := le_mul_of_one_le_left (S.weight_pos i p).le (S.one_le i)
      refine le_trans ?_ (le_mul_of_one_le_right (by have H:=S.full.cheap_pos (p:=p) (i:=i) trivial; positivity) (show 1 ≤ _ from ?_))
      · gcongr; linarith
      dsimp only; rw [←div_eq_inv_mul]; exact (one_le_div (by positivity)).mpr (by gcongr)
   intro k; rcases le_total j k with he|he
   exact H k he
   induction he using Nat.decreasingInduction with
   | self => exact H j le_rfl
   | of_succ x hx IH =>
       refine LogTime.lower_jet S (fun _ => hf.1) (Cost.of_le fun i p _=> ?_) IH
       have hr:=h i; rw [hv x hx,norm_zero]; positivity

lemma rescaled (S : Scale ι) (hf : f.HasTemperateGrowth) : Bound S (fun i p => f (S.length i • p)) fun _=>1 := by
   refine ⟨fun i=> hf.1.comp (contDiff_const.smul contDiff_id), fun j=>?_⟩
   obtain ⟨b,C,hC,hp⟩:=hf.norm_iteratedFDeriv_le_uniform j
   refine ⟨(C+1)* ‖ContinuousLinearMap.id ℝ E‖^j+1, by positivity,b,fun i p _=>?_⟩
   let A := ContinuousLinearMap.id ℝ E; let R := S.length i; have hR : 0<R:=S.pos i; let L:= R • A
   have hL : ‖L‖ = R * ‖A‖ := by unfold L; rw [norm_smul,Real.norm_of_nonneg hR.le]
   have he : (1 + ‖L p‖) ≤ S.full.cheap i p := by
     change 1+‖R • p‖ ≤ _; rw [norm_smul_of_nonneg hR.le]; exact le_mul_of_one_le_left (S.weight_pos i p).le (S.one_le i)
   dsimp only; rw [one_mul]
   change ‖iteratedFDeriv ℝ j (f ∘ L) _‖ ≤ _
   rw [L.iteratedFDeriv_comp_right hf.1 _ (by exact_mod_cast le_top)]; apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
   rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,hL]
   let w:= S.full.cheap i p; have hw : 0<w:=S.full.cheap_pos trivial
   have ht := norm_nonneg A
   calc
    _ ≤ C*w^b*(R * ‖A‖)^j:= by apply mul_le_mul_of_nonneg_right _ (by positivity); apply (hp j le_rfl _).trans; gcongr
    _ = C * ‖A‖^j * w^b*R^j := by rw [mul_pow]; ring
    _ ≤ ((C+1)*‖A‖^j+1)*w^b*R^j:= by gcongr; nlinarith [pow_nonneg ht j]
    _ = _ := rfl
end YM.MS.Scale
