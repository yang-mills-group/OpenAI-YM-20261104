import YM.FormalBulk08.Dawn.Coast

/-! Convert individual profile costs to *one* formal signed-address
presentation. No loss on enlarging volume and test needn't be polynomial.
Exchange linear mixtures in any fixed derivative demand.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Dawn
open Filter Set MeasureTheory Function
open scoped BigOperators Topology ENNReal Classical
variable {D : ℕ}

lemma address_account (A:ℝ) (hA:0≤A)(b : Studio D→ₗ[ℝ]ℝ)(hp:∀ x, ‖b x‖≤A*‖x‖) : ∃ μ ν:Brush D→Measure Pier,(∀ i,IsFiniteMeasure (μ i)) ∧ (∀ i,IsFiniteMeasure (ν i)) ∧
    (∑ i, ((μ i).real univ + (ν i).real univ))≤ Fintype.card (Brush D)*A ∧ ∀ f: Studio D,
    b f=∑ i, ((∫ t,f.val i t ∂(μ i)) - ∫ t,f.val i t ∂(ν i)) := by
   obtain ⟨L,h,hL⟩:= offsets (studio D) b A hA hp
   let g i:= ContinuousLinearMap.single ℝ (fun _:Brush D=>Hub) i
   choose μ ν hμ hν he ht using fun i=>dual_ferns (L.comp (g i))
   refine ⟨μ,ν,hμ,hν,?_,fun f=>?_⟩
   · simp_rw [he]; refine le_trans (Finset.sum_le_sum (f:=fun i=>‖L.comp (g i)‖) (g:=fun _=>A) (fun i _=> ?_)) ?_
     · refine le_trans ?_ hL; exact (ContinuousLinearMap.opNorm_comp_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_single_le_one ..))
     simp
   simp_rw [←ht]; have he : f.val=∑ i,g i (f.val i):=(Finset.univ_sum_single _).symm
   exact (h f).symm.trans ((congr_arg L he).trans (map_sum L ..))
end YM.FormalBulk08.Dawn
