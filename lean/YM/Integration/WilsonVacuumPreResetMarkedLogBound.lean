import YM.Integration.WilsonVacuumPreResetMarkedOrdinaryBound

/-! The genuine finite connected logarithm of full ordinary heat
cofactors, retaining the product of all occupied source bills. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedLogBound
open Function Finset WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonVacuumPreResetMarkedProducts WilsonVacuumPreResetMarkedOrdinaryBound
open scoped Classical BigOperators
variable {ι U:Type}[DecidableEq ι]{D:ι→ℕ}

private def point (I:Finset ι)(h e r:ℕ)(x:Fin r→U):
    Layers (Pen D I) U→ₗ[ℝ] Pen D I where
  toFun p:=p h e r x
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

theorem original (D:ι→ℕ)(I:Finset ι)(e r h:ℕ):∃C:ℝ,0≤C ∧
    ∀(U:Type)(X:thalamus D U)(a:ι→ℝ), (∀j,0≤a j)→
    (∀J⊆I,J.Nonempty→∀u≤h,Bounded e r (X J u) (weights a J))→
    ∀v≤h,Bounded e r (turnTLog X I v) (C*weights a I):=by
  induction I using Finset.strongInduction with
  | H I ih=>
    by_cases empty:I=∅
    · subst I
      refine ⟨0,le_rfl,?_⟩
      intro U X a _ _ v _ i _ l _ x
      rw [turnTLog,dif_pos rfl]
      simp only [Pi.zero_apply,norm_zero,zero_mul,le_refl]
    · let price(J:Finset ι):ℝ:=if w:J⊆I∧J≠I then (ih J (lt_of_le_of_ne w.1 w.2)).choose else 0
      let charge(J:Finset ι):ℝ:=(J.card:ℝ)*(h+1:ℕ)*tariff e r*price J
      have pos(J:Finset ι):0≤price J:=by
        by_cases w:J⊆I∧J≠I
        · simpa only [price,dif_pos w] using (ih J (lt_of_le_of_ne w.1 w.2)).choose_spec.1
        · simp [price,w]
      have chpos(J:Finset ι):0≤charge J:=by dsimp only [charge,tariff];have:=pos J;positivity
      let fee:ℝ:=(I.card:ℝ)⁻¹*∑J∈I.powerset,charge J
      have fpos:0≤fee:=mul_nonneg (by positivity) (Finset.sum_nonneg fun J _=>chpos J)
      refine ⟨1+fee,by linarith,?_⟩
      intro U X a nonneg raw v hv i hi l hl x
      rw [turnTLog,dif_neg empty]
      change ‖point I v i l x (X I-(I.card:ℝ)⁻¹ • ∑J∈I.powerset, if w:J⊆I∧J≠I then
        (J.card:ℝ) • foamT w.1 (turnTLog X J) (X (I\J)) else 0)‖≤_
      rw [map_sub,map_smul,map_sum,add_mul,one_mul]
      apply (norm_sub_le ..).trans
      apply add_le_add (raw I le_rfl (Finset.nonempty_iff_ne_empty.mpr empty) v hv i hi l hl x)
      dsimp only [fee]
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(I.card:ℝ)⁻¹),
        mul_assoc,Finset.sum_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le ..).trans
      apply Finset.sum_le_sum
      intro J _
      by_cases w:J⊆I∧J≠I
      · have strict:=lt_of_le_of_ne w.1 w.2
        have earlier:∀v≤h,Bounded e r (turnTLog X J v) (price J*weights a J):=by
          simpa only [price,dif_pos w] using
            (ih J strict).choose_spec.2 U X a nonneg (fun V inside=>raw V (inside.trans w.1))
        have other:=raw (I\J) Finset.sdiff_subset (Finset.sdiff_nonempty.mpr (not_le_of_gt strict))
        have fine:=time_bound w.1 _ _ e r h _ _
          (mul_nonneg (pos J) (positive a nonneg _)) (positive a nonneg _) earlier other v hv i hi l hl x
        simp only [dif_pos w,map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(J.card:ℝ))]
        apply (mul_le_mul_of_nonneg_left fine (Nat.cast_nonneg J.card)).trans_eq
        dsimp only [charge]
        rw [← splitCost a w.1]
        ring
      · simp only [dif_neg w,map_zero,norm_zero]
        exact mul_nonneg (chpos J) (positive a nonneg I)

end YM.Integration.WilsonVacuumPreResetMarkedLogBound
end
