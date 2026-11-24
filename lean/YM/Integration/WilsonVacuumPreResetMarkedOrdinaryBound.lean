import YM.Integration.WilsonVacuumPreResetMarkedProducts

/-! Full finite ordinary source head at a moving inlet, priced by the
product of the actual occupied incoming cofactor bills. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedOrdinaryBound
open Function Finset Lattice Wilson RG WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonVacuumPreResetMarkedProducts PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{ι:Type}[DecidableEq ι]{D:ι→ℕ}

def weights(a:ι→ℝ)(I:Finset ι):ℝ:=∏j∈I,a j

theorem splitCost (a:ι→ℝ){I J:Finset ι}(sub:J⊆I):weights a J*weights a (I\J)=weights a I:=by
  unfold weights
  rw [mul_comm,Finset.prod_sdiff sub]

omit [DecidableEq ι] in
theorem positive (a:ι→ℝ)(a0:∀j,0≤a j)(I:Finset ι):0≤weights a I:=
  Finset.prod_nonneg (fun j _=>a0 j)

private def point (I:Finset ι)(n:Side)(i r:ℕ)(x:Fin r→Woods G n):
    Era G (Pen D I)→ₗ[ℝ]Pen D I where
  toFun p:=p.1 n i r x
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

omit [DecidableEq ι] in
private theorem unitBound (G:Gauge)(D:ι→ℕ)(n:Side)(e r:ℕ):
    Bounded e r ((puff D G).1 n) ‖ochre D‖:=by
  intro i _ l _ x
  change ‖uband (1:Cost) i l x • ochre D‖≤‖ochre D‖
  cases l
  · simp only [uband,shine_lit];rw [coeff_one];split <;> simp
  · simp only [uband,shine_dark (show 0≠_+1 by omega),Pi.zero_apply,zero_smul,norm_zero,norm_nonneg]

/-- The cofactor bound precedes the underlying torus, field and source
positions. Every proper face retains its own product of deposited bills. -/
theorem original (G:Gauge)(D:ι→ℕ)(I:Finset ι)(e r:ℕ):∃C:ℝ,0≤C ∧
    ∀(n:Side)(K:family G D)(a:ι→ℝ), (∀j,0≤a j)→
    (∀J⊆I,J.Nonempty→Bounded e r ((K J).1 n) (weights a J))→
    Bounded e r ((levelsO K I).1 n) (C*weights a I):=by
  induction I using Finset.strongInduction with
  | H I ih=>
    by_cases empty:I=∅
    · subst I
      refine ⟨‖ochre D‖,norm_nonneg _,fun n _ _ _ _=>?_⟩
      simpa only [empty_level,weights,Finset.prod_empty,mul_one] using unitBound G D n e r
    · let price(J:Finset ι):ℝ:=if w:J⊆I∧J≠∅ then (ih (I\J) (sh_k w.1 w.2)).choose else 0
      let charge(J:Finset ι):ℝ:=(J.card:ℝ)*tariff e r*price J
      have pos(J:Finset ι):0≤price J:=by
        by_cases w:J⊆I∧J≠∅
        · simpa only [price,dif_pos w] using (ih _ (sh_k w.1 w.2)).choose_spec.1
        · simp [price,w]
      have chpos(J:Finset ι):0≤charge J:=by
        dsimp only [charge,tariff]
        have:=pos J;positivity
      refine ⟨(I.card:ℝ)⁻¹*∑J∈I.powerset,charge J,mul_nonneg (by positivity) (Finset.sum_nonneg fun J _=>chpos J),?_⟩
      intro n K a nonneg paid i hi l hl x
      rw [levelsO,dif_neg empty]
      change ‖point I n i l x ((I.card:ℝ)⁻¹ • ∑J∈I.powerset, if w:J⊆I∧J≠∅ then
        (J.card:ℝ) • waxV w.1 (K J) (levelsO K (I\J)) else 0)‖≤_
      simp only [map_smul,map_sum,norm_smul,Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : 0≤(I.card:ℝ)⁻¹)]
      rw [mul_assoc,Finset.sum_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply (norm_sum_le ..).trans
      apply Finset.sum_le_sum
      intro J _
      by_cases w:J⊆I∧J≠∅
      · have u:=sh_k w.1 w.2
        have cover:= (ih (I\J) u).choose_spec.2 n K a nonneg
          (fun T under=>paid T (under.trans Finset.sdiff_subset))
        have old:Bounded e r ((levelsO K (I\J)).1 n) (price J*weights a (I\J)):=by
          simpa only [price,dif_pos w] using cover
        have result:=foam_bound w.1 ((K J).1 n) ((levelsO K (I\J)).1 n) e r _ _
          (positive a nonneg J) (mul_nonneg (pos J) (positive a nonneg _))
          (paid J w.1 (Finset.nonempty_iff_ne_empty.mpr w.2)) old i hi l hl x
        simp only [dif_pos w,map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤(J.card:ℝ))]
        apply (mul_le_mul_of_nonneg_left result (Nat.cast_nonneg J.card)).trans_eq
        dsimp only [charge]
        rw [← splitCost a w.1]
        ring
      · simp only [dif_neg w,map_zero,norm_zero]
        exact mul_nonneg (chpos J) (positive a nonneg I)

end YM.Integration.WilsonVacuumPreResetMarkedOrdinaryBound
end
