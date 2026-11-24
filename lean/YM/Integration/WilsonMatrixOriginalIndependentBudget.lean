import YM.Integration.WilsonMatrixOriginalIndependentForest

/-! Spend a single original intermediate quota on the full independent grade-four spectral roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentBudget
open Filter Function Finset Labels Lattice RG RG12 RG17 Spec Wilson MS.Local.Physical MS.Menus
open FVA2 PhysicalNext.Repeat.Legato Next.Rank.Price WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentColumns WilsonMatrixTicketLanesRegulatorColumn
open WilsonMatrixOriginalIndependentForest
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F)

include L in
theorem one (k N p:ℕ) (age:R.family.ref 4≤k) (live:k≤N) (x:R.family.label 4) :
    ∑q:Glyph B 4,‖coefficient R B k N p x q‖ ≤
      ((2:ℝ)^4*((R.family.S.a k^4)⁻¹*Next.UVStress.quota R.family 4 k N p x))*fare (warehouse R) B 4 := by
  let y:=entry R 4 k N p x
  let t:=shrink R.family k N p
  have pos:0≤t:=(shrink_pos R.family R.makes live p).le
  have upper:t≤2:=RG12.Arche.shrink_current (C:=R.family) (p:=p) R.makes live
  have ht : RG12.mass R.family 4 (entering R k N p x) ≤ (2:ℝ)^4 * RG12.mass R.family 4 y := by
    unfold RG12.mass Frame.coeffSize
    rw [mul_sum]
    refine sum_le_sum fun i _=>?_ 
    change ‖(R.family.labels.level 4).scaled t y i‖≤_
    rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg pos _)]
    exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ pos upper _).trans
      (pow_le_pow_right₀ one_le_two (Planned.PrimaryIntegral295.Film.second_fits (R.family.labels.level 4) i))) (norm_nonneg _)
  have budget : RG12.mass R.family 4 y = _:=cost R F L 4 k N p age live x
  rw [budget] at ht
  exact (bounded (warehouse R) B 4 _).trans (mul_le_mul_of_nonneg_right ht
    (sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _))

include L in
theorem roster {I:Type} [Fintype I] (k N p:ℕ) (age:R.family.ref 4≤k) (live:k≤N) (x:I→R.family.label 4) :
    ∑q:I→Glyph B 4,‖∏i,coefficient R B k N p (x i) (q i)‖ ≤
      ∏i,(((2:ℝ)^4*((R.family.S.a k^4)⁻¹*Next.UVStress.quota R.family 4 k N p (x i)))*fare (warehouse R) B 4) := by
  simp_rw [norm_prod]
  rw [←Fintype.prod_sum (fun i q=>‖coefficient R B k N p (x i) q‖)]
  exact Finset.prod_le_prod (fun i _=>sum_nonneg fun _ _=>norm_nonneg _) (fun i _=>one R B F L k N p age live (x i))

end YM.Integration.WilsonMatrixOriginalIndependentBudget
