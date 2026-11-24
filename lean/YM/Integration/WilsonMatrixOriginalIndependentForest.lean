import YM.Integration.WilsonMatrixOriginalIndependentColumns

/-! Expand the finite parent-matched Wilson forecast in genuine independent MS source slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentForest
open Wilson RG FVA2 Labels MS.Local.Physical MS.Menus
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open WilsonMatrixTicketLanesRegulatorColumn WilsonMatrixTicketLanesReportedMaster
open WilsonMatrixTicketLanesRegulatorCoupon Finset
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (B:Deck G) {I:Type} [Fintype I]
abbrev Index := (R.family.labels.level 4).Index


def entering (k N p:ℕ) (v:R.family.label 4) : R.family.label 4 := color R 4 k N p (entry R 4 k N p v)

def coefficient (k N p:ℕ) (v:R.family.label 4) : (Glyph B 4) → ℂ :=
  weights (warehouse R) B 4 (entering R k N p v)

def reading (q:I→(Glyph B 4)) (value:(I→(Index R))→ℂ) : ℂ :=
  ∑ j:I→(Index R),(∏ i,column (warehouse R) B 4 (q i) (j i))*value j

def independent (k N p:ℕ) (top:I→R.family.label 4) (value:(I→(Index R))→ℂ) : ℂ :=
  ∑ q:I→(Glyph B 4),(∏i,coefficient R B k N p (top i) (q i))*reading R B q value

/-- All coherent MS words on the actual finite regulator, including each genuine one-point term. -/
theorem forecast_eq (simple:G.Simple) (k N p:ℕ) (top:I→R.family.label 4) (value:(I→(Index R))→ℂ) :
    forecast R (k:=k) (fun _:I=>4) N p top value = independent R B k N p top value := by
  have hi (i:I) (j:(Index R)) :
      entering R k N p (top i) j = ∑ q:(Glyph B 4),coefficient R B k N p (top i) q * column (warehouse R) B 4 q j := by
    exact (congrFun (resolution (warehouse R) B simple (entering R k N p (top i))) j).trans
      (by simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,coefficient])
  calc
    _ = ∑ j:I→(Index R),(∏i,∑q:(Glyph B 4),coefficient R B k N p (top i) q * column (warehouse R) B 4 q (j i))*value j := by
      unfold forecast
      apply sum_congr rfl; intro j _
      exact congrArg (fun z:ℂ=>z*value j) (prod_congr rfl (fun i _=>hi i (j i)))
    _ = ∑ j:I→(Index R),∑ q:I→(Glyph B 4),(∏i,coefficient R B k N p (top i) (q i))*
        ((∏i,column (warehouse R) B 4 (q i) (j i))*value j) := by
      apply sum_congr rfl; intro j _
      rw [Fintype.prod_sum,sum_mul]
      exact sum_congr rfl fun q _=>by rw [prod_mul_distrib,mul_assoc]
    _ = _ := by
      rw [sum_comm]
      unfold independent reading
      exact sum_congr rfl fun q _=>(mul_sum ..).symm

/-- The cost of the entire independent word roster is the product of the true finite source costs. -/
theorem mass (k N p:ℕ) (top:I→R.family.label 4) :
    ∑ q:I→(Glyph B 4),‖∏i,coefficient R B k N p (top i) (q i)‖ ≤
      ∏ i, (R.family.labels.level 4).coeffSize (entering R k N p (top i))*fare (warehouse R) B 4 := by
  simp_rw [norm_prod]
  rw [←Fintype.prod_sum (fun i q=>‖coefficient R B k N p (top i) q‖)]
  exact prod_le_prod (fun i _=>sum_nonneg fun _ _=>norm_nonneg _) (fun i _=>bounded (warehouse R) B 4 _)

end YM.Integration.WilsonMatrixOriginalIndependentForest
