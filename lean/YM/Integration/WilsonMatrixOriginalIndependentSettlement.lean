import YM.Integration.WilsonMatrixOriginalIndependentLimit

noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentSettlement
open Filter Wilson RG FVA2 Labels MS.Local.Physical MS.Menus Finset
open WilsonMatrixTicketLanesNativePrices WilsonMatrixOriginalIndependentColumns
open WilsonMatrixOriginalIndependentForest
open PhysicalNext.Repeat.Legato
open scoped Topology BigOperators Classical

variable {G:Gauge} (R:Run G) (B:Deck G) {I:Type} [Fintype I]

def book (a:I→Glyph B 4→ℂ) (v:(I→Index R)→ℂ):ℂ :=
  ∑q:I→Glyph B 4,(∏i,a i (q i))*reading R B q v

private def stock (q:I→Glyph B 4):ℝ :=
  ∑j:I→Index R,‖∏i,column (warehouse R) B 4 (q i) (j i)‖

def change (a b:I→Glyph B 4→ℂ):ℝ :=
  ∑q:I→Glyph B 4,‖(∏i,a i (q i))-∏i,b i (q i)‖*stock R B q

private theorem expense (q:I→Glyph B 4) (v:(I→Index R)→ℂ) {C:ℝ} (bound:∀j,‖v j‖≤C) :
    ‖reading R B q v‖≤ stock R B q*C := by
  unfold reading stock
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro j _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (bound j) (norm_nonneg _)

/-- This estimate is simultaneous in the entire signed non-product value array. -/
theorem settle (a b:I→Glyph B 4→ℂ) (v:(I→Index R)→ℂ) {C:ℝ} (bound:∀j,‖v j‖≤C) :
    ‖book R B a v-book R B b v‖≤change R B a b*C := by
  unfold book change
  rw [←sum_sub_distrib,sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro q _
  rw [←sub_mul,norm_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (expense R B q v bound) (norm_nonneg _)

theorem clear {Z:Type*} {l:Filter Z} (a:Z→I→Glyph B 4→ℂ) (b:I→Glyph B 4→ℂ)
    (cut:∀i,Tendsto (fun z=>a z i) l (𝓝 (b i))) :
    Tendsto (fun z=>change R B (a z) b) l (𝓝 0) := by
  have each (q:I→Glyph B 4) :
      Tendsto (fun z=>‖(∏i,a z i (q i))-∏i,b i (q i)‖*stock R B q) l (𝓝 0) := by
    have prod:Tendsto (fun z=>∏i,a z i (q i)) l (𝓝 (∏i,b i (q i))) :=
      tendsto_finsetProd _ (fun i _=>((continuous_apply (q i)).tendsto _).comp (cut i))
    simpa only [sub_self,norm_zero,zero_mul] using
      ((prod.sub (tendsto_const_nhds (x:=∏i,b i (q i)))).norm.mul_const (stock R B q))
  simpa only [change,sum_const_zero] using tendsto_finsetSum univ (fun q _=>each q)

end YM.Integration.WilsonMatrixOriginalIndependentSettlement
