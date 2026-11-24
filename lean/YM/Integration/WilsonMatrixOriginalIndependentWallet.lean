import YM.Integration.WilsonMatrixOriginalIndependentBudget
import YM.Integration.WilsonMatrixOriginalIndependentLimit

/-! Pass the true reported physical budget to the full independently measured MS coordinates,
with the same constant for every cutoff, period and choice of submitted label. -/
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalIndependentWallet
open Filter Finset Lattice Labels RG RG12 RG17 Spec Wilson MS.Local.Physical MS.Menus FVA2
open PhysicalNext.Repeat.Legato Next.Rank.Price WilsonMatrixTicketLanesNativePrices
open WilsonMatrixOriginalIndependentColumns WilsonMatrixTicketLanesRegulatorColumn
open WilsonMatrixOriginalIndependentForest WilsonMatrixOriginalIndependentLimit
open scoped Classical Topology BigOperators

variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
    (F:Final R.family f S) (L:Layout F)

/-- The finite-date independent array costs at most the same rescaled physical budget. -/
theorem cleared (U:Ultrafilter (ℕ×ℕ)) (cut:(U:Filter (ℕ×ℕ))≤L.lens)
    (τ:ℕ→ℝ) (r:ℝ) (w:R.family.label 4) (age:R.family.ref 4≤L.level r)
    (lim:Tendsto (fun z:ℕ×ℕ=>coefficient R B (L.level r) z.1 z.2 (atRef L 4 r z w))
        (U:Filter (ℕ×ℕ)) (𝓝 (fixed R B F L τ r w))) (fee:ℝ)
    (wallet:∀N p:ℕ,L.level r≤N→Next.UVStress.quota R.family 4 (L.level r) N p
      (atRef L 4 r (N,p) w) ≤ R.family.S.a (L.level r)^4 * fee) :
    ∑i:Glyph B 4,‖fixed R B F L τ r w i‖ ≤ 16*fee*fare (warehouse R) B 4:=by
  let m:=L.level r
  have budget:=tendsto_finsetSum (univ:Finset (Glyph B 4)) (fun i _=>
    (tendsto_pi_nhds.mp lim i).norm)
  apply le_of_tendsto budget
  have positive:0<R.family.S.a m^4:=pow_pos (R.family.S.a_pos m) _
  have cheap:0≤fare (warehouse R) B 4:=sum_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  filter_upwards [((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono (cut.trans L.certified)]
    with z live
  let x:=atRef L 4 r z w
  calc
    _ ≤ _ := WilsonMatrixOriginalIndependentBudget.one R B F L m z.1 z.2 age live x
    _ ≤ ((2:ℝ)^4*((R.family.S.a m^4)⁻¹*(R.family.S.a m^4*fee)))*fare (warehouse R) B 4:=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (wallet z.1 z.2 live) (inv_nonneg.mpr positive.le)) (by positivity)) cheap
    _ = _ := by rw [inv_mul_cancel_left₀ positive.ne'];norm_num

end YM.Integration.WilsonMatrixOriginalIndependentWallet
