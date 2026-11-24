import YM.Integration.WilsonMeasuredNullAccounts
import YM.Integration.WilsonMeasuredOriginalColumnTransition
import YM.Trace.Physicalv2.GermPrices

/-! The wrapped coordinate of any null source on the measured budget is flat in the actual scale, uniformly in the period. -/
noncomputable section
namespace YM.Integration.WilsonMeasuredNullWrappedDate
open Filter Labels Lattice Wilson RG Source Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org
open scoped Classical

variable {G:Gauge} (R:Run G)

theorem original (simple:G.Simple) (d:ℕ) (δ:ℝ) :
    ∀ᶠ i:ℕ in atTop, ∀ (per:ℕ) (W:Rep G (R.family.side i per)),
    W.p=R.family.path.levels.budget i →
    ∀ (o:Site (R.family.side i per))(P:Coefficient (R.family.labels.level d) (R.family.side i per))
      {κ b:ℝ},P.Format o R.family.params W → P.remBound o W κ b →
      d≤W.p.order → d≤W.p.power → projection (R.family.labels.level d) R.family.params W.p.threshold o P=0 →
      ‖P.x‖ ≤ (germ_close (R.family.labels.level d) R.family.params).choose*
        Real.exp (δ*R.family.S.scale i)*b:=by
  filter_upwards [GermGraph.cut_flat R.family simple δ] with i h per W budget o P κ b form paid order power null
  have price:=(WilsonMeasuredNullAccounts.wrapped (R.family.labels.level d) R.family.params o W P
    form paid order power null).2
  have nn:0≤b:=by obtain ⟨u,v,hu,hv,total,_⟩:=paid;linarith
  have width: wraps W.p (R.family.side i per) ≤ Real.exp (δ*R.family.S.scale i) :=by
    rw [budget];exact h per
  exact price.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left width (germ_close (R.family.labels.level d) R.family.params).choose_spec.1.le) nn)

end YM.Integration.WilsonMeasuredNullWrappedDate
end
