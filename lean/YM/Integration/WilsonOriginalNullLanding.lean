import YM.Integration.WilsonOriginalNullColumnSplit
import YM.Integration.WilsonMeasuredSectionCorrection

/-! The actual lower projection and its signed field-valued feed. Present the
landing either in the intrinsic local section or in a registered field with
that same measured coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullLanding
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Relay
open Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "S₀" => R.family.localSection d
local notation "Y₀" => R.family.params

theorem local_section (simple:G.Simple) : ∀ᶠ i:ℕ in atTop, ∀ (per:ℕ)
    (W:Rep G (R.family.side i per)), W.p=R.family.path.levels.budget i →
    ∀ (o:Site (R.family.side i per)) (P:Coefficient F₀ (R.family.side i per)) {κ b:ℝ},
    P.Format o Y₀ W → P.remBound o W κ b → (F₀).coeffSize P.x ≤ b →
    d ≤ W.p.order → d ≤ W.p.power → W.p.supportExponent ≤ 100 →
    let α:=projection F₀ Y₀ W.p.threshold o P
    let z:=WilsonMeasuredSectionCorrection.subtract F₀ P α
    z.Format o Y₀ W ∧ z.remBound o W κ b ∧ projection F₀ Y₀ W.p.threshold o z=0 ∧
    (F₀).coeffSize z.x ≤ b ∧ (F₀).coeffSize α ≤ 2*b ∧
    P.density o S₀ W=z.density o S₀ W + (primary o α).density o S₀ W := by
  filter_upwards [WilsonOriginalNullProjectedPrice.original R d simple] with i bank
  intro per W point o P κ b form paid gross dw pw support α z
  obtain ⟨shaped,fee,zero,read,_,_⟩:=WilsonMeasuredSectionCorrection.original
    F₀ Y₀ S₀ o W P form paid dw pw support
  obtain ⟨diff,head⟩:=bank per W point o P form paid dw pw
  refine ⟨shaped,fee,zero,?_,?_,?_⟩
  · change (F₀).coeffSize (P.x-α) ≤ b
    have sym : (F₀).coeffSize (P.x-α)=(F₀).coeffSize (α-P.x):=by
      unfold Frame.coeffSize;apply Finset.sum_congr rfl;intro j _;exact norm_sub_rev ..
    exact sym.le.trans diff
  · linarith only [head,gross]
  · funext U;change _ = _+(primary o α).density o S₀ W U
    rw [primary_density];exact read U

theorem normalized (i per:ℕ) (W:Rep G (R.family.side i per))
    (o:Site (R.family.side i per)) (P Y:Coefficient F₀ (R.family.side i per)) {κ b e σ C Λ δ w:ℝ}
    (law:W.Lawful σ C Λ δ w) (dw:d ≤ W.p.order) (pw:d ≤ W.p.power)
    (form:P.Format o Y₀ W) (paid:P.remBound o W κ b) (sForm:Y.Format o Y₀ W)
    (sPaid:Y.remBound o W κ e)
    (registered : projection F₀ Y₀ W.p.threshold o Y=projection F₀ Y₀ W.p.threshold o P)
    (funded : e ≤ 2*(R.family.path.levels.params i).columns*b) :
    ∃ z:Coefficient F₀ (R.family.side i per),z.Format o Y₀ W ∧
      z.remBound o W κ ((2+4*(R.family.path.levels.params i).columns)*b) ∧
      projection F₀ Y₀ W.p.threshold o z=0 ∧
      P.density o S₀ W=z.density o S₀ W+Y.density o S₀ W := by
  obtain ⟨z,shape,fee,null,read⟩:=WilsonOriginalNullColumnSplit.original
    Y₀ S₀ W o P Y law dw pw form paid sForm sPaid registered
  have p0:0≤(R.family.path.levels.params i).columns:=le_trans zero_le_one (R.family.path.levels.params i).columns_ge
  have b0:=rem_nonneg paid
  refine ⟨z,shape,rem_mono fee ?_,null,funext read⟩
  nlinarith only [funded,b0,mul_nonneg p0 b0]

end YM.Integration.WilsonOriginalNullLanding
