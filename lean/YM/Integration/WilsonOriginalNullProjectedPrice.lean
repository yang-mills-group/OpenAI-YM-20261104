import YM.Integration.WilsonOriginalNullAppointments
import YM.Integration.WilsonMeasuredSectionCorrection

/-! Counted measured projection on a real returning carrier, uniformly in
period and origin. The wrapped displacement is counted only after summing
its true original rows. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullProjectedPrice
open Filter Lattice Wilson RG Source Labels Extra.Histories Trace.Physical Trace.Physical.Germ
open PhysicalNext Repeat Legato Graces Roost Org Push.Local
open scoped Classical Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "F₀" => R.family.labels.level d
local notation "frames₀" => R.family.params
local notation "wrap₀" => (germ_close F₀ frames₀).choose

/-- The full measured projection of the lower source pays at most one extra
copy of its divisible residual bill. This includes wrapping sheets. -/
theorem original (simple:G.Simple) : ∀ᶠ i:ℕ in atTop, ∀ (per:ℕ)
    (W:Rep G (R.family.side i per)), W.p=R.family.path.levels.budget i →
    ∀ (o:Site (R.family.side i per)) (P:Coefficient F₀ (R.family.side i per)) {κ b:ℝ},
      P.Format o frames₀ W → P.remBound o W κ b → d ≤ W.p.order → d ≤ W.p.power →
      let π₁:=projection F₀ frames₀ W.p.threshold o P
      (F₀).coeffSize (π₁-P.x) ≤ b ∧ (F₀).coeffSize π₁ ≤ (F₀).coeffSize P.x+b := by
  let K:=(Fintype.card (F₀).Index:ℝ)*wrap₀
  have hg:= (germ_close F₀ frames₀).choose_spec.1.le
  have hk:0 ≤ K:=mul_nonneg (Nat.cast_nonneg _) hg
  filter_upwards [R.family.S.divergent.eventually_ge_atTop K,GermGraph.cut_flat R.family simple (-1)]
    with i far discount per W budget o P κ b shape paid order power
  intro π₁
  let T:=R.family.S.scale i
  have hcoef : ‖π₁-P.x‖ ≤ wrap₀*wraps W.p (R.family.side i per)*b :=
    (germ_close F₀ frames₀).choose_spec.2 W P shape paid order power
  have bill:=rem_nonneg paid
  have hwrap : wraps W.p (R.family.side i per) ≤ (Real.exp T)⁻¹ := by
    rw [budget];simpa only [T,neg_one_mul,Real.exp_neg] using discount per
  have base : K ≤ Real.exp T:= by have h:=Real.add_one_le_exp T;linarith only [far,h]
  have low : K*wraps W.p (R.family.side i per) ≤ 1 := by
    refine (mul_le_mul_of_nonneg_left hwrap hk).trans ?_
    rw [←div_eq_mul_inv];exact (div_le_one (Real.exp_pos _)).mpr base
  have count : (F₀).coeffSize (π₁-P.x) ≤ b := calc
    _ ≤ (Fintype.card (F₀).Index :ℝ)*‖π₁-P.x‖ := Size.le_norm F₀ _
    _ ≤ K*wraps W.p (R.family.side i per)*b := by
      have h:=mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg (Fintype.card (F₀).Index))
      exact h.trans_eq (by dsimp only [K];ring)
    _ ≤ b := by simpa only [one_mul] using mul_le_mul_of_nonneg_right low bill
  exact ⟨count,
    calc
      _ = (F₀).coeffSize (P.x+(π₁-P.x)) := by rw [add_sub_cancel]
      _ ≤ _ := (Size.add F₀ _ _).trans (add_le_add le_rfl count)⟩

end YM.Integration.WilsonOriginalNullProjectedPrice
