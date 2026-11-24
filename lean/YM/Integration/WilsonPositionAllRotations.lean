import YM.GapsContact.Jost.Aligned

/-! Uniform cost of rotating an actual field, on the same physical scaling witnesses.
The original stable comparison uses the purchased Bliss on this table, before the radius,
the orthogonal transformation or the input field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionAllRotations
open Function Filter Set Analysis Spec Table Climb Trace Trace.Pilot Trace.Terrace Trace.Over
open GapsContact GapsContact.Ascent Next.UVStress MergeProof.East Work.A05 Spin TraceExtension
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) {l : Ultrafilter (ℕ × ℕ)} {Z : Arch C} {H : (Bel C.book).Hierarchy}

attribute [local instance] Work.A15.compact_ortho

/-- One scalar pays the genuine physical rotation action on every field at every later radius. -/
theorem cost (hG : G.Simple) (bliss : Bliss F l Z H) (d : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ᶠ r in trail, ∀ (g : Ortho) (x : S.Field d),
      Ascent.cost F d r (F.sector.turns.act d g x) ≤ A * Ascent.cost F d r x := by
  obtain ⟨B,hB,h⟩ := Jost.have_stable F hG bliss d
  let V := circle (compass (C:=C) (H:=H) hG) (LinearEquiv.refl ℂ ((Bel C.book).Field d))
  have hv := circle_cont (compass (C:=C) (H:=H) hG) (LinearEquiv.refl ℂ ((Bel C.book).Field d))
  obtain ⟨g₀,-,hg⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hv.norm.continuousOn
  let D := max 1 ‖V g₀‖
  have hd : 1 ≤ D := le_max_left ..
  have hz (g : Ortho) : ‖V g‖ ≤ D := (hg (Set.mem_univ _)).trans (le_max_right ..)
  refine ⟨B*(D*B),one_le_mul_of_one_le_of_one_le hB (one_le_mul_of_one_le_of_one_le hd hB),?_⟩
  filter_upwards [h] with r ⟨R,hR⟩ g x
  obtain ⟨v,rfl⟩ := R.surjective x
  rw [← hR.align.axis]
  refine (hR.budget (V g v)).trans ?_
  simp only [mul_assoc]
  gcongr
  exact ((V g).le_opNorm v).trans ((mul_le_mul (hz g) (hR.inverse v) (norm_nonneg _) (zero_le_one.trans hd)))

end YM.Integration.WilsonPositionAllRotations
