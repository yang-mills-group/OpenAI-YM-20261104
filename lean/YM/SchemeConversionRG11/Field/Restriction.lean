import YM.SchemeConversionRG11.Field.Horizon

/-!
# The nested finite flag of field-increment operators

Surjectivity of restriction matters for constructing square, nested position tests.
Again these act on the on-shell Wick symbols, not BRST lifts.
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Horizon

open Function Pert.Position Pert.Rigid
variable {G : Gauge} (F : Labels.Frames G) {d e k : ℕ}

/-- The restriction is actually defined by inclusion intertwining. -/
theorem restrict_calc (he : d ≤ e) (B : Buffer F e) (v : E F d) :
    incl F he (cut F d e (B.val (incl F he v))) = B.val (incl F he v) := by
  rcases lt_or_eq_of_le he with h|h
  · have hl : incl F he v ∈ lower F d e := by rw [← incl_range F he]; exact ⟨v,rfl⟩
    have hh := B.property.2.1 _ h _ hl
    rw [← incl_range F he] at hh
    obtain ⟨w, hw⟩ := hh
    rw [← hw, cut_incl]
  subst d
  apply Eq.trans (incl_self ..)
  rw [incl_self]
  exact (congrArg (cut F e e) (incl_self F (B.val v)).symm).trans (cut_incl F le_rfl (B.val v))

private def rest {d e : ℕ} (h : d ≤ e) (B : Buffer F e) : operator F d :=
  (((cut F d e).restrictScalars ℝ).toContinuousLinearMap).comp
    (B.val.comp (((incl F h).restrictScalars ℝ).toContinuousLinearMap))

private lemma restricting (h : d ≤ e) (B : Buffer F e) : rest F h B ∈ buffers F d := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change cut F d e (B.val (incl F h _)) = 0
    rw [incl_unit, B.property.1, map_zero]
  · intro j hj p hp
    rw [← incl_range F hj.le] at hp ⊢
    obtain ⟨v, rfl⟩ := hp
    have hl := restrict_calc F (hj.le.trans h) B v
    refine ⟨cut F j e (B.val (incl F (hj.le.trans h) v)), ?_⟩
    apply incl_injective F h
    change incl F h (incl F hj.le (cut F j e (B.val (incl F (hj.le.trans h) v)))) =
      incl F h (cut F d e (B.val (incl F h (incl F hj.le v))))
    rw [incl_repeat F, hl, restrict_calc F, incl_repeat F]
  · intro p
    change bar F d (cut F d e (B.val (incl F h p))) = cut F d e (B.val (incl F h (bar F d p)))
    rw [incl_bar, ← cut_bar]
    exact congrArg _ (B.property.2.2.1 _)
  · intro s p
    change Extra.FD.rideO F s.ortho d (cut F d e (B.val (incl F h p))) =
      cut F d e (B.val (incl F h (Extra.FD.rideO F s.ortho d p)))
    rw [incl_rotate, ← cut_rotate]; exact congrArg _ (B.property.2.2.2.1 _ _)
  intro p
  change cut F d e (B.val (incl F h (Complex.I • p))) = Complex.I • cut F d e (B.val (incl F h p))
  rw [map_smul, dispatch_cmul, map_smul]

/-- Continuous (at each finite horizon) restriction. -/
def restr (h : d ≤ e) : Buffer F e →L[ℝ] Buffer F d := by
  let L : Buffer F e →ₗ[ℝ] Buffer F d := {
    toFun := fun B ↦ ⟨_, restricting F h B⟩
    map_add' := by
      intro x y; apply Subtype.ext; apply ContinuousLinearMap.ext; intro p; apply map_add (((cut F d e).restrictScalars ℝ))
    map_smul' := by
      intro c y; apply Subtype.ext; apply ContinuousLinearMap.ext; intro p; apply map_smul (((cut F d e).restrictScalars ℝ)) }
  exact LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Buffer F e) (F' := Buffer F d) L

theorem restrictions (h : d ≤ e) (B : Buffer F e) (v : E F d) :
    incl F h ((restr F h B).val v) = B.val (incl F h v) := restrict_calc F h B v

theorem motors (h : d ≤ e) (B : Buffer F e) (v : E F d) :
    incl F h (motor F (restr F h B) v) = motor F B (incl F h v) := by
  change incl F h (v + (restr F h B).val v) = _ + _
  rw [map_add, restrictions]; rfl

theorem restr_self (u : Buffer F d) : restr F le_rfl u = u := by
  apply Subtype.ext; apply ContinuousLinearMap.ext; intro p
  simpa [incl_self F (d := d)] using restrictions F le_rfl u p

theorem restr_compose (h : d ≤ e) (k' : e ≤ k) (B : Buffer F k) :
    restr F h (restr F k' B) = restr F (h.trans k') B := by
  apply Subtype.ext; apply ContinuousLinearMap.ext; intro v; apply incl_injective F (h.trans k')
  rw [restrictions, ← incl_repeat, ← incl_repeat F h k' v, restrictions, restrictions]

section Surj
variable (h : d ≤ e)

private def prolong (A : Buffer F d) : operator F e :=
  (((incl F h).restrictScalars ℝ).toContinuousLinearMap).comp
    (A.val.comp (((cut F d e).restrictScalars ℝ).toContinuousLinearMap))

private theorem prod_prolong (A : Buffer F d) : prolong F h A ∈ buffers F e := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change incl F h (A.val (cut F d e _)) = 0
    rw [← incl_unit F h, cut_incl, A.property.1, map_zero]
  · intro j hj p hp
    change incl F h (A.val (cut F d e p)) ∈ _
    rw [← incl_range F hj.le] at hp ⊢
    rcases lt_or_ge j d with he | he
    · obtain ⟨v,rfl⟩ := hp
      rw [← incl_repeat F he.le h, cut_incl, ← restrictions F he.le A, incl_repeat]
      exact ⟨_,rfl⟩
    exact ⟨incl F he (A.val (cut F d e p)), incl_repeat F he hj.le _⟩
  · intro p; change bar F e (incl F h (A.val (cut F d e p))) = incl F h (A.val (cut F d e (bar F e p)))
    rw [← incl_bar, cut_bar]; exact congrArg _ (A.property.2.2.1 _)
  · intro s p
    change Extra.FD.rideO F s.ortho e (incl F h (A.val (cut F d e p))) =
      incl F h (A.val (cut F d e (Extra.FD.rideO F s.ortho e p)))
    rw [← incl_rotate, cut_rotate]; exact congrArg _ (A.property.2.2.2.1 _ _)
  intro p; change incl F h (A.val (cut F d e (Complex.I • p))) = Complex.I • incl F h (A.val (cut F d e p))
  rw [map_smul, dispatch_cmul, map_smul]

theorem restr_surjective : Function.Surjective (restr F h) := by
  intro A
  refine ⟨⟨prolong F h A, prod_prolong F h A⟩, ?_⟩
  apply Subtype.ext; apply ContinuousLinearMap.ext; intro p
  apply incl_injective F h
  rw [restrictions]; change incl F h (A.val (cut F d e (incl F h p))) = _
  rw [cut_incl F h]
end Surj
end YM.SchemeConversionRG11.Horizon
