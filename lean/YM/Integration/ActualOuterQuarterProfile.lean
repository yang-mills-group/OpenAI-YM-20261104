import YM.Integration.ActualCoarseQuarterProfile

/-!
Generic outer profiles on the original ordered regulator filter.
The outer level and theta may vary arbitrarily with the outer datum.
The bank estimate and authentication to an effective action remain explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOuterQuarterProfile

open Filter Lattice
open scoped Topology

abbrev Cutoffs (I : Type) := I × (ℕ × ℕ)

def nested {I : Type} (l : Filter I) (f : Extraction.Order) : Filter (Cutoffs I) :=
  l.curry f.fuse

def lengths {I : Type} (S : Schedule) (level : I → ℕ) (w : Cutoffs I) : Side :=
  ActualCoarseQuarterProfile.halfSide S (level w.1) w.2.2

def profile {I : Type} (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a) (μ : ℝ) :
    MS.Rake.Geo (Cutoffs I) where
  θ w := θ w.1
  η w := μ - θ w.1
  room w := hθ w.1

private theorem side_tendsto (S : Schedule) (m : ℕ) :
    Tendsto (fun p => ((S.side m p).val : ℝ)) atTop atTop := by
  have h : StrictMono (fun p => (S.side m p).val) := by
    intro a b hab
    change (S.period a).val * (S.denominator m).val <
      (S.period b).val * (S.denominator m).val
    exact Nat.mul_lt_mul_of_pos_right (S.period_strict hab) (S.denominator m).property
  exact tendsto_natCast_atTop_atTop.comp h.tendsto_atTop

theorem theta_tendsto {I : Type} (l : Filter I) (f : Extraction.Order)
    (θ : I → ℝ) (hθ : Tendsto θ l atTop) :
    Tendsto (fun w : Cutoffs I => θ w.1) (nested l f) atTop := by
  apply tendsto_atTop.2
  intro b
  change ∀ᶠ a in l, ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop, b ≤ θ a
  exact (hθ.eventually (eventually_ge_atTop b)).mono
    (fun a ha => Eventually.of_forall fun _ => Eventually.of_forall fun _ => ha)

/-- No inner-cutoff dependence or positivity of theta is needed for Super. -/
theorem super {I : Type} (S : Schedule) (l : Filter I) (f : Extraction.Order)
    (level : I → ℕ) (θ : I → ℝ) :
    MS.Tide.Super (nested l f) (lengths S level) (fun w => θ w.1) := by
  intro h
  have he : ∀ w : Cutoffs I,
      MS.Vista.tickA (lengths S level) w = ((S.side (level w.1) w.2.2).val : ℝ) := by
    intro w
    change ((MS.Orbit.periodN
      (ActualCoarseQuarterProfile.halfSide S (level w.1) w.2.2)).val : ℝ) = _
    rw [ActualCoarseQuarterProfile.dimension]
  simp_rw [he]
  change ∀ᶠ a in l, ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop,
    h * θ a ≤ Real.log ((S.side (level a) (f.per k)).val : ℝ)
  exact Eventually.of_forall fun a =>
    ((Real.tendsto_log_atTop.comp (side_tendsto S (level a))).comp f.per.cofinal).eventually
      (eventually_ge_atTop (h * θ a)) |>.mono
        (fun k hk => Eventually.of_forall fun _ => hk)

/-- The full native bank bound is a premise, not a consequence of geometry. -/
theorem nearPlan_of_bank {I : Type} (S : Schedule) (l : Filter I) (f : Extraction.Order)
    (level : I → ℕ) (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a) (μ : ℝ)
    (hdiv : Tendsto θ l atTop) (V : MS.Vista.Visa (Cutoffs I))
    (hbank : ∃ A : ℝ, ∀ᶠ w in nested l f, V.bank w ≤ Real.exp (A * θ w.1)) :
    MS.Tide.NearPlan (nested l f) (profile θ hθ μ) V (lengths S level) μ := by
  refine ⟨theta_tendsto l f θ hdiv, super S l f level θ, ?_, hbank⟩
  intro w
  rfl

theorem eventually_legal {I : Type} (l : Filter I) (f : Extraction.Order)
    (level : I → ℕ) :
    ∀ᶠ w : Cutoffs I in nested l f, level w.1 ≤ w.2.1 := by
  change ∀ᶠ a in l, ∀ᶠ k : ℕ in atTop, ∀ᶠ j : ℕ in atTop,
    level a ≤ f.mesh j
  exact Eventually.of_forall fun a => Eventually.of_forall fun _ =>
    f.mesh.cofinal.eventually (eventually_ge_atTop (level a))

end YM.Integration.ActualOuterQuarterProfile
end
