import YM.Integration.WilsonReportExteriorBudget
import YM.Comparison.RG02.Cumulants.Split

/-! A separate measured gauge spectator in the connected coarse Wilson law. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter
open scoped BigOperators Classical
namespace YM.Integration.WilsonReportSpectatorModes
open YM YM.Marker YM.Extra.Trajectories YM.Primitives.GCC.Anchor YM.Multi
open YM.Lattice YM.Wilson YM.RG YM.Source
open YM.PhysicalNext.Repeat.Legato YM.OPE
open YM.Comparison.RG02.Cumulants
variable {G : Gauge} {C : Family G} {N p k : ℕ}
variable {V : Type} [DecidableEq V] {Γ : Census (Option V)}

/-- The extra slot is a single original coarse observable. Every coefficient is
integrated on the same Wilson scene before the connected logarithm is taken. -/
def board (Γ : Census (Option V)) (X : Config G (C.side k p) → ℂ)
    (F : V → Config G (C.side k p) → ℂ) : Poly Γ := Poly.inject fun s =>
  ∫ U, (if none ∈ s.val then X U else 1) * ∏ j ∈ s.val.eraseNone, F j U ∂(Therm.scene C.path N p k)

private lemma weights (c : ℂ) (s : Finset (Option V)) :
    ∏ i ∈ s, (if i=none then c else 1) = if none ∈ s then c else 1 := by
  classical
  by_cases h : none ∈ s
  · rw [if_pos h,Finset.prod_eq_single_of_mem none h]
    · simp
    · intro i _ ne
      exact if_neg ne
  · rw [if_neg h]
    refine Finset.prod_eq_one fun i hi => if_neg ?_
    intro e
    exact h (e ▸ hi)

theorem quiet (hC : C.Makes) (hk : k≤N) (X : Config G (C.side k p) → ℂ)
    (F : V → Config G (C.side k p) → ℂ) : (board (N:=N) Γ X F).part Γ.quiet=1 := by
  letI : IsProbabilityMeasure (Therm.scene C.path N p k) := Therm.probability hC.wilson hk
  change (∫ U, (if none ∈ (∅ : Finset (Option V)) then X U else 1) *
    ∏ j ∈ (∅ : Finset (Option V)).eraseNone, F j U ∂(Therm.scene C.path N p k))=1
  simp

private theorem scaled (X Y : Config G (C.side k p) → ℂ)
    (F : V → Config G (C.side k p) → ℂ) (c : ℂ)
    (same : X =ᵐ[Therm.scene C.path N p k] fun U => c * Y U) :
    board (N:=N) Γ X F = dilation Γ (fun i => if i=none then c else 1) (board (N:=N) Γ Y F) := by
  classical
  ext s
  rw [dilation_part,weights]
  change (∫ U, (if none ∈ s.val then X U else 1) * ∏ j ∈ s.val.eraseNone, F j U ∂_) =
    (if none ∈ s.val then c else 1) *
    (∫ U, (if none ∈ s.val then Y U else 1) * ∏ j ∈ s.val.eraseNone, F j U ∂_)
  by_cases h : none ∈ s.val
  · simp only [h,if_true]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [same] with U eq
    rw [eq,mul_assoc]
  · simp [h]

/-- Exact linear homogeneity in the separately introduced, occupied spectator slot.
Other mutually excluded slots are retained by the actual Census. -/
theorem linear [Fintype V] (hC : C.Makes) (hk : k≤N) (s : Γ.Mode) (hs : none ∈ s.val)
    (X Y : Config G (C.side k p) → ℂ) (c : ℂ)
    (same : X =ᵐ[Therm.scene C.path N p k] fun U => c * Y U)
    (F : V → Config G (C.side k p) → ℂ) :
    (connected (board (N:=N) Γ X F)).part s = c * (connected (board (N:=N) Γ Y F)).part s := by
  classical
  rw [scaled X Y F c same,← log_map _ (quiet_dilation _) (quiet hC hk Y F),dilation_part,weights,if_pos hs]

/-- Normalize the actual spectator in the same positive coarse probability, including
zero measured mass. Neither the exterior nor its absolute value is a new probability. -/
theorem normalized (X : Config G (C.side k p) → ℂ) (hX : Integrable X (Therm.scene C.path N p k)) :
    ∃ Y : Config G (C.side k p) → ℂ, Integrable Y (Therm.scene C.path N p k) ∧
      (∫ U, ‖Y U‖ ∂(Therm.scene C.path N p k))≤1 ∧
      X =ᵐ[Therm.scene C.path N p k] fun U =>
        ((∫ Z, ‖X Z‖ ∂(Therm.scene C.path N p k) : ℝ) : ℂ)*Y U := by
  let μ := Therm.scene C.path N p k
  let L := ∫ U, ‖X U‖ ∂μ
  have hL : 0≤L := integral_nonneg fun _ => norm_nonneg _
  by_cases h : L=0
  · refine ⟨0,integrable_zero _ _ _,by simp,?_⟩
    have hz := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun U => norm_nonneg (X U)) hX.norm).mp h
    filter_upwards [hz] with U eq
    simpa using norm_eq_zero.mp eq
  let Y := fun U => ((L:ℂ)⁻¹)*X U
  refine ⟨Y,hX.const_mul _,?_,?_⟩
  · change (∫ U, ‖(L:ℂ)⁻¹ * X U‖ ∂μ) ≤ 1
    simp only [norm_mul, integral_const_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
    exact le_of_eq (inv_mul_cancel₀ h)
  · apply Eventually.of_forall
    intro U
    change X U = (L:ℂ)*((L:ℂ)⁻¹*X U)
    rw [←mul_assoc,mul_inv_cancel₀ (show (L:ℂ)≠0 by exact_mod_cast h),one_mul]

end YM.Integration.WilsonReportSpectatorModes
