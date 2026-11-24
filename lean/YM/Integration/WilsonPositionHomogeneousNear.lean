import YM.Integration.WilsonPositionHomogeneousRealization

/-! Actual invertible field changes at sufficiently small (measured) real
coupling. Extension by the identity on the unused nonpositive half-line
allows the basis to be defined before the interacting first slope is paid. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionHomogeneousNear
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register FVA2.Scale
open WilsonPositionHomogeneousCoefficients
open scoped Topology BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G)

def field (d : ℕ) (t : ℝ) : Change G d := if 0<t then WilsonPositionHomogeneousRealization.correction Z d t else 0

theorem near (d : ℕ) : Tendsto (fun t=>guide G d (field Z d t)) (𝓝 0) (𝓝 0) := by
  obtain ⟨A,hA,h⟩:=WilsonPositionHomogeneousRealization.expansion Z d 0
  have fee : ∀ᶠ t : ℝ in 𝓝[>] 0,‖guide G d (WilsonPositionHomogeneousRealization.correction Z d t)‖≤A*t := by
    simpa [letter] using h
  have gate := eventually_nhdsWithin_iff.mp fee
  apply squeeze_zero_norm' (a:=fun t:ℝ=>A*|t|) _ _
  · filter_upwards [gate] with t bound
    by_cases hp:0<t
    · rw [field,if_pos hp,abs_of_pos hp]
      exact bound hp
    rw [field,if_neg hp,map_zero,norm_zero]
    exact mul_nonneg hA (abs_nonneg _)
  · have small : Continuous (fun t : ℝ=>A*|t|) := by fun_prop
    simpa using small.tendsto 0

theorem invertible (d : ℕ) : ∀ᶠ t : ℝ in 𝓝 0,Bijective (stand (field Z d t)) := by
  filter_upwards [(near Z d).eventually (Fray.safe_pegs (G:=G) (d:=d))] with t hot
  simpa only [Fray.box,LinearEquiv.symm_apply_apply] using hot

theorem diagonal (H : Warrant Z) (d : ℕ) (t : ℝ) : Level.diag (stand (field Z d t))=1 := by
  by_cases hp:0<t
  · rw [field,if_pos hp];exact WilsonPositionHomogeneousRealization.diagonal Z H d hp
  rw [field,if_neg hp,stand0,Level.diagonal_one]

theorem includes (H:Warrant Z) {d e : ℕ} (h:d≤e) (t:ℝ) (v:Sec G d) :
    stand (field Z e t) (up h v)=up h (stand (field Z d t) v) := by
  by_cases hp:0<t
  · simp only [field,if_pos hp];exact WilsonPositionHomogeneousRealization.includes Z H h hp v
  simp only [field,if_neg hp,stand0,Module.End.one_apply]

/-- Asymptotic along the positive coupling axis used by the MS prescription. -/
theorem expansion (d q:ℕ) :
    ∃ A : ℝ,0≤A ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖guide G d (field Z d t)-∑n∈range (q+1),t^n • guide G d (letter Z d n)‖≤A*t^(q+1) := by
  obtain ⟨A,hA,h⟩:=WilsonPositionHomogeneousRealization.expansion Z d q
  refine ⟨A,hA,?_⟩
  filter_upwards [h,self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0)] with t ht hp
  simpa only [field,if_pos (show 0<t from hp)] using ht

end YM.Integration.WilsonPositionHomogeneousNear

