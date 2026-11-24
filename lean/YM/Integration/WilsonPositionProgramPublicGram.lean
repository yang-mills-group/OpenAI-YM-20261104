import YM.Integration.WilsonMatrixTicketLanesSmearedPivot

/-! The Gram and signed measurements of the actual compact determining tests,
on a full finite public horizon in its original engineering normalization. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicGram
open Filter RG Spec PhysicalNext.Repeat.Legato PhysMS Climb Next.UVStress Trace.Pilot
open Matrix WilsonMatrixTicketLanesSmearedPivot WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : FVA2.Register.WilsonPrescription G)
    {d : ℕ}

def samples (B : Profiles R d) (r : ℝ) :
    (Climb.Bel R.family.book).Field d →ₗ[ℂ] (B.probes.index → ℂ) :=
  (row F J Z B r).comp (homogeneous F J Z r d).toLinearMap

def square {I : Type*} [Fintype I] (v : I → ℂ) : ℝ := ∑ i, ‖v i‖^2

theorem dominates {I : Type*} [Fintype I] (v : I → ℂ) : ‖v‖^2 ≤ square v := by
  have pos : 0 ≤ square v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have point (i : I) : ‖v i‖^2 ≤ square v := Finset.single_le_sum
    (f:=fun j => ‖v j‖^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h : ‖v‖ ≤ Real.sqrt (square v) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    exact (Real.le_sqrt (norm_nonneg _) pos).mpr (point i)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (Real.sq_sqrt pos)

theorem original {Y : (Climb.Bel R.family.book).Hierarchy}
    (lead : Leading F J) (paid : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) (d : ℕ) :
    ∃ B : Profiles R d, ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in trail,
      (∀ x y, ‖x-y‖ ≤ K * ‖samples F J Z B r x - samples F J Z B r y‖) ∧
      (∀ x, ‖x‖^2 ≤ K^2 * square (samples F J Z B r x)) ∧
      Function.Injective (samples F J Z B r) := by
  obtain ⟨B,K,pos,event⟩ := WilsonMatrixTicketLanesSmearedPivot.original F J Z lead paid simple d
  refine ⟨B,K,pos,?_⟩
  filter_upwards [event] with r hr
  have bar (x : (Climb.Bel R.family.book).Field d) : ‖x‖ ≤ K * ‖samples F J Z B r x‖ := by
    change ‖x‖ ≤ K * ‖(WilsonMatrixTicketLanesSmearedPivot.row F J Z B r) (homogeneous F J Z r d x)‖
    simpa only [LinearEquiv.symm_apply_apply] using hr (homogeneous F J Z r d x)
  have signed (x y) := bar (x-y)
  refine ⟨fun x y => ?_,fun x => ?_,fun x y eq => ?_⟩
  · simpa only [map_sub] using signed x y
  · calc
      _ ≤ (K*‖samples F J Z B r x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (bar x) 2
      _ = K^2 * ‖samples F J Z B r x‖^2 := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (dominates _) (sq_nonneg K)
  · have b := signed x y
    rw [map_sub,eq,sub_self,norm_zero,mul_zero] at b
    exact sub_eq_zero.mp (norm_le_zero_iff.mp b)

end YM.Integration.WilsonPositionProgramPublicGram
