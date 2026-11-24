import YM.Integration.WilsonCenteredNestedShadowBasis

/-! Uniform action of the one genuinely elected compact rotation group
on the original field spaces and on the signed input coefficient mass. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRotation
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Prescription OPE.Log WilsonCenteredNestedShadowBasis
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable {I : Type} [Fintype I] {d : I→ℕ}
attribute [local instance] YM.Work.A15.compact_ortho

include Q in
lemma inputs (v : Labels S d) : ∃D : ℝ,0 ≤ D ∧ ∀ k : Ortho,mass (roll F.sector.turns k v) ≤ D := by
  have cont : Continuous (fun k : Ortho => mass (roll F.sector.turns k v)) := by
    apply continuous_finsetSum
    intro t _
    apply Continuous.norm
    apply continuous_finsetProd
    intro i _
    change Continuous (fun k : Ortho=> ((Module.finBasis ℂ (S.Field (d i))).coord (t i)) (F.sector.turns.act (d i) k (v i)))
    exact ((Module.finBasis ℂ (S.Field (d i))).coord (t i)).continuous_of_finiteDimensional.comp (Q.law.spin _ _)
  obtain ⟨D,all⟩ := isCompact_univ.exists_bound_of_continuousOn cont.continuousOn
  refine ⟨max D 0,le_max_right _ _,fun k=>?_⟩
  exact (le_abs_self _).trans ((all k (mem_univ k)).trans (le_max_left _ _))

include Q in
lemma output (h : ℕ) : ∃D : ℝ,0 ≤ D ∧ ∀(k:Ortho)(v:S.Field h),‖F.sector.turns.act h k v‖ ≤ D*‖v‖ := by
  let b := Module.finBasis ℂ (S.Field h)
  have bank (j : Fin (Module.finrank ℂ (S.Field h))) : ∃B:ℝ,0 ≤ B ∧ ∀k : Ortho,‖F.sector.turns.act h k (b j)‖ ≤ B := by
    obtain ⟨B,all⟩ := isCompact_univ.exists_bound_of_continuousOn (Q.law.spin h (b j)).continuousOn
    exact ⟨max B 0,le_max_right _ _,fun k=>(all k (mem_univ k)).trans (le_max_left _ _)⟩
  choose B Bn bound using bank
  let L j := (b.coord j).toContinuousLinearMap
  refine ⟨∑ j,‖L j‖*B j,Finset.sum_nonneg fun j _=>mul_nonneg ((L j).opNorm_nonneg) (Bn j),?_⟩
  intro k v
  have id : F.sector.turns.act h k v = ∑ j,b.repr v j • F.sector.turns.act h k (b j) := by
    conv_lhs => rw [←b.sum_repr v]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _=>(F.sector.turns.act h k).map_smul _ _)
  rw [id,Finset.sum_mul]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum fun j _=>?_)
  rw [norm_smul]
  calc
    ‖b.repr v j‖ * ‖F.sector.turns.act h k (b j)‖ ≤ (‖L j‖ * ‖v‖) * B j :=
      mul_le_mul ((L j).le_opNorm v) (bound j k) (norm_nonneg _) (mul_nonneg (L j).opNorm_nonneg (norm_nonneg _))
    _ = _ := by ring

omit [Fintype I] in
lemma moved {r M η : ℝ} {x : I→E4} {o : E4} (fit : WithinRoom r M η x o) (k : Ortho) :
    WithinRoom r M η (Ortho.move k ∘x) (Ortho.move k o) := by
  constructor
  · intro i
    change ‖Ortho.motion k (x i) - Ortho.motion k o‖ ≤ _
    rw [←map_sub]
    change ‖Ortho.move k (x i-o)‖ ≤ _
    rw [Ortho.move_norm];exact fit.span i
  · intro i j off
    change _ ≤ ‖Ortho.motion k (x i) - Ortho.motion k (x j)‖
    rw [←map_sub]
    change _ ≤ ‖Ortho.move k (x i-x j)‖
    rw [Ortho.move_norm];exact fit.spaced i j off

lemma packet (h : ℕ) (x : I→E4) (v : Labels S d) (o : E4) (k : Ortho) :
    Q.packet h (Ortho.move k ∘x) (roll F.sector.turns k v) (Ortho.move k o) = F.sector.turns.act h k (Q.packet h x v o) := by
  unfold Reader.packet
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _=>?_
  rw [Q.rotate_fresh,Q.law.filtered]

end YM.Integration.WilsonCenteredNestedRotation
