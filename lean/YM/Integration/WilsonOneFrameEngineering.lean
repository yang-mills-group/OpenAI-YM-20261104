import YM.Integration.WilsonOneFramePhysicalPivot
import YM.PhysMS.Frame.Cost

/-! Graded forward and inverse bounds on the final, measured Wilson frame. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOneFrameEngineering
open Filter Function Set Lattice Wilson RG Source Table Spec Extraction OPE OPE.Levy Climb Trace.Pilot PhysMS RG17
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open WilsonMacroscopicRichTwoDatePivot (active)
open scoped Topology Classical

private lemma powerBound {T : Type*} [Norm T] {f : ℝ → T} {a : ℝ}
    (h : RateLE trail LogV f a) (δ : ℝ) (pos : 0 < δ) :
    ∀ᶠ r : ℝ in trail, ‖f r‖ ≤ r ^ (-a - δ) := by
  filter_upwards [h (a+δ) (by linarith), self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r bound hr
  apply bound.trans_eq
  rw [LogV, Real.log_inv, Real.rpow_def_of_pos hr]
  congr 1
  ring

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Spec.Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}

theorem original (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) (d e : ℕ) (he : e ≤ d) (φ : S.Field d →L[ℂ] ℂ)
    (kills : ∀ p ∈ planeAt (U := F.sector.derivatives) e he, φ p = 0) (δ : ℝ) (pos : 0 < δ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail,
      (∀ v : RG17.Free R.family d, ‖φ (homogeneous F J Z r d v)‖ ≤ A * r^((e:ℝ)-δ) * ‖v‖) ∧
      (∀ u : S.Field d, ‖(homogeneous F J Z r d).symm u‖ ≤ 2 * r^(-(d:ℝ)-δ) * ‖u‖) := by
  obtain ⟨A,apos,near⟩ := WilsonOneFramePhysicalPivot.original F J Z lead owed simple d
  have forward := powerBound (Frame.upper F d J lead e he φ kills) δ pos
  have reverse := powerBound (Frame.inverse_rate F d J lead) δ pos
  refine ⟨A,apos,?_⟩
  filter_upwards [near,forward,reverse,self_mem_nhdsWithin (s := Ioi (0:ℝ))] with r close upper lower hr
  rw [neg_neg] at upper
  constructor
  · intro v
    let w := active F J Z r d v
    have placed : J r d w = homogeneous F J Z r d v := (J r d).apply_symm_apply _
    rw [←placed]
    calc
      _ ≤ ‖Frame.pulling d J φ r‖ * ‖w‖ := (Frame.pulling d J φ r).le_opNorm w
      _ ≤ r^((e:ℝ)-δ) * (A * ‖v‖) :=
        mul_le_mul upper (close v).1 (norm_nonneg _) (Real.rpow_nonneg hr.le _)
      _ = _ := by ring
  · intro u
    let w := (J r d).symm u
    have placed : (active F J Z r d).symm w = (homogeneous F J Z r d).symm u := by
      change (homogeneous F J Z r d).symm (J r d ((J r d).symm u)) = _
      rw [LinearEquiv.apply_symm_apply]
    rw [←placed]
    calc
      _ ≤ 2 * ‖w‖ := (close w).2
      _ ≤ 2 * (r^(-(d:ℝ)-δ) * ‖u‖) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact ((Frame.backward d J r).le_opNorm u).trans
          (mul_le_mul_of_nonneg_right lower (norm_nonneg _))
      _ = _ := by ring

end YM.Integration.WilsonOneFrameEngineering
end
