import YM.PhysMS.Frame.Cost

/-! A strict engineering gap absorbs the subpower loss in the original physical frame. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryGradeMargins
open Filter Set Spec OPE OPE.Levy Trace.Pilot
open scoped Topology

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)

private lemma inversePower {r : ℝ} (hr : 0 < r) (d : ℕ) :
    Real.exp ((d:ℝ) * LogV r) = (r ^ d)⁻¹ := by
  rw [LogV, Real.exp_nat_mul, Real.exp_log (inv_pos.mpr hr), inv_pow]

include H

/-- Exact dimensional inlet growth for a fixed field that comes from a strictly lower
    horizon. The two frames are compared by the actual `rise` map on the final quotient. -/
theorem lowerInlet {e d : ℕ} (hed : e < d) (x : S.Field e) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r in trail,
      r ^ d * ‖(J r d).symm (F.sector.derivatives.rise hed.le x)‖ ≤ A := by
  let I := ((Maxwell.Free.scheme C.labels).rise hed.le).toContinuousLinearMap
  refine ⟨‖I‖ * ‖x‖, by positivity, ?_⟩
  have growth := PhysMS.Frame.inverse_rate F e J H (d:ℝ) (by exact_mod_cast hed)
  filter_upwards [growth, H.raised hed.le, self_mem_nhdsWithin] with r hg hrise hr
  have hpos : 0 < r := hr
  have hp := pow_pos hpos d
  have hrev : (J r d).symm (F.sector.derivatives.rise hed.le x) =
      I ((J r e).symm x) := by
    apply (J r d).injective
    rw [LinearEquiv.apply_symm_apply]; change _ = J r d ((Maxwell.Free.scheme C.labels).rise hed.le _)
    rw [hrise, LinearEquiv.apply_symm_apply]
  rw [hrev]; rw [inversePower hpos d] at hg
  have hinner : ‖(J r e).symm x‖ ≤ (r^d)⁻¹ * ‖x‖ :=
    ((PhysMS.Frame.backward e J r).le_opNorm x).trans (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
  calc
    r^d * ‖I ((J r e).symm x)‖ ≤ r^d * (‖I‖ * ((r^d)⁻¹ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left ((I.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hinner (norm_nonneg _))) hp.le
    _ = ‖I‖ * ‖x‖ := by field_simp

/-- Exact dimensional outlet growth at weight `w` for a physical row annihilating
    the grade `w` as well as every lower grade. -/
theorem higherOutlet {w d : ℕ} (hwd : w < d) (L : S.Field d →L[ℂ] ℂ)
    (kill : ∀ x ∈ planeAt (U:=F.sector.derivatives) (w+1) hwd, L x = 0) :
    ∀ᶠ r in trail, ‖PhysMS.Frame.pulling d J L r‖ ≤ r^w := by
  have hg := PhysMS.Frame.upper F d J H (w+1) hwd L kill (-(w:ℝ)) (by push_cast; linarith)
  filter_upwards [hg, self_mem_nhdsWithin] with r hv hr
  have hp : 0 < r := hr
  rwa [neg_mul, Real.exp_neg, inversePower hp w, inv_inv] at hv

end YM.Integration.WilsonOrdinaryGradeMargins
