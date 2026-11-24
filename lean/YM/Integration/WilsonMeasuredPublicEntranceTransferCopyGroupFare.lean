import YM.Integration.WilsonOriginalPublicTrialPhaseGroup

/-! Per-tile restoration of the actual occupied names on the replicated board. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyGroupFare
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu MergeProof.Float Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Ribbons Ribbons.Fibers Ribbons.ManyCopies Further.ShellBirth49.Fusing
open scoped Topology ContDiff BigOperators Classical

open WilsonOriginalPublicTrialPhaseGroup (wage)
variable {V I:Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]

theorem original (i:I) (v:V) (w:V×I→ℝ) (z a:ℝ) (l:ℕ) :
    wage i w z a l ((),v)=∏ t:I,(a/(Fintype.card I:ℝ)*w (v,t))/Real.exp ((z+1/2)*l):=by
  unfold wage
  rw [contentP,Finset.prod_image (fun _ _ _ _ h=> (Prod.mk.inj h).2)]
  rw [contentF,Finset.prod_image (fun _ _ _ _ h=> (Prod.mk.inj h).2)]
  rfl

/-- Regrouping scales with the finite number of fields inside a copy. -/
theorem inverse (i:I) (v:V) (w:V×I→ℝ) (z a B:ℝ) (l:ℕ) (ap:0<a)
    (wp:∀t,0<w (v,t)) (actual:∀t,(w (v,t))⁻¹≤B):
    (wage i w z a l ((),v))⁻¹≤
      ((Fintype.card I:ℝ)*a⁻¹*B*Real.exp ((z+1/2)*l))^(Fintype.card I):=by
  have card:0<(Fintype.card I:ℝ):=by exact_mod_cast (Fintype.card_pos_iff.mpr ⟨i⟩)
  have exp:=Real.exp_pos ((z+1/2)*l)
  rw [original,←Finset.prod_inv_distrib]
  calc
    _≤∏ _t:I,(Fintype.card I:ℝ)*a⁻¹*B*Real.exp ((z+1/2)*l):=by
      apply Finset.prod_le_prod
      · intro t _;exact (inv_pos.mpr (div_pos (mul_pos (div_pos ap card) (wp t)) exp)).le
      · intro t _
        rw [show ((a/(Fintype.card I:ℝ)*w (v,t))/Real.exp ((z+1/2)*l))⁻¹=
            ((Fintype.card I:ℝ)*a⁻¹)*(w (v,t))⁻¹*Real.exp ((z+1/2)*l) by
          simp only [div_eq_mul_inv,mul_inv_rev,inv_inv];ring]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (actual t) (by positivity)) exp.le
    _=_:=by simp

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyGroupFare
