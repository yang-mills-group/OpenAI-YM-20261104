import YM.Integration.FVA1Physical.Sources.Round2.CurrentBoundary
import YM.Integration.FVA1Physical.Sources.Round2.CrossingTail
import YM.Integration.FVA1Physical.Marked.ExteriorRows

/-! Absolute exterior variation of a genuine scalar coefficient on arbitrary
rough boundaries. Only the distant signed gas remainder survives after
subtracting the physical readouts and reserving the regular support weight. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson Source Labels
open Push.Local Push.AbsoluteSums Push.GridApprox.Attach Next.Foundations
open scoped Classical BigOperators Topology
variable {G:Gauge} {n:Side} {d:ℕ} {F:Frame G d} (R:Rep G n) (Q:Coefficient F n)

private theorem short_reads {X:Support n} {z:Site n} {M r:ℕ} (pin:z∈X)
    (short:coverNumber M X < r) : inspected X ⊆ halo (r*leg M+8) {z} := by
  intro e he
  obtain ⟨s,hs,dist⟩:=halo_spec.mp (Next.Scheduling.flag_layer X he)
  have inside : s∈halo (r*leg M) {z} := by
    by_contra outside
    exact short.not_ge (LocalLTE.Sail.Round2.cover_of_flag_outside pin (mem_singleton_self z) hs outside)
  obtain ⟨a,ha,near⟩:=halo_spec.mp inside
  exact halo_spec.mpr ⟨a,ha,(separation_triangle a s e).trans (Nat.add_le_add near dist)⟩

theorem regular_entry_exterior (z:Site n) (C:SectionData F) {A:Hol G} (shape:Q.Format z A R)
    {κ cost:ℝ} (fund:Q.remBound z R κ cost) (r:ℕ) (U W:Config G n)
    (patch:Agrees (inspected (C.footprint z)) U W)
    (agree:Agrees (halo (r*leg R.p.B+8) {z}) U W) :
    ‖Q.exponentialEntry z C R U-Q.exponentialEntry z C R W‖ ≤
      2*Real.exp (-R.p.supportExponent*r)*cost := by
  have sumU:=(Coefficient.regular_series fund).summable U
  have sumW:=(Coefficient.regular_series fund).summable W
  have fixed:=UsesFinal.allReads R.p.threshold (C.footprint z) _
    (uses_mask R.p.threshold (C.placed_local z (F.scaled R.p.threshold⁻¹ (F.core Q.x)))) U W patch
  obtain ⟨a,b,ha,hb,hcost,_,⟨t,win,spec⟩,_⟩:=fund
  let k:=2*Real.exp (-R.p.supportExponent*r)
  have hk:0 ≤ k := mul_nonneg zero_le_two (Real.exp_nonneg _)
  have cap (i:ℕ) (Y:Config G n) : ‖Q.maskedTerm R i Y‖ ≤ t i := by
    by_cases good:Healthy R.p.threshold (Q.support i) Y
    · rw [Coefficient.maskedTerm,masked_eq _ _ _ _ good]
      exact (spec i).2 Y good [] (Nat.zero_le _) (by simp)
    rw [Coefficient.maskedTerm,masked_ne _ _ _ _ good,norm_zero]
    exact (spec i).1
  have delta:SumBudget (fun i=>‖Q.maskedTerm R i U-Q.maskedTerm R i W‖) (k*a) := by
    apply budget_mono (budget_scale hk win) (fun _=>norm_nonneg _)
    intro i
    by_cases short:coverNumber R.p.B (Q.support i)<r
    · have agreeRow:=UsesFinal.allReads R.p.threshold (Q.support i) _
        (uses_mask R.p.threshold (shape.smooth i).sites) U W (agrees_mono agree (short_reads (shape.origin i) short))
      rw [show Q.maskedTerm R i U=Q.maskedTerm R i W from agreeRow,sub_self,norm_zero]
      exact mul_nonneg hk (win.1 _)
    have far:(r:ℝ) ≤ (coverNumber R.p.B (Q.support i):ℝ):=Nat.cast_le.mpr (le_of_not_gt short)
    have weight:1 ≤ Real.exp (-R.p.supportExponent*r)*Real.exp (R.p.supportExponent*coverNumber R.p.B (Q.support i)) := by
      rw [←Real.exp_add]
      apply Real.one_le_exp
      linarith only [mul_le_mul_of_nonneg_left far R.p.exponent_pos.le]
    have near:‖Q.maskedTerm R i U-Q.maskedTerm R i W‖ ≤ 2*t i :=
      (norm_sub_le ..).trans ((add_le_add (cap i U) (cap i W)).trans_eq (two_mul _).symm)
    apply near.trans
    change _ ≤ (2*Real.exp _)*(Real.exp _*t i)
    nlinarith only [mul_le_mul_of_nonneg_right weight (spec i).1]
  change ‖(Q.x 0+_+∑' i,Q.maskedTerm R i U)-(Q.x 0+_+∑' i,Q.maskedTerm R i W)‖ ≤ _
  rw [fixed,add_sub_add_left_eq_sub,←sumU.tsum_sub sumW]
  exact (norm_tsum_le_tsum_norm delta.2.1).trans (delta.2.2.trans (mul_le_mul_of_nonneg_left (by linarith only [hb,hcost]) hk))

end YM.Integration.FVA1Physical.Round2.Curvature
