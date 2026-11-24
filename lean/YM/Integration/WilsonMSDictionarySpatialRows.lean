import YM.Integration.WilsonMSDictionaryPositionCost
import YM.RG17.Tested

/-! Recover the full macroscopic exterior of a moving ultraviolet field from its
 engineering prices. Only the original continuum reader is used, without any
 symmetry or location condition on the positioned scheme. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMSDictionarySpatialRows
open Function Filter Set MeasureTheory Spec Extraction Table OPE OPE.Orbits RG17
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (E : Services C f S) {n : ℕ} (d : Fin n→ℕ) (v : ℝ→Labels S d)

include E in
/-- Collapse the ordinary OPE in the joint signed inner and outer tests. The same compact
 exterior test is fixed before the ultraviolet radius and every retained far cutoff. -/
theorem original (grades : GradePrice Q d v (fun _=>0)) (h : ℕ) (ψ : Test n) (X : External C S)
    {δ : ℝ} (hd : 0<δ) : ∀ᶠ r in home,
    ‖appeared F (v r) X r ψ-X.charge F h (basket Q h (v r) r ψ)‖ ≤
      r^((h:ℝ)+1-δ)*(∫ x : Points (X.n+1), ‖X.test x‖)*(∫ x : Points n, ‖ψ x‖) := by
  obtain ⟨a,ha,offsets⟩ := X.range_open
  let m := ∫ x : Points n, ‖ψ x‖
  let power := (h:ℝ)+1-δ
  have uniform := testedPacketBound Q E v h (fun _=>0) grades ψ.hasCompactSupport ψ.tsupport_subset hd ha X.labels
  have integrable := appearedIntegrable (d:=d) Q E ψ.hasCompactSupport ψ.tsupport_subset X
  filter_upwards [uniform,integrable] with r obs whole
  let w := basket Q h (v r) r ψ
  change ‖(∫ i : Points (X.n+1), X.test i*query F (v r) (X.offset i) X.labels none r ψ)-
    ∫ i : Points (X.n+1), X.test i * X.pay h w i‖ ≤ _
  rw [← integral_sub (whole (v r) ψ (subset_refl _)) (X.pay_integrable F h w)]
  refine (norm_integral_le_of_norm_le (g:=fun i : Points (X.n+1)=>‖X.test i‖*(r^power*m)) ?_ ?_).trans_eq ?_
  · exact (X.test.continuous.integrable_of_hasCompactSupport X.test.hasCompactSupport|>.norm).mul_const _
  · filter_upwards with i
    by_cases hi : i∈tsupport X.test
    · rw [←mul_sub,norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [w,m,power,RG17.External.pay,OPE.spectator,Option.elim,Finset.sum_const_zero,sub_zero] using obs ψ (subset_refl _) (X.offset i) (offsets i hi) none
    · simp [image_eq_zero_of_notMem_tsupport hi]
  rw [integral_mul_const]
  ring

end YM.Integration.WilsonMSDictionarySpatialRows
