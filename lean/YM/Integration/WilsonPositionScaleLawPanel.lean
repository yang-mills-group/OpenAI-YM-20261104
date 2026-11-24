import YM.Integration.WilsonPositionScaleLawJacobian

/-! The declared survey is exactly linear in its entire numerical bank after
fixing the slot correction. Its bank operator has one bound over the closed
unit ball of corrections, independently of the measured or proposed bank. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawPanel
open Function Filter Set Metric XSpace XSpace.Normalize
open scoped Topology Classical BigOperators
variable {G:Gauge}{d:ℕ}{A:Screen G d}(D:Fray A)

private def account (a:MoveSpace G d):D.Bag→ₗ[ℝ]MoveSpace G d where
  toFun x:=D.itinerary (x,a)
  map_add' x y:=by
    rw [Fray.itinerary,Fray.itinerary,Fray.itinerary,←map_add]
    congr 1;funext i
    simp [Pi.add_apply,smul_add,Finset.sum_add_distrib]
  map_smul' c x:=by
    rw [Fray.itinerary,Fray.itinerary,RingHom.id_apply,←map_smul]
    congr 1;funext i
    simp only [Pi.smul_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl;intro j _;exact smul_comm _ _ _

theorem original :∃L:ℝ,0≤L ∧ ∀a:MoveSpace G d,‖a‖≤ 1→∀x y:D.Bag,
    ‖D.itinerary (x,a)-D.itinerary (y,a)‖≤L*‖x-y‖:=by
  let K:=Metric.closedBall (0:D.At) 1
  obtain ⟨L,hL⟩:= (isCompact_closedBall (0:D.At) 1).bddAbove_image D.fair.continuous.norm.continuousOn
  refine ⟨max 0 L,le_max_left _ _,?_⟩
  intro a ha x y
  let B:=account D a
  have test (u:D.Bag)(hu:‖u‖≤ 1):‖B u‖≤ max 0 L:=by
    have hit:(u,a)∈K:=mem_closedBall_zero_iff.mpr (max_le hu ha)
    exact (hL (mem_image_of_mem _ hit)).trans (le_max_right _ _)
  change ‖B x-B y‖≤_
  rw [←B.map_sub]
  by_cases h:x-y=0
  · simp [h]
  have nz:‖x-y‖≠0:=norm_ne_zero_iff.mpr h
  let u:=(‖x-y‖⁻¹:ℝ) • (x-y)
  have hu:‖u‖≤ 1:=by simp [u,norm_smul,nz]
  have recovers:‖x-y‖ • u=x-y:=by simp [u,smul_smul,nz]
  calc
    ‖B (x-y)‖=‖B (‖x-y‖ • u)‖:=congrArg (fun z=>‖B z‖) recovers.symm
    _=‖x-y‖*‖B u‖:=by simp [norm_smul]
    _≤ max 0 L*‖x-y‖:=(mul_le_mul_of_nonneg_left (test u hu) (norm_nonneg _)).trans_eq (mul_comm _ _)

end YM.Integration.WilsonPositionScaleLawPanel
end
