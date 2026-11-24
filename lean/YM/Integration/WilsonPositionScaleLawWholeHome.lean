import YM.Integration.WilsonPositionScaleLawWhole

/-! Two-sided comparison of all coordinates of the original named position
tower and its genuine precomputed homogeneous Borel frame at the measured coupling. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawWholeHome
open Function Filter Set Spec Table Extraction OPE Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open WilsonPhysicalPositionBornCandidates (operator record expansion)
open WilsonPhysicalPositionDiscreteBranches (field)
open WilsonPositionHomogeneousFrame (homogeneous change turn)
open WilsonPositionScaleLawWhole (full)
open private leg from YM.Integration.WilsonPositionHomogeneousFrame
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

def physical (d:ℕ)(r:ℝ)(O:S.Field d):E d:=(r:ℂ)^d • (homogeneous F J Z r d).symm O

private theorem bilateral {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X](B:X≃ₗ[ℂ]X)(A:X→L[ℂ]X)
    (fit:∀u,B u=u+A u)(small:‖A‖≤1/2)(x:X):‖B.symm x‖≤2*‖x‖ ∧ ‖x‖≤2*‖B.symm x‖:=by
  let u:=B.symm x
  have eq:x=u+A u:=by rw [←fit,B.apply_symm_apply]
  have cost:‖A u‖≤(1/2)*‖u‖:=(A.le_opNorm _).trans (mul_le_mul_of_nonneg_right small (norm_nonneg _))
  have f:‖x‖≤‖u‖+‖A u‖:=by simpa only [←eq] using norm_add_le u (A u)
  have b:‖u‖≤‖x‖+‖A u‖:=by
    calc _=‖x-A u‖:=congrArg _ (eq ▸ (add_sub_cancel_right u (A u)).symm)
         _≤_:=norm_sub_le ..
  change ‖u‖≤2*‖x‖ ∧ ‖x‖≤2*‖u‖
  exact ⟨by linarith,by linarith [norm_nonneg u]⟩

theorem originalOperator {d:ℕ}{r:ℝ}(h:Bijective (stand (turn F J Z d r)))(x:E d):
    change F J Z d r x=x+record G R.family d (guide G d (turn F J Z d r)) x:=by
  let Q:=turn F J Z d r
  have same:change F J Z d r x=operator R.family (guide G d Q) x:=by
    obtain ⟨v,rfl⟩:=(fields R.family.labels d).symm.surjective x
    rw [leg F J Z h]
    change (fields R.family.labels d).symm (stand Q v)=(fields R.family.labels d).symm (field (guide G d Q) (fields R.family.labels d ((fields R.family.labels d).symm v)))
    simp only [LinearEquiv.apply_symm_apply,field,LinearEquiv.symm_apply_apply]
  rw [same,expansion];rfl

variable (hG:G.Simple)(lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
include hG lead paid in
theorem original (d:ℕ):∀ᶠr in trail,∀O:S.Field d,
    ‖physical F J Z d r O‖≤2*‖full F J Z d r O‖ ∧ ‖full F J Z d r O‖≤2*‖physical F J Z d r O‖:=by
  let X:=E d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI :NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI :NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  let V:MoveSpace G d→L[ℝ](X→L[ℂ]X):=(record G R.family d).toContinuousLinearMap
  have g:=WilsonPositionPrescribedZero.measured F J Z.store lead paid hG Z.criterion
  have near:Tendsto (fun r=>guide G d (turn F J Z d r)) trail (𝓝 0):=(WilsonPositionHomogeneousNear.near Z d).comp g
  have small:Tendsto (fun r=>‖V (guide G d (turn F J Z d r))‖) trail (𝓝 0):=by
    simpa only [map_zero,norm_zero] using! ((V.continuous.tendsto (0:MoveSpace G d)).comp near).norm
  have room:=((tendsto_order.mp small).2 _ (by norm_num : (0:ℝ)<1/2)).mono fun _ h=>h.le
  filter_upwards [room,g.eventually (WilsonPositionHomogeneousNear.invertible Z d)] with r bill good O
  let B:=change F J Z d r
  let x:=full F J Z d r O
  have exact:physical F J Z d r O=B.symm x:=by
    change (r:ℂ)^d • B.symm _=B.symm ((r:ℂ)^d • _)
    rw [B.symm.map_smul];rfl
  rw [exact]
  exact bilateral B (V (guide G d (turn F J Z d r))) (originalOperator F J Z good) bill x

end YM.Integration.WilsonPositionScaleLawWholeHome
end
