import YM.Integration.WilsonPositionScaleLawBooked
import YM.Integration.WilsonPositionScaleLawInclusion

/-! Descent of the genuine measured two-home branch along each fixed physical filtration inclusion. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardNest
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPhysicalPositionUniformBranches (change)
open WilsonPositionScaleLawCompactNative (positive bothHomes)
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "E"=>(Bel C.book).Field

theorem faithful {d k:ℕ}(h:d≤k):Injective ((scheme C.labels).rise h):=by
  intro x y eq
  apply (fields C.labels d).injective
  apply Subtype.ext
  exact ((address_rise C.labels k h x).symm.trans (congrArg (address C.labels k) eq)).trans (address_rise C.labels k h y)

theorem natural [RangeSpec] (lead:Leading F J){d k:ℕ}(h:d≤k):∀ᶠz:ℝ×Ratio in sweep,∀v:E d,
    change J k z.1 z.2.val (positive z.2) ((scheme C.labels).rise h v)=
      (scheme C.labels).rise h (change J d z.1 z.2.val (positive z.2) v):=by
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually (lead.raised h),bothHomes.eventually (lead.raised h)] with z near far v
  let t:=z.2.val
  let r:=z.1
  have ht:0<t:=positive z.2
  apply (Pert.Scale.gearIso C.labels k t ht).injective
  apply (J r k).injective
  change J r k (Pert.Scale.gear C.labels k t (Frame.cocycle k J r t ht ((scheme C.labels).rise h v)))=
    J r k (Pert.Scale.gear C.labels k t ((scheme C.labels).rise h (Frame.cocycle d J r t ht v)))
  rw [Frame.cocycle_value,RG12.Roof.gear_rises,near,Frame.cocycle_value,far]

private def fold {X V:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][FiniteDimensional ℂ X]
    [NormedAddCommGroup V][NormedSpace ℂ V](put:X→ₗ[ℂ]V)(back:V→ₗ[ℂ]X):(V→L[ℂ]V)→ₗ[ℂ](X→L[ℂ]X) where
  toFun:=fun A=>(back.comp (A.toLinearMap.comp put)).toContinuousLinearMap
  map_add':=fun A B=>by ext v;exact back.map_add _ _
  map_smul':=fun s A=>by ext v;exact back.map_smul _ _

theorem original [RangeSpec] (lead:Leading F J){d k:ℕ}(h:d≤k)(selected:WilsonPositionScaleLawCompactBranch.Raw J k):
    WilsonPositionScaleLawCompactBranch.Raw J d:=by
  let put: E d→ₗ[ℂ]E k:=(scheme C.labels).rise h
  letI :NormedAddCommGroup (E d→L[ℂ]E d):=ContinuousLinearMap.toNormedAddCommGroup
  letI :NormedAddCommGroup (E k→L[ℂ]E k):=ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨back,undo⟩:=put.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (faithful h))
  let cut:=fold put back
  have one:cut (ContinuousLinearMap.id ℂ (E k))=ContinuousLinearMap.id ℂ (E d):=by
    ext v;exact DFunLike.congr_fun undo v
  have full: Tendsto (fun z:ℝ×Ratio=>cut (change J k z.1 z.2.val (positive z.2))) sweep (𝓝 (cut (ContinuousLinearMap.id ℂ (E k)))):=
    (cut.continuous_of_finiteDimensional.continuousAt.tendsto).comp selected
  rw [one] at full
  apply full.congr'
  filter_upwards [natural F J lead h] with z eq
  ext v
  change back (change J k z.1 z.2.val (positive z.2) ((scheme C.labels).rise h v))=change J d z.1 z.2.val (positive z.2) v
  rw [eq]
  exact DFunLike.congr_fun undo _

end YM.Integration.WilsonPositionScaleLawGuardNest
