import YM.Integration.WilsonPositionScaleLawNative
import YM.Integration.WilsonPositionScaleLawWindow

/-! Exact original calibrated cocycle and true finite position equations on a general positive ratio window. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactNative
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawHome (bank positioned engineering)
open WilsonPositionScaleLawNative (income)
open WilsonPhysicalPositionAdmissible WilsonPhysicalPositionCocycleNative
open WilsonPhysicalPositionBornCandidates (operator record faithful expansion)
open WilsonPhysicalPositionDiscreteBranches (field)
open private one star face from YM.Integration.WilsonPhysicalPositionAdmissible
open scoped Topology Classical BigOperators
variable [Win:RangeSpec] {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

theorem positive (t:Ratio):0<t.val:=Win.positive.trans_le t.property.1

theorem bothHomes : Tendsto (fun z:ℝ×Ratio=>z.2.val*z.1) sweep trail:=by
  let u:=fun z:ℝ×Ratio=>z.2.val*z.1
  have hr:Tendsto (fun z:ℝ×Ratio=>z.1) sweep trail:=tendsto_fst
  have hrpos:=hr.eventually (self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0))
  have hp:∀ᶠz in sweep,0<u z:=hrpos.mono fun z hz=>mul_pos (positive z.2) hz
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨squeeze_zero' (hp.mono fun _ h=>h.le) ?_ (hr.mono_right nhdsWithin_le_nhds),hp⟩
  exact hrpos.mono fun z hz=>mul_le_of_le_one_left hz.le z.2.property.2

def exactOp (d:ℕ)(z:ℝ×Ratio):E d→L[ℂ]E d:=
  WilsonPhysicalPositionUniformBranches.change (positioned F J V) d z.1 z.2.val (positive z.2)

def coordinates (d:ℕ)(z:ℝ×Ratio):MoveSpace G d:=
  if h:∃a:MoveSpace G d,operator C a=exactOp F J V d z then h.choose else 0

theorem realizes (lead:Leading F J)(d:ℕ):∀ᶠz in sweep,
    operator C (coordinates F J V d z)=exactOp F J V d z:=by
  have hr:Tendsto (fun z:ℝ×Ratio=>z.1) sweep trail:=tendsto_fst
  filter_upwards [hr.eventually (income F J V lead d),bothHomes.eventually (income F J V lead d)] with z h k
  obtain ⟨a,idA⟩:=WilsonPhysicalPositionAdmissible.coordinates C
    (WilsonPhysicalPositionCocycleNative.original F (positioned F J V) (positive z.2) h k)
  have existsA:∃a:MoveSpace G d,operator C a=exactOp F J V d z:=
    ⟨a,ContinuousLinearMap.ext fun v=>congrArg (fun L:E d→ₗ[ℂ]E d=>L v) idA⟩
  rw [coordinates,dif_pos existsA]
  exact existsA.choose_spec

theorem exactEquation (lead:Leading F J)(d:ℕ):∀ᶠz in sweep,
    let P:=bank F J V d z.1 z.2.val
    let a:=coordinates F J V d z
    recruit (field a) P=WilsonPositionPrescribedScreen.hierarchy F (positioned F J V) d (z.2.val*z.1):=by
  let U:=fields C.labels d
  let H:=positioned F J V
  have hp:∀ᶠ z in sweep,0<z.1:=tendsto_fst.eventually RG17.positiveLength
  filter_upwards [realizes F J V lead d,hp] with z hz hr
  let t:=z.2.val
  let r:=z.1
  let a:=coordinates F J V d z
  have p:0<t:=positive z.2
  have card(v:E d):U.symm (field a (U v))=Frame.cocycle d H r t p v:=
    congrArg (fun L:E d→L[ℂ]E d=>L v) hz
  have identify:engineering (C:=C) d t ∘ₗ field a=(WilsonPhysicalPositionHomeDilation.arm H r (r*t) d).toLinearMap:=by
    apply LinearMap.ext;intro v
    obtain ⟨w,rfl⟩:=U.surjective v
    apply U.symm.injective
    apply (H r d).injective
    change H r d (U.symm (U (Pert.Scale.gear C.labels d t (U.symm (field a (U w))))))=_
    rw [U.symm_apply_apply,card,Frame.cocycle_value]
    change H (t*r) d w=H r d (U.symm (WilsonPhysicalPositionHomeDilation.arm H r (r*t) d (U w)))
    rw [WilsonPhysicalPositionHomeDilation.paid_at_home]
    change H (t*r) d w=H (r*t) d (U.symm (U w))
    rw [U.symm_apply_apply,mul_comm]
  dsimp only
  change recruit (field a) (recruit (engineering (C:=C) d t) (WilsonPhysicalPositionHomeDilation.samples F H r t d))=_
  rw [recruits_comp,identify,←WilsonPhysicalPositionHomeDilation.full F H hr p,mul_comm]

end YM.Integration.WilsonPositionScaleLawCompactNative
end
