import YM.Integration.WilsonPositionScaleLawHome
import YM.Integration.WilsonPhysicalPositionCocycleNative
import YM.Integration.WilsonPositionPrescribedNested
import YM.Integration.WilsonPhysicalPositionUniformBranches

/-! The exact position-calibrated tower respects the original real unit,
signed rotations and every one of the fixed grade inclusions. This gives
actual admissible coordinates on the complete two-home change. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawNative
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize WilsonPositionScaleLawHome
open WilsonPhysicalPositionAdmissible WilsonPhysicalPositionCocycleNative
open WilsonPhysicalPositionBornCandidates (operator record faithful expansion)
open WilsonPhysicalPositionDiscreteBranches (field)
open private one star face from YM.Integration.WilsonPhysicalPositionAdmissible
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)(V:Store G)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

theorem raised (lead:Leading F J){j d:ℕ}(hj:j≤d):∀ᶠr in trail,∀v:E j,
    positioned F J V r d ((scheme C.labels).rise hj v)=
      F.sector.derivatives.rise hj (positioned F J V r j v):=by
  induction d,hj using Nat.le_induction with
  | base=>
    exact .of_forall fun r v=> by
      rw [(scheme C.labels).arrival (Maxwell.table_sym _) (scheme_filters _),
        F.sector.derivatives.arrival F.room.kernel.laws.toSymmetric F.phase.transport.injection]
  | succ d hd ih=>
    filter_upwards [ih,WilsonPositionPrescribedNested.transported F J lead V (positioned F J V)
      (fun j r z v=>congrArg (J r j) (WilsonPositionPrescribedFrame.leg F J V z v)) d] with r lo hi v
    rw [← (scheme C.labels).transit (Maxwell.table_sym _) (scheme_filters _) hd (Nat.le_succ d),hi,lo,
      F.sector.derivatives.transit F.room.kernel.laws.toSymmetric F.phase.transport.injection]

theorem income (lead:Leading F J)(d:ℕ):∀ᶠr in trail,Income F (positioned F J V) d r:=by
  have lower:∀ᶠr in trail,∀j:Fin (d+1),∀v:E j,positioned F J V r d
      ((scheme C.labels).rise (Nat.le_of_lt_succ j.isLt) v)=
        F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt) (positioned F J V r j v):=
    eventually_all.mpr fun _=>raised F J V lead _
  filter_upwards [purchased F J lead d,lower,(WilsonPositionPrescribedScreen.original F J lead V d).2] with r raw lo ok
  let U:=fields C.labels d
  let A:=WilsonPositionPrescribedScreen.correction F J V d r
  let B:=WilsonPositionPrescribedFrame.change F J V d r
  have leg (v:E d):U (B v)=stand A (U v):=by
    obtain ⟨w,rfl⟩:=U.symm.surjective v
    rw [show B (U.symm w)=U.symm (stand A w) from WilsonPositionPrescribedFrame.leg F J V ok.2.1 w,
      U.apply_symm_apply,U.apply_symm_apply]
  have onUnit:B (unit C d)=unit C d:=U.injective (by rw [leg,show U (unit C d)=leaf G d from one C,solitary])
  have onStar(v:E d):B (real C d v)=real C d (B v):=U.injective (by
    rw [leg,show U (real C d v)=reel d (U v) from star C v,
      show U (real C d (B v))=reel d (U (B v)) from star C (B v),leg,stood_reel])
  have onTurns(s:Signed)(v:E d):B (turns C d s v)=turns C d s (B v):=U.injective (by
    rw [leg,show U (turns C d s v)=ori s.ortho d (U v) from face C s v,
      show U (turns C d s (B v))=ori s.ortho d (U (B v)) from face C s (B v),leg,stood_ori])
  refine ⟨?_,⟨?_,?_⟩,fun {j} hj=>lo ⟨j,Nat.lt_succ_of_le hj⟩⟩
  · exact (congrArg (J r d) onUnit).trans raw.neutral
  · intro s v
    exact (congrArg (J r d) (onTurns s v)).trans (raw.real.1 s (B v))
  · intro v
    exact (congrArg (J r d) (onStar v)).trans (raw.real.2 (B v))

theorem positive (t:Ratio):0<t.val:=(show (0:ℝ)<1/2 by norm_num).trans_le t.property.1

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

end YM.Integration.WilsonPositionScaleLawNative
end
