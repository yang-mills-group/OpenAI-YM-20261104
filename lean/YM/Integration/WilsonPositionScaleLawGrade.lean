import YM.Integration.WilsonPositionScaleLawQinter
import YM.Integration.WilsonPositionScaleLawUnits

/-! The measured bounded-ratio scale operator on each actual grade has no
linear coupling term. The fixed grade projection is transported by the exact
Maxwell fields; its diagonal error is quadratic at each dyadic step. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGrade
open Function Filter Set Finset PowerSeries Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawIndependent (B trial letter)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawQinter (prediction measured)
open WilsonPhysicalPositionBornCandidates (record expansion)
open scoped Topology BigOperators Classical Asymptotics
variable {G:Gauge}(C:Family G){d:ℕ}
set_option quotPrecheck false
local notation "E"=> (Bel C.book).Field

abbrev lift (A:FieldEnd G d):E d→L[ℂ]E d:=(WilsonPhysicalPositionBornTransition.present (C:=C) A).toContinuousLinearMap
abbrev grade (i:Fin (d+1)):=lift C (Level.proj i)

theorem reads (A:FieldEnd G d)(x:E d):fields C.labels d (lift C A x)=A (fields C.labels d x):=
  (fields C.labels d).apply_symm_apply _

def cut (i:Fin (d+1)):(E d→L[ℂ]E d)→ₗ[ℝ](E d→L[ℂ]E d) where
  toFun A:=(grade C i).comp (A.comp (grade C i))
  map_add' A B:=by ext1 x;exact (grade C i).map_add _ _
  map_smul' c A:=by ext1 x;exact (grade C i).map_smul_of_tower c _

variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

def coeffOp (j:ℕ)(s:ℝ):E d→L[ℂ]E d:=record G C d (guide G d (letter Z M ν d j s))

include H in
theorem first (s:ℝ)(i:Fin (d+1)):cut C i (coeffOp C Z M ν 0 s)=0:=by
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have no:Level.diag (coeff 1 (B Z M ν s d))=0:=Generator.Q.horizonX ν Z.scheme Z.criterion M σ s hG data.Taylor data.still data.base
  ext1 x
  apply (fields C.labels d).injective
  change fields C.labels d (lift C (Level.proj i) (lift C (((guide G d).symm (guide G d (letter Z M ν d 0 s))).val)
    (lift C (Level.proj i) x)))=fields C.labels d 0
  rw [reads,reads,reads,map_zero,LinearEquiv.symm_apply_apply,WilsonPositionScaleLawIndependent.filled Z M H ν,
    ←Level.diagonals,no];rfl

include H in
theorem second (s g:ℝ)(i:Fin (d+1)):
    cut C i (WilsonPhysicalPositionBornCandidates.operator C (trial Z M ν d 2 s g)-ContinuousLinearMap.id ℂ (E d))=
      g^2 • cut C i (coeffOp C Z M ν 1 s):=by
  have terms:trial Z M ν d 2 s g=g • guide G d (letter Z M ν d 0 s)+g^2 • guide G d (letter Z M ν d 1 s):=by
    simp [trial,Finset.sum_range_succ]
  rw [expansion,terms,add_sub_cancel_left,map_add,map_smul,map_smul,map_add,map_smul,map_smul]
  change g • cut C i (coeffOp C Z M ν 0 s)+_=_
  rw [first C Z M H ν]
  ext1 x;change g • (0:E d)+_=_;rw [smul_zero,zero_add];rfl

def half:Ratio:=⟨1/2,le_rfl,by norm_num⟩

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)

include H lead paid in
theorem quadratic (i:Fin (d+1))(t:Ratio)(raw:WilsonPositionScaleLawBranch.Raw J d)
    (observed:(measured Z M ν F J d 2)=o[sweep] (fun z=>kinetic Z F J z.1^2)):
    ∃K:ℝ,0≤K ∧ ∀ᶠr in trail,‖cut R.family i (exactOp F J Z.store d (r,t)-
      ContinuousLinearMap.id ℂ ((Bel R.family.book).Field d))‖≤K*kinetic Z F J r^2:=by
  let X:=(Bel R.family.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  let P: (X→L[ℂ]X)→L[ℝ](X→L[ℂ]X):=(cut R.family i).toContinuousLinearMap
  let I:=ContinuousLinearMap.id ℂ X
  let s:=WilsonPositionScaleLawIndependent.time t
  let A:=P (coeffOp R.family Z M ν 1 s)
  have pin:Tendsto (fun r:ℝ=>(r,t)) trail sweep:=tendsto_id.prodMk tendsto_top
  have h:=WilsonPositionScaleLawQinter.qinter Z M H ν F J lead paid d 2 raw observed
  refine ⟨‖P‖+‖A‖,add_nonneg (norm_nonneg _) (norm_nonneg _),?_⟩
  filter_upwards [pin.eventually (Asymptotics.isLittleO_iff.mp h zero_lt_one)] with r hr
  let U:=exactOp F J Z.store d (r,t)
  let V:=prediction Z M ν F J d 2 (r,t)
  let g:=kinetic Z F J r
  have small:‖U-V‖≤g^2:=by
    change ‖U-V‖≤1*‖g^2‖ at hr
    simpa only [Real.norm_eq_abs,abs_of_nonneg (_root_.sq_nonneg g),one_mul] using hr
  have fixed:P (V-I)=g^2 • A:=second R.family Z M H ν s g i
  have total:U-I=(U-V)+(V-I):=by abel
  change ‖P (U-I)‖≤(‖P‖+‖A‖)*g^2
  rw [total,P.map_add,fixed]
  refine (norm_add_le _ _).trans ((add_le_add ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left small (norm_nonneg _))) le_rfl).trans_eq ?_)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (_root_.sq_nonneg g)];ring

end YM.Integration.WilsonPositionScaleLawGrade
end
