import YM.Integration.WilsonPhysicalPositionBornTransition
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! The original two-sided reflected Wilson income, together with the
normalized position hierarchy, puts *all* possible bounded-ratio limits in
one finite set before the discrete orientation test. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionBornCandidates
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionDiscreteBranches (field preserves)
open WilsonPhysicalPositionBornTransition (present)
open scoped Topology Classical BigOperators
variable {G:Gauge}{d n:ℕ}
local notation "M" => MoveSpace G d

private theorem entry (t:Test n)(p:Fin n→Sec G d):Continuous (fun a:M=>
    reference G d n t (fun j=>field a (p j))):=by
  let Q:=reference G d n t
  let f(a:M)(j:Fin n):=field a (p j)
  have hc (j:Fin n):Continuous (fun a:M=>tableD G d (f a j)):=by
    have eq(a:M):tableD G d (f a j)=tableD G d (p j)+WilsonPhysicalPositionChangePanel.displacement (p j) a:=by
      rw [show f a j=p j+((guide G d).symm a).val (p j) from rfl,map_add]
      rfl
    simp_rw [eq]
    exact continuous_const.add (WilsonPhysicalPositionChangePanel.displacement (p j)).continuous_of_finiteDimensional
  have expand(a:M):Q (f a)=∑z:Fin n→Pin G d,(∏j,tableD G d (f a j) (z j)) • Q (fun j=>Module.finBasis ℝ (Sec G d) (z j)):=
    medium (f a) (Q.restrictScalars ℝ)
  change Continuous (fun a=>Q (f a))
  simp_rw [expand]
  apply continuous_finsetSum
  intro z _
  have hp:Continuous (fun a:M=>∏j,tableD G d (f a j) (z j)):=by
    apply continuous_finsetProd
    intro j _
    exact (continuous_apply (z j)).comp (hc j)
  exact hp.smul (continuous_const (y:=Q (fun j=>Module.finBasis ℝ (Sec G d) (z j))))

theorem closed (G:Gauge)(d:ℕ):IsClosed {b:MoveSpace G d|preserves b}:=by
  have setEq:{b:MoveSpace G d|preserves b}=⋂n:ℕ,⋂t:Test n,⋂p:Fin n→Sec G d,
      {b:MoveSpace G d|reference G d n t (fun j=>field b (p j))=reference G d n t p}:=by
    ext b
    simp only [mem_setOf_eq,mem_iInter]
    constructor
    · intro h n t p
      exact congrArg (fun U:Prediction G d=>U n t p) h
    intro h
    funext n
    exact LinearMap.ext fun t=>MultilinearMap.ext (h n t)
  rw [setEq]
  exact isClosed_iInter fun n=>isClosed_iInter fun t=>isClosed_iInter fun p=>isClosed_eq (entry (n:=n) t p) continuous_const

variable (C:Family G)
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field d

local instance realField (C:Family G)(d:ℕ):NormedSpace ℝ ((Bel C.book).Field d):=
  NormedSpace.restrictScalars ℝ ℂ _

def record (G:Gauge)(C:Family G)(d:ℕ):
    MoveSpace G d→ₗ[ℝ] ((Bel C.book).Field d→L[ℂ] (Bel C.book).Field d) where
  toFun a:=(present (C:=C) ((guide G d).symm a).val).toContinuousLinearMap
  map_add' a b:=by
    ext1 v
    change (fields C.labels d).symm (((guide G d).symm (a+b)).val _)=_
    rw [map_add]
    exact ((fields C.labels d).symm.map_add ..)
  map_smul' s a:=by
    ext1 v
    change (fields C.labels d).symm (((guide G d).symm (s•a)).val _)=_
    rw [map_smul]
    exact ((fields C.labels d).symm.toLinearMap.restrictScalars ℝ).map_smul s _

theorem faithful:Injective (record G C d):=by
  intro a b same
  apply (guide G d).symm.injective
  apply Subtype.ext
  apply LinearMap.ext
  intro p
  have atp:=congrArg (fun T:E→L[ℂ]E=>T ((fields C.labels d).symm p)) same
  change (fields C.labels d).symm (((guide G d).symm a).val ((fields C.labels d) _))=
    (fields C.labels d).symm (((guide G d).symm b).val ((fields C.labels d) _)) at atp
  simpa only [LinearEquiv.apply_symm_apply] using (fields C.labels d).symm.injective atp

def operator (a:M):E→L[ℂ]E:=(present (C:=C) (field a)).toContinuousLinearMap

theorem expansion (a:M):operator C a=ContinuousLinearMap.id ℂ E+record G C d a:=by
  ext1 v
  change (fields C.labels d).symm ((fields C.labels d) v+((guide G d).symm a).val ((fields C.labels d) v))=_
  rw [map_add,LinearEquiv.symm_apply_apply]
  rfl

def possible (C:Family G)(d:ℕ)(B:ℝ):Set (MoveSpace G d):=
  {a|preserves a ∧ ‖operator C a‖≤B ∧ ∀v,‖v‖≤B*‖operator C a v‖}

theorem finite (V:Store G)(d:ℕ)(B:ℝ):(possible C d B).Finite:=by
  let X:=(Bel C.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℂ (X→L[ℂ]X):=ContinuousLinearMap.toNormedSpace
  letI : NormedSpace ℝ (X→L[ℂ]X):=NormedSpace.restrictScalars ℝ ℂ _
  letI : FiniteDimensional ℝ (X→L[ℂ]X):=Module.Finite.trans ℂ (X→L[ℂ]X)
  have hc:Continuous (operator (d:=d) C):=by
    simp_rw [show operator (d:=d) C=fun a=>ContinuousLinearMap.id ℂ ((Bel C.book).Field d)+record G C d a from funext (expansion C)]
    exact continuous_const.add (record G C d).continuous_of_finiteDimensional
  have closed' :IsClosed (possible C d B):=by
    unfold possible
    simp only [Set.setOf_and,Set.setOf_forall]
    apply (closed G d).inter
    apply IsClosed.inter (isClosed_le hc.norm continuous_const)
    apply isClosed_iInter
    intro v
    exact isClosed_le (continuous_const (y:=‖v‖)) ((continuous_const (y:=B)).mul (hc.clm_apply (continuous_const (y:=v))).norm)
  obtain ⟨L,hL⟩:=LinearMap.exists_leftInverse_of_injective (K:=ℝ) (record G C d) (show LinearMap.ker (record G C d)=⊥ from LinearMap.ker_eq_bot.mpr (faithful C))
  let T:=L.toContinuousLinearMap
  have bound:IsCompact (possible C d B):=by
    apply (isCompact_closedBall (0:MoveSpace G d) (‖T‖*(B+‖ContinuousLinearMap.id ℂ ((Bel C.book).Field d)‖))).of_isClosed_subset closed'
    intro a ha
    have ident:T (record G C d a)=a:=DFunLike.congr_fun hL a
    have cost:‖record G C d a‖≤B+‖ContinuousLinearMap.id ℂ ((Bel C.book).Field d)‖:=by
      have diff:record G C d a=operator C a-ContinuousLinearMap.id ℂ ((Bel C.book).Field d):=by rw [expansion];abel
      rw [diff]
      exact (norm_sub_le ..).trans (add_le_add_left ha.2.1 _)
    rw [Metric.mem_closedBall,dist_zero_right,←ident]
    exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left cost (norm_nonneg _))
  apply WilsonPhysicalPositionDiscreteBranches.finite V _ bound (fun _ h=>h.1)
  intro a ha
  have opInject:Injective (operator C a):=by
    intro v w same
    have h:=ha.2.2 (v-w)
    rw [map_sub,same,sub_self,norm_zero,mul_zero] at h
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h)
  intro v w same
  have eq:operator C a ((fields C.labels d).symm v)=operator C a ((fields C.labels d).symm w):=by
    change (fields C.labels d).symm (field a ((fields C.labels d) _))= (fields C.labels d).symm (field a ((fields C.labels d) _))
    simpa only [LinearEquiv.apply_symm_apply] using congrArg (fields C.labels d).symm same
  exact (fields C.labels d).symm.injective (opInject eq)

end YM.Integration.WilsonPhysicalPositionBornCandidates
end
