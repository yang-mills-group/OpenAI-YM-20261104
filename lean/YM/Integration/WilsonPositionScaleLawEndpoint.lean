import YM.Integration.WilsonPositionScaleLawFixed

/-! A single intermediate ratio costs a fixed factor on the actual fixed-field
column, uniformly in both the ratio and the physical field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawEndpoint
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register FVA2.Scale
open WilsonPositionScaleLawHome (positioned Ratio sweep)
open WilsonPositionScaleLawNative (exactOp positive)
open WilsonPositionScaleLawGrade (grade lift reads)
open WilsonPositionScaleLawFixed (top)
open private peak respects from YM.Integration.WilsonPositionScaleLawFixed
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

def column (d:ℕ)(r:ℝ)(O:S.Field d):E d:=(r:ℂ)^d • grade R.family (top d) ((positioned F J Z.store r d).symm O)

private theorem triangular (lead:Leading F J)(d:ℕ):∀ᶠz in sweep,∀v:E d,
    grade R.family (top d) (exactOp F J Z.store d z v)=
      grade R.family (top d) (exactOp F J Z.store d z (grade R.family (top d) v)):=by
  filter_upwards [WilsonPositionScaleLawNative.realizes F J Z.store lead d] with z hu v
  rw [←hu]
  apply (fields R.family.labels d).injective
  let a:=WilsonPositionScaleLawNative.coordinates F J Z.store d z
  let A:=WilsonPhysicalPositionDiscreteBranches.field a
  change fields R.family.labels d (grade R.family (top d) (lift R.family A v))=
    fields R.family.labels d (grade R.family (top d) (lift R.family A (grade R.family (top d) v)))
  rw [reads,reads,reads,reads,reads]
  exact peak (respects a) _

theorem balance (lead:Leading F J)(d:ℕ):∀ᶠz in sweep,∀O:S.Field d,
    column F J Z d z.1 O=grade R.family (top d) (exactOp F J Z.store d z (column F J Z d (z.2.val*z.1) O)):=by
  let T:=positioned F J Z.store
  let P:=grade R.family (top d)
  filter_upwards [triangular F J Z lead d] with z same O
  let r:=z.1
  let t:=z.2
  let U:=exactOp F J Z.store d z
  let v:=(T (t.val*r) d).symm O
  have atHome:(T r d).symm O=Pert.Scale.gear R.family.labels d t.val (U v):=by
    apply (T r d).injective
    change T r d ((T r d).symm O)=T r d (Pert.Scale.gear R.family.labels d t.val (Frame.cocycle d T r t.val (positive t) v))
    rw [Frame.cocycle_value,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  change (r:ℂ)^d • P ((T r d).symm O)=P (U ((↑(t.val*r):ℂ)^d • P v))
  rw [atHome,U.map_smul,P.map_smul,WilsonPositionScaleLawFixed.engineering,smul_smul,Complex.ofReal_mul,mul_pow,mul_comm ((t.val:ℂ)^d)]
  exact congrArg ((↑r^d*(↑t.val:ℂ)^d) • ·) (same v)

private theorem pure (d:ℕ)(r:ℝ)(O:S.Field d):grade R.family (top d) (column F J Z d r O)=column F J Z d r O:=by
  rw [column,map_smul,WilsonPositionScaleLawFixed.idempotent]

private theorem debit {X I:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]{l:Filter I}
    {A:I→X→L[ℂ]X}(P:X→L[ℂ]X)(near:Tendsto A l (𝓝 (ContinuousLinearMap.id ℂ X))):
    ∀ᶠz in l,‖P‖*‖A z-ContinuousLinearMap.id ℂ X‖≤1/2:=by
  have small:=tendsto_iff_norm_sub_tendsto_zero.mp near
  have bill: Tendsto (fun z=>‖P‖*‖A z-ContinuousLinearMap.id ℂ X‖) l (𝓝 (‖P‖*0)):=
    (tendsto_const_nhds (x:=‖P‖)).mul small
  rw [mul_zero] at bill
  exact ((tendsto_order.mp bill).2 _ (by norm_num)).mono fun _ h=>h.le

theorem original (lead:Leading F J)(d:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d):
    ∀ᶠr in trail,∀t:Ratio,∀O:S.Field d,
      ‖column F J Z d (t.val*r) O‖≤2*‖column F J Z d r O‖ ∧
      ‖column F J Z d r O‖≤2*‖column F J Z d (t.val*r) O‖:=by
  let P:=grade R.family (top d)
  let U:=exactOp F J Z.store d
  let I:=ContinuousLinearMap.id ℂ (E d)
  have near:Tendsto U sweep (𝓝 I):=WilsonPositionScaleLawBranch.transferred F J Z.store lead d raw
  have charged:=debit P near
  obtain ⟨p,hp,q,hq,all⟩:=Filter.eventually_prod_iff.mp (charged.and (balance F J Z lead d))
  filter_upwards [hp] with r hr t O
  obtain ⟨small,recur⟩:=all hr (Filter.eventually_top.mp hq t)
  let x:=column F J Z d (t.val*r) O
  let y:=column F J Z d r O
  let A:=U (r,t)
  have eq:y-x=P ((A-I) x):=by
    change y-x=P (A x-x)
    rw [P.map_sub,show P x=x from pure F J Z _ _ _,show y=P (A x) from recur O]
  have price:‖y-x‖≤(1/2:ℝ)*‖x‖:=by
    rw [eq]
    calc
      _≤‖P‖*‖(A-I) x‖:=P.le_opNorm _
      _≤‖P‖*(‖A-I‖*‖x‖):=mul_le_mul_of_nonneg_left ((A-I).le_opNorm _) P.opNorm_nonneg
      _≤_:=by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right small (norm_nonneg _)
  have xy:=norm_sub_norm_le x y
  have yx:=norm_sub_norm_le y x
  rw [norm_sub_rev x y] at xy
  change ‖x‖≤2*‖y‖ ∧ ‖y‖≤2*‖x‖
  constructor <;> linarith [norm_nonneg x]

end YM.Integration.WilsonPositionScaleLawEndpoint
end
