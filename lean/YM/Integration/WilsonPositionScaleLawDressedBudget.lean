import YM.Integration.WilsonPositionScaleLawDressedTransport
import YM.Integration.WilsonPositionScaleLawDressedGear

/-! The actual homogeneous scale operator is recovered quantitatively from its
two measured position homes. The price is uniform on a whole half panel. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawDressedBudget
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato FVA2 FVA2.Register
open WilsonPositionScaleLawHome (positioned Ratio)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawDressedGear (cap engine)
open WilsonPositionScaleLawDressedTransport (dressed)
open WilsonPositionHomogeneousFrame (homogeneous change)
open WilsonPositionScaleLawWhole (full)
open WilsonPositionScaleLawWholeHome (physical)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    (Z:WilsonPrescription G)(hG:G.Simple)(lead:Leading F J){Y:(Bel R.family.book).Hierarchy}
    (paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

def home (d:ℕ)(r:ℝ):E d→L[ℂ]E d:=(change F J Z d r).toLinearMap.toContinuousLinearMap

include hG lead paid in
theorem two (d:ℕ):∀ᶠr in trail,∀v:E d,‖v‖≤2*‖home F J Z d r v‖ ∧ ‖home F J Z d r v‖≤2*‖v‖:=by
  have hit:=WilsonPositionScaleLawWholeHome.original F J Z hG lead paid d
  filter_upwards [hit,self_mem_nhdsWithin] with r hits hr v
  have hr':0<r:=hr
  let O:=homogeneous F J Z r d v
  obtain ⟨a,b⟩:=hits O
  have f:full F J Z d r O=(r:ℂ)^d • (home F J Z d r v):=by
    change (r:ℂ)^d • (positioned F J Z.store r d).symm (positioned F J Z.store r d (change F J Z d r v))=_
    rw [LinearEquiv.symm_apply_apply];rfl
  have h:physical F J Z d r O=(r:ℂ)^d • v:=by
    change (r:ℂ)^d • (homogeneous F J Z r d).symm (homogeneous F J Z r d v)=_
    rw [LinearEquiv.symm_apply_apply]
  rw [h,f,norm_smul,norm_smul] at a b
  have c:0<‖(r:ℂ)^d‖:=norm_pos_iff.mpr (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr'.ne'))
  constructor
  · by_contra! bad
    have fee:=mul_pos c (sub_pos.mpr bad)
    nlinarith only [a,fee]
  · by_contra! bad
    have fee:=mul_pos c (sub_pos.mpr bad)
    nlinarith only [b,fee]

def residual (d:ℕ)(r:ℝ)(t:Ratio)(D:E d→L[ℂ]E d):E d→L[ℂ]E d:=
  (engine R.family d t).comp ((exactOp F J Z.store d (r,t)).comp (home F J Z d (t.val*r)))-
  (home F J Z d r).comp ((engine R.family d t).comp D)

theorem value (d:ℕ)(r:ℝ)(t:Ratio)(D:E d→L[ℂ]E d)(v:E d):
    home F J Z d r (engine R.family d t ((dressed Z F J d r t-D) v))=residual F J Z d r t D v:=by
  change change F J Z d r (Pert.Scale.gear R.family.labels d t.val (dressed Z F J d r t v-D v))=
    Pert.Scale.gear R.family.labels d t.val (exactOp F J Z.store d (r,t) (change F J Z d (t.val*r) v))-
    change F J Z d r (Pert.Scale.gear R.family.labels d t.val (D v))
  rw [map_sub,map_sub,WilsonPositionScaleLawDressedTransport.original]

include hG lead paid in
theorem original (d:ℕ):∀ᶠr in trail,∀t:Ratio,∀D:E d→L[ℂ]E d,
    ‖dressed Z F J d r t-D‖≤2*cap R.family d*‖residual F J Z d r t D‖:=by
  let X:=E d
  letI :NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  filter_upwards [two F J Z hG lead paid d] with r homePrice t D
  have c:=WilsonPositionScaleLawDressedGear.capPositive (d:=d) R.family
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (by norm_num) c) (norm_nonneg _))
  intro v
  let w:=(dressed Z F J d r t-D) v
  calc
    ‖w‖≤cap R.family d*‖engine R.family d t w‖:=WilsonPositionScaleLawDressedGear.inverse R.family t w
    _≤cap R.family d*(2*‖home F J Z d r (engine R.family d t w)‖):=mul_le_mul_of_nonneg_left (homePrice _).1 c
    _=2*cap R.family d*‖residual F J Z d r t D v‖:=by rw [show home F J Z d r (engine R.family d t w)=_ from value F J Z d r t D v];ring
    _≤2*cap R.family d*(‖residual F J Z d r t D‖*‖v‖):=mul_le_mul_of_nonneg_left ((residual F J Z d r t D).le_opNorm v) (mul_nonneg (by norm_num) c)
    _=_:=by ring

end YM.Integration.WilsonPositionScaleLawDressedBudget
