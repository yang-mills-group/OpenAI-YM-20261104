import YM.Integration.WilsonPositionScaleLawGuardQuadratic

/-! Exact original physical and MS scale equality, at all orders, on the genuine unit of every retained horizon. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardUnit
open Function Filter Set Spec Table Extraction Climb PhysMS Trace.Pilot Maxwell Maxwell.Free XSpace XSpace.Normalize
open OPE OPE.Orbits PhysicalNext.Repeat.Legato MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawDressedTransport (dressed guard)
open WilsonPositionScaleLawGuardSheet (atValue)
open WilsonPositionScaleLawGuardLift (pack)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics Polynomial
variable {G:Gauge}

theorem named (C:Family G)(d:ℕ):fields C.labels d ((Bel C.book).unit d)=leaf G d:=Subtype.ext (unit_address C.labels d)

theorem seat (C:Family G)(d:ℕ)(a:Change G d)(h:Bijective (stand a)):
    ((fields C.labels d).trans ((LinearEquiv.ofBijective (stand a) h).trans (fields C.labels d).symm)) ((Bel C.book).unit d)=(Bel C.book).unit d:=by
  apply (fields C.labels d).injective
  change fields C.labels d ((fields C.labels d).symm (stand a (fields C.labels d ((Bel C.book).unit d))))=_
  rw [LinearEquiv.apply_symm_apply,named,solitary]

variable {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field
local notation "unit"=> (Bel R.family.book).unit

theorem positioned (d:ℕ)(r:ℝ):WilsonPositionPrescribedFrame.change F J Z.store d r (unit d)=unit d:=by
  unfold WilsonPositionPrescribedFrame.change
  split
  · exact seat R.family d _ _
  · rfl

theorem moving (d:ℕ)(r:ℝ):WilsonPositionHomogeneousFrame.change F J Z d r (unit d)=unit d:=by
  unfold WilsonPositionHomogeneousFrame.change
  split
  · exact seat R.family d _ _
  · rfl

theorem original (lead:Leading F J)(d:ℕ):∀ᶠz:ℝ×Ratio in sweep,dressed Z F J d z.1 z.2 (unit d)=unit d:=by
  let T:=WilsonPositionHomogeneousFrame.homogeneous F J Z
  have home:∀ᶠr in trail,T r d (unit d)=S.unit d:=by
    filter_upwards [lead.unit d] with r chosen
    change J r d (WilsonPositionPrescribedFrame.change F J Z.store d r (WilsonPositionHomogeneousFrame.change F J Z d r (unit d)))=S.unit d
    rw [moving,positioned,chosen]
  letI :WilsonPositionScaleLawWindow.RangeSpec:=⟨1/2,by norm_num⟩
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually home,WilsonPositionScaleLawCompactNative.bothHomes.eventually home] with z near far
  let t:=z.2.val
  have ht:0<t:=WilsonPositionScaleLawNative.positive z.2
  apply (Pert.Scale.gearIso R.family.labels d t ht).injective
  apply (T z.1 d).injective
  change T z.1 d (Pert.Scale.gear R.family.labels d t (Frame.cocycle d T z.1 t ht (unit d)))=T z.1 d (Pert.Scale.gear R.family.labels d t (unit d))
  rw [Frame.cocycle_value,Pert.Scale.gear_unit,near,far]

variable (C:Family G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
include H in
theorem independent (s:ℝ)(d q:ℕ)(z:ℂ):atValue q (pack C (guard Z M ν s d)) z ((Bel C.book).unit d)=(Bel C.book).unit d:=by
  let g:=guard Z M ν s d
  let a:=pack C g
  let u:=(Bel C.book).unit d
  let data:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have base:Base g:=GroupS.true_N ν Z.scheme Z.criterion M σ hG data.Taylor data.still data.base s
  have one:coeff 0 a=1:=by dsimp only [a];rw [WilsonPositionScaleLawGuardLift.pack,PowerSeries.coeff_map,base.zero,map_one]
  have high(k:ℕ)(hk:k≠0):coeff k a u=0:=by
    dsimp only [a];rw [WilsonPositionScaleLawGuardLift.coefficient]
    apply (fields C.labels d).injective
    rw [WilsonPositionScaleLawGrade.reads,map_zero,named]
    exact (base.high k hk).1
  change atValue q a z u=u
  induction q with
  | zero=>
    have printed:atValue 0 a z=1:=by rw [atValue,WilsonPositionScaleLawGuardEval.printed,show Finset.Iic (0:ℕ)={0} by decide];simp [one]
    rw [printed];rfl
  | succ q ih=>
    rw [WilsonPositionScaleLawGuardQuadratic.nextTerm]
    change atValue q a z u+z^(q+1) • (coeff (q+1) a u)=u
    rw [ih,high _ (by omega),smul_zero,add_zero]

include H in
theorem comparison (lead:Leading F J)(d:ℕ):∀ᶠz:ℝ×Ratio in sweep,∀q:ℕ,
    dressed Z F J d z.1 z.2 (unit d)=WilsonPositionScaleLawGuardPhysical.expected F J Z M ν d q z.1 z.2 (unit d):=by
  filter_upwards [original F J Z lead d] with z price q
  exact price.trans (independent Z R.family M H ν _ d q _).symm

end YM.Integration.WilsonPositionScaleLawGuardUnit
