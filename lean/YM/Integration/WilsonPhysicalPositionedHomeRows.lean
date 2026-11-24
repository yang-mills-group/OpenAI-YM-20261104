import YM.Integration.WilsonPhysicalNormalizedWholeTable
import YM.Integration.WilsonPositionHomogeneousFrame

/-! The shared position solve evaluated on an actual original Wilson field at each of its own physical homes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionedHomeRows
open Filter Function Set Maxwell Maxwell.Free XSpace XSpace.Normalize Wilson RG
open MeasureTheory Lattice Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress PhysMS Trace.Pilot FVA2 FVA2.Register
open WilsonPhysicalPositionTargetRows WilsonPhysicalNormalizedSignedMenu WilsonPhysicalNormalizedWholeTable
open WilsonPositionPrescribedScreen
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
variable (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G)
variable {d n:ℕ}{I:Type}

def pins (J:ℝ→PhysMS.tower S)(ages:Fin n→ℝ)(x:Points n):Row G d n:=
  (S.classMoment (spectator F none) (fun _:Fin n=>d) x).compLinearMap
    (fun j=>(J (ages j) d).toLinearMap.comp (Maxwell.Free.fields R.family.labels d).symm.toLinearMap)

def declared (r:ℝ)(v:Sec G d):Sec G d:=
  (Maxwell.Free.fields R.family.labels d)
    (WilsonPositionHomogeneousFrame.change F J Z d r ((Maxwell.Free.fields R.family.labels d).symm v))

theorem named (r:ℝ)(v:Sec G d)(h:Bijective (stand (correction F J Z.store d r))):
    WilsonPositionHomogeneousFrame.homogeneous F J Z r d ((Maxwell.Free.fields R.family.labels d).symm v)=
    J r d ((Maxwell.Free.fields R.family.labels d).symm
      (stand (correction F J Z.store d r) (declared F J Z r v))):=by
  simpa [WilsonPositionHomogeneousFrame.homogeneous,WilsonPositionPrescribedFrame.positioned,declared]
    using congrArg (J r d) (WilsonPositionPrescribedFrame.leg F J Z.store h (declared F J Z r v))

theorem issued (home:Fin n→I)(ages:I→ℝ)(x:Points n)(μ:ℂ)(v:Fin n→Sec G d)
    (h:∀i,Bijective (stand (correction F J Z.store d (ages i)))):
    fitted (Z.store.survey d) (Z.store.prepared d) home (fun i=>hierarchy F J d (ages i))
      (μ • pins F J (ages ∘ home) x) (fun j=>declared F J Z (ages (home j)) (v j))=
      μ*pins F (WilsonPositionHomogeneousFrame.homogeneous F J Z) (ages ∘ home) x v:=by
  change μ * S.classMoment (spectator F none) _ x _=μ*S.classMoment (spectator F none) _ x _
  congr 1
  apply congrArg
  funext j
  exact (named F J Z (ages (home j)) (v j) (h _)).symm

theorem original [Fintype I]{ι:Type*}(u:Filter ι)(lead:PhysMS.Leading F J)(d:ℕ)(home:Fin n→I):
    ∃ C:ℝ,0<C ∧ ∀(ages:ι→I→ℝ)(_:∀a,Tendsto (fun z=>ages z a) u trail)
      (Q:ι→I→Prediction G d)(s:ι→I→Change G d)
      (_:∀ a,(Z.store.survey d).Via (fun z=>Q z a) (u:=u))
      (_:∀a,Tendsto (fun z=>guide G d (s z a)) u (𝓝 0))
      (x:ι→Points n)(μ:ι→ℂ)(W:ι→Row G d n),
      ∀ᶠ z in u,∀v:Fin n→Sec G d,
        let h:=fun j=>declared F J Z (ages z (home j)) (v j)
        let M:=μ z • pins F J (ages z ∘ home) (x z)
        let Y:=offered home (s z) (W z)
        let D:=Z.store.survey d
        ‖μ z*pins F (WilsonPositionHomogeneousFrame.homogeneous F J Z) (ages z ∘ home) (x z) v-
          fitted D (Z.store.prepared d) home (Q z) (W z) h‖≤
        cost h*(C*(‖rows M-rows Y‖+‖docket D (fun a=>hierarchy F J d (ages z a))-
          docket D (retag (s z) (Q z))‖*‖rows Y‖)):=by
  let D:=Z.store.survey d
  let H:=Z.store.prepared d
  obtain ⟨C,hC,pay⟩:=WilsonPhysicalNormalizedWholeTable.original D H home u
  refine ⟨C,hC,?_⟩
  intro ages old Q s bare oriented x μ W
  let P:=fun z a=>hierarchy F J d (ages z a)
  let M:ι→Row G d n:=fun z=>μ z • pins F J (ages z ∘ home) (x z)
  have raw:(Z.store.survey d).Via (hierarchy F J d) (u:=trail):=warm F J lead Z.store d
  have paid:=pay P Q s (fun a=>raw.comp (old a)) bare oriented M W
  have allowed:∀ᶠ z in u,∀a:I,Bijective (stand (correction F J Z.store d (ages z a))):=
    Filter.eventually_all.mpr fun a=>(old a).eventually (D.stand_sure H raw)
  filter_upwards [paid,allowed] with z amount live
  intro v
  let h:=fun j=>declared F J Z (ages z (home j)) (v j)
  have mass:0≤cost h:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have applied:=(tested (fitted D H home (P z) (M z)) (fitted D H home (Q z) (W z)) h).trans
    (mul_le_mul_of_nonneg_left amount mass)
  rw [←issued F J Z home (ages z) (x z) (μ z) v live]
  exact applied

end YM.Integration.WilsonPhysicalPositionedHomeRows
