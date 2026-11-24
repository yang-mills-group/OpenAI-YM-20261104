import YM.Integration.WilsonCapturedPrimaryWindingMaterialRead
import YM.Integration.WilsonEmittedFiledDeckFare

/-! Ordered angular coefficients of an actually filed group word on its
own torus. The scalar row is evaluated on the same occupied face. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintFronts
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary AllOrder AllOrder.Floe
open Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi FVA1Physical FVA1Physical.TwoReset
open Further.PhysicalPeriodLimitF933 Macrame
open WilsonCapturedPinnedGroupClock WilsonCapturedPinnedColorFile WilsonOriginalMarkedFaceReading
open WilsonOriginalOccupiedFieldLayout WilsonOriginalCenteredSeamSalary WilsonCapturedRootedAngularSlots
open WilsonCapturedClockRankProjection RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{n:Side}{V X ι:Type}[DecidableEq V]{o:Passport n V}{J:Census V}


open WilsonCapturedPrimaryWindingMaterialRead (nativeClock)
open WilsonIndependentCapturedAngularWinding
variable (M:ι→Row o J G X)(t:X)(grade:V→ℕ)(layout:Layout G)(tape:Finset Age)
  (s:Hot J)(phase:ℂ→L[ℝ]ℝ)
local notation "one" => WilsonOriginalMarkedFaceReading.field
  (Air.craft M (fun i=>(M i).paint t) grade layout tape) s (Stock.census Unit)
def table:=WilsonCapturedRealFiledKernel.entries (fun e B=>phase ((peek dvd_rfl M grade layout tape t e B).part s.val))

theorem scalar (e:ℕ)(x:Fin 0→Site n×Loc G 1):
    table M t grade layout tape s phase e 0 x=phase ((peek dvd_rfl M grade layout tape t e 0).part s.val):=by
  simp [table,WilsonCapturedRealFiledKernel.entries,iteratedFDeriv_zero_apply]

theorem issued {w:V→ℝ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grade σ C order seats shelf)(hs:0<σ)(proper:Legal tape layout)
    (v:s.val.val)(slack:LipschitzWith 1 phase)(cap e r:ℕ)(positive:0<r):
    let A:=table M t grade layout tape s phase
    let Z:=channel phase one
    let pole:=Launch.index J grade s.val+1
    Bulk.Well Z ∧ Arm.Single nativeClock Z A () cap pole ∧
    Poly.toll w s.val*(∑x:Fin r→Site n×Loc G 1,
      Real.exp ((σ/8)*(radius (o.origin v.val) (sites x):ℝ))*|A e r x|) ≤
      (r.factorial:ℝ)⁻¹*charge nativeClock (-(pole:ℤ)) (pole+e) r
        (fun j=>WilsonCapturedCoveredSourceWage.fare G j r σ C) ∧
    ∀j B,WilsonEmittedFiledDeckFare.row nativeClock Z () j B=(phase ((peek dvd_rfl M grade layout tape t j B).part s.val):ℂ):=by
  intro A Z pole
  let page₀:Fin (Pages n n):=⟨0,by simp [Pages,Nat.div_self n.pos]⟩
  have trueRow:=WilsonCapturedPrimaryWindingMaterialRead.original M t grade layout tape stock hs proper s v page₀ phase slack cap e r positive
  dsimp only at trueRow
  have license:=Air.license M (fun i=>(M i).paint t) grade w stock hs (fun i=>stock.honor i t)
  have actual:Bulk.Well (Air.craft M (fun i=>(M i).paint t) grade layout tape):=
    (Air.standard M _ grade license layout tape proper).1
  have filed (j:ℕ)(u:Link G n):
      See.noseC (Stock.census Unit) () nativeClock one j (Stationary.arm G n 1 u)=
        (peek dvd_rfl M grade layout tape t j u).part s.val:=by
    rw [WilsonCapturedPrimaryWindingMaterialRead.native _ actual s j,WilsonThermometerPositionFilmSelf.pupil]
  have eqn:(fun j=>phase ∘ (fun a:Link G n=>See.noseC (Stock.census Unit) () nativeClock one j (Stationary.arm G n 1 a)))=
      (fun j u=>phase ((peek dvd_rfl M grade layout tape t j u).part s.val)):=by
    funext j u
    exact congrArg phase (filed j u)
  rw [eqn] at trueRow
  exact trueRow

end YM.Integration.WilsonNeutralTwoPrintFronts
end
