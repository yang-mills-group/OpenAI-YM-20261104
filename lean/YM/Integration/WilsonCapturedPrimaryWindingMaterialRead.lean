import YM.Integration.WilsonCapturedPrimaryWindingMaterial
import YM.Integration.WilsonOriginalFiledPointedIncome

/-! On the original torus the unaltered clock reads the literal thermal
coefficient of the enrolled group field, including its value at zero. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWindingMaterialRead
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary AllOrder AllOrder.Floe
open Exterior Comparison.RG02 Comparison.RG02.Adjacent Multi FVA1Physical FVA1Physical.TwoReset
open Further.PhysicalPeriodLimitF933 Macrame
open WilsonCapturedPinnedGroupClock WilsonCapturedPinnedColorFile WilsonOriginalMarkedFaceReading
open WilsonOriginalOccupiedFieldLayout WilsonOriginalCenteredSeamSalary WilsonCapturedRootedAngularSlots
open WilsonCapturedClockRankProjection RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{n:Side}{V X ι:Type}[DecidableEq V]{o:Passport n V}{J:Census V}

def nativeClock:UnitCost:=⟨fun _=>1,contDiffAt_const,rfl⟩

theorem native (Z:Bulk.Colors J G n)(well:Bulk.Well Z)(s:Hot J)(e:ℕ)(B:fieldDir G n 1) :
    See.noseC (Stock.census Unit) () nativeClock (field Z s (Stock.census Unit)) e B=
      (Air.discharge Z e B).part s.val:=by
  rw [WilsonOriginalMarkedFaceReading.original]
  simp only [WilsonOriginalFiledMarkCloth.row,nativeClock,UnitCost.enter,mul_one,one_pow,inv_one,one_smul,
    Air.discharge,part_lit]
  let T:ℝ→L[ℝ]ℝ×fieldDir G n 1:=(ContinuousLinearMap.id ℝ ℝ).smulRight (1,B)
  have applyT(x:ℝ):T x=(x,x • B):=by ext1 <;> simp [T]
  have pay:=Assembly.jet_continuous_right T ((well.suppose_mark s).smooth.of_le
    (show ((Z.power s+e:ℕ):WithTop ℕ∞)≤ω from le_top)) (1:ℝ)
  rw [show (Bulk.projected (Z.mark s)) ∘ T=(fun x:ℝ=>Bulk.projected (Z.mark s) (x,x • B)) from
    funext (fun x=>congrArg (Bulk.projected (Z.mark s)) (applyT x)),applyT,one_smul] at pay
  exact pay

variable (M:ι→Row o J G X)(t:X)(grade:V→ℕ)(layout:Layout G)(tape:Finset Age)
local notation "source" => Air.craft M (fun i=>(M i).paint t) grade layout tape
local notation "raw" s:max => field (source) s (Stock.census Unit)
local notation "reading" s:max c:max => (fun e (a:Link G n)=>See.noseC (Stock.census Unit) () c (raw s) e (Stationary.arm G n 1 a))

theorem original {w:V→ℝ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grade σ C order seats shelf)(hs:0<σ)(proper:Legal tape layout)
    (s:Hot J)(v:s.val.val)(b:Fin (Pages n n))(projection:ℂ→L[ℝ]ℝ)
    (slack:LipschitzWith 1 projection)(cap e r:ℕ)(pos:0<r):
    let Z:=channel projection (raw s)
    let A:=WilsonCapturedRealFiledKernel.entries (fun j=>projection ∘ ((reading s nativeClock) j))
    Bulk.Well Z ∧ Arm.Single nativeClock Z A () cap ((source).power s) ∧
    Poly.toll w s.val*(∑x:Fin r→Site n×Loc G 1,
      Real.exp ((σ/8)*(radius (o.origin v.val) (sites x):ℝ))*|A e r x|) ≤
      (r.factorial:ℝ)⁻¹*charge nativeClock (-((source).power s:ℤ)) ((source).power s+e) r
        (fun j=>WilsonCapturedCoveredSourceWage.fare G j r σ C) ∧
    ∀j a,See.noseC (Stock.census Unit) () nativeClock Z j (Stationary.arm G n 1 a)=
      (projection ((peek dvd_rfl M grade layout tape t j a).part s.val):ℂ):=by
  intro Z A
  have license:=Air.license M (fun i=>(M i).paint t) grade w stock hs (fun i=>stock.honor i t)
  have earned:Bulk.Well (source):=(Air.standard M _ grade license layout tape proper).1
  have paper:=WilsonOriginalFiledPointedIncome.original (n:=n) dvd_rfl M t s.val v stock hs b nativeClock
    ((source).power s) (source).vac projection slack cap e r pos
  dsimp only at paper
  rw [WilsonCapturedPrimaryWindingMaterial.material M t grade layout tape s v b,
    WilsonMeasuredOriginalPeriodRead.atSite] at paper
  refine ⟨WilsonCapturedPrimaryWindingMaterial.legal _ (WilsonOriginalMarkedFaceReading.legal _ s _ earned)
    projection,paper.1,paper.2.1,?_⟩
  intro j a
  rw [paper.2.2 j a,WilsonMeasuredOriginalPeriodWord.literal]
  exact congrArg (fun z:ℂ=>(projection z:ℂ)) (native (source) earned s j _)

end YM.Integration.WilsonCapturedPrimaryWindingMaterialRead
