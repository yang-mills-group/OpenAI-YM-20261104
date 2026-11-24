import YM.Integration.WilsonPointChildTestCoordinates
import YM.Integration.WilsonMarkedCoverIndependentStep
import YM.Integration.WilsonNeutralPointCourse

/-! The original, single addressed test pull and thermal reversion on the
    covered independently constrained ordinary step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildCoverStep
open YM FormalBulk08 Lattice RG Laurent Next.Foundations PhysicalNext.Repeat.Legato
open Reef Flat Stationary Dawn Pose Kemp Palm Shore Mesa Wine Quire Roof Lotus Sierra Gorge Dove
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped ContDiff BigOperators Topology Classical
variable {G:Gauge}{d D:ℕ}
def routes (R:Run G):Primer.Families R.family:=fun i=>Flat.routes (R.family.path.levels.clock.op i 0).patch

theorem address (P:Patch)(x:Site P.L)(y:E4):
    coordinates (Dawn.bay x y)=tucks P x (coordinates y):=by
  unfold Dawn.bay Dawn.pith tucks offset
  rw [map_add,map_smul,map_smul]
  rfl

theorem pulled (P:Patch)(x:Site P.L)(h:2≤P.L.val)(p:Scroll D):
    Dawn.throughW x D h (physical p)=physical (growWord P x D p):=by
  rw [physical,Dawn.through_show]
  apply congrArg (Dawn.portrait D)
  apply Subtype.ext
  funext y
  change p.val (coordinates (Dawn.bay x y))=p.val (tucks P x (coordinates y))
  rw [address]

theorem work_origin (Z:Mesa.Pot G):Kemp.work 0 Z=Z:=by
  funext e r x
  change Z e r (fun t=>_) = Z e r x
  congr 1
  funext t
  rcases hz:x t with ⟨z,θ⟩
  simp [Lotus.tint,hz]

theorem filed (R:Run G)(u:G.ColorIndex)(N j:ℕ)(Y:Plaza (R.family.labels.level d) D)
    (v:Letter (R.family.labels.level d))(p:Scroll D):
    let P:=WilsonCoeffUV.loose R.family.path.levels j
    WilsonNeutralPointCourse.forward R (routes R) u (fun _=>0) N j Y v (physical p)=
      (P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d (Y v (physical (growWord P 0 D p))):=by
  let P:=WilsonCoeffUV.loose R.family.path.levels j
  let T:=Dawn.throughW (0:Site P.L) D (Elm.growL R.family.path.levels j) (physical p)
  have h:T=physical (growWord P 0 D p):=pulled _ _ _ _
  have lift0:lift (0:Site P.L)=(0:Cover):=by ext; simp [lift]
  change (P.L.val:ℝ)^d • WilsonMarkedCoverIndependentStep.fixed R u N j d (Kemp.work (lift (0:Site P.L)) (Y v T))=_
  rw [lift0,work_origin,h]

end YM.Integration.WilsonPointChildCoverStep

