import YM.Integration.WilsonIndependentWardStampOrbit
import YM.Integration.WilsonIndependentMatchedRankedPair
import YM.Integration.WilsonIndependentRawNamedProduct

/-! A compact fixed real Ward word and its precisely named R/W peer,
with the latter's true own-rank de-shift on the filmed tree. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardNamedHearing
open Lattice Wilson RG Source Labels WardBin PowerSeries PertExtension Orb XSpace XSpace.Rose XSpace.Cirrus FVA2
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Halo
open WilsonIndependentMatchedNamedPair WilsonIndependentRawNamedStencil
open scoped Classical BigOperators
variable {G:Gauge}

theorem submit (n:Side)(f:CoverConfig G→ℝ)(o:Cover) :
    vital n (convey o (fun _=>f)) =
      WilsonIndependentMatchedOrbitReading.insert (places (wrap n o) f) := by
  funext t v _
  apply congrArg f
  funext e
  change Orb.liftLinks v (wrap n (e.1+o),e.2)=Orb.liftLinks v (wrap n e.1+wrap n o,e.2)
  rw [map_add]

variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(Y:Sample 2)
  (k:ℕ)(label:(R.family.labels.level k).Index)(render:Bool)
local notation "T" => W.tree Y.F.p
theorem original (f:CoverConfig G→ℝ)(o z:Cover)(clean:PreTest (places (wrap Y.F.p.side o) f))(q:ℕ) :
    coeff q (Bare.normalized T G (BareOrb.stencil T (places (wrap Y.F.p.side o) f) *
      printed R W Y render k z label)) =
      (plotPT WilsonIndependentMatchedOrbitReading.originalClock
        (vital Y.F.p.side (convey o (fun _=>f) * convey z (brand R W render k label)))
        (0+((R.family.labels.level k).grades label).2) q:ℂ) := by
  rw [WilsonIndependentMatchedClosedPlan.pair T clean (admitted R W Y render k z label)
    (r:=0) (by simp) (ranked R W Y render k z label)]
  congr 2
  funext t v h
  have l:=congrFun (congrFun (congrFun (submit Y.F.p.side f o) t) v) h
  have r:=congrFun (congrFun (congrFun (submitted R W render k label z Y) t) v) h
  exact congrArg₂ (·*·) l.symm r.symm

end YM.Integration.WilsonIndependentWardNamedHearing
