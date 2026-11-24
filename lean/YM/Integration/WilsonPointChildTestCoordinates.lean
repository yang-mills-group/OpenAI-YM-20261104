import YM.Integration.WilsonPointChildTestJet

/-! A genuine smooth test in the sup-norm half-cell and its physical
    Euclidean representative have equal pointed jets in the same axes. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildTestCoordinates
open YM Lattice RG Laurent FormalBulk08 Dawn Pose Next.Foundations PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Embroider WilsonPointChildTestSupport WilsonNeutralPointCourse WilsonPointChildTestJet
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{d D:ℕ}

def coordinates:E4 →L[ℝ] E:=(PiLp.continuousLinearEquiv 2 ℝ (fun _:Axis=>ℝ)).toContinuousLinearMap

theorem axis (u:Axis):coordinates (basis u)=dot u:=by
  ext j
  simp [coordinates,basis,dot,Pi.single_apply]

def garden (p:Scroll D):Garden D:=⟨p.val ∘ coordinates,(scribble p le_rfl).comp coordinates.contDiff⟩
def physical (p:Scroll D):Studio D:=portrait D (garden p)

theorem common (p:Scroll D)(k:Brush D): (physical p).val k origin=(page D p).val k zeroC:=by
  change iteratedFDeriv ℝ (k.1:ℕ) (p.val ∘ coordinates) (0:E4) (basis ∘ k.2)=
    iteratedFDeriv ℝ (k.1:ℕ) p.val (0:E) (dot ∘ k.2)
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right coordinates (scribble p le_rfl) _
    (Nat.cast_le.mpr (Nat.le_of_lt_succ k.1.isLt)),ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [Function.comp_def,axis]

theorem original (R:Run G)(wood:Primer.Families R.family)(a:G.ColorIndex)(depth:d<D)
    (N i:ℕ)(v:Letter (R.family.labels.level d))(p:Scroll D):
    filed R wood a depth (fun _=>0) N i v (physical p)=
      filed R wood a depth (fun _=>0) N i v (extend D zeroC (page D p)):=by
  apply WilsonPointChildTestJet.original
  intro t
  exact common p _

end YM.Integration.WilsonPointChildTestCoordinates

