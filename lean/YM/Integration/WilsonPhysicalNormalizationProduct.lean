import YM.Integration.WilsonPositionPrescribedScreen
import YM.XSpace.Deck
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

/-! Products of the admitted filtered, unit-preserving public field changes in the actual coordinates of the survey. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalNormalizationProduct
open Function Filter Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Classical BigOperators Topology
variable {G:Gauge}{d:ℕ}

def mixed (s t:Change G d):Change G d:=⟨s.val*t.val,by
  rw [may_change]
  simp only [Module.End.mul_apply]
  exact ⟨by rw [t.property.1,map_zero],
    fun i hi p hp=>s.property.2.1 _ hi _ (t.property.2.1 i hi p hp),
    fun p=>by rw [t.property.2.2.1,s.property.2.2.1],
    fun a p=>by rw [t.property.2.2.2,s.property.2.2.2]⟩⟩

def compose (s t:Change G d):Change G d:=s+t+mixed s t

theorem composed (s t:Change G d):stand (compose s t)=stand s*stand t:=by
  change 1+(s.val+t.val+s.val*t.val)=(1+s.val)*(1+t.val)
  noncomm_ring

theorem left_sum (r s t:Change G d):mixed (r+s) t=mixed r t+mixed s t:=by
  apply Subtype.ext
  exact add_mul r.val s.val t.val
theorem right_sum (r s t:Change G d):mixed r (s+t)=mixed r s+mixed r t:=by
  apply Subtype.ext
  exact mul_add r.val s.val t.val
theorem left_real (a:ℝ)(r s:Change G d):mixed (a • r) s=a • mixed r s:=by
  apply Subtype.ext
  exact smul_mul_assoc a r.val s.val
theorem right_real (a:ℝ)(r s:Change G d):mixed r (a • s)=a • mixed r s:=by
  apply Subtype.ext
  exact mul_smul_comm a r.val s.val

def moves (G:Gauge)(d:ℕ):MoveSpace G d →ₗ[ℝ] MoveSpace G d →ₗ[ℝ] MoveSpace G d:=
  LinearMap.mk₂ ℝ (fun x y=>guide G d (mixed ((guide G d).symm x) ((guide G d).symm y)))
    (by intro x y z;rw [map_add,left_sum,map_add])
    (by intro a x y;rw [map_smul,left_real,map_smul])
    (by intro x y z;rw [map_add,right_sum,map_add])
    (by intro a x y;rw [map_smul,right_real,map_smul])

theorem approaches {ι:Type*}{u:Filter ι}{s t:ι→Change G d}
    (before:Tendsto (fun i=>guide G d (s i)) u (𝓝 0))
    (after:Tendsto (fun i=>guide G d (t i)) u (𝓝 0)):
    Tendsto (fun i=>guide G d (compose (s i) (t i))) u (𝓝 0):=by
  have product:=((moves G d).toContinuousBilinearMap.continuous₂.tendsto (0,0)).comp
    (before.prodMk_nhds after)
  have cross:Tendsto (fun i=>guide G d (mixed (s i) (t i))) u (𝓝 0):=by
    have vanish:mixed (0:Change G d) 0=0:=Subtype.ext (zero_mul _)
    simpa [moves,Function.comp_def,vanish] using product
  simpa [compose] using (before.add after).add cross

end YM.Integration.WilsonPhysicalNormalizationProduct
