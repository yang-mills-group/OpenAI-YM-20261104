import YM.Integration.WilsonMaxwellThermometerCommonTangent
import YM.XSpace.OffAxis
import YM.XSpace.Laurel

/-! The complete Maxwell first variation of the named curvature thermometer. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonObservedChiralFreeRoseTangent
open Maxwell Maxwell.Free Maxwell.Wick XSpace XSpace.Structure1 XSpace.Normalize
open WilsonMaxwellThermometerFaces (connected opposite_parity tested)
open WilsonMaxwellThermometerOriginal (lower)
open WilsonMaxwellThermometerCommonTangent (payout correction separate)
variable {G:Gauge}{V:Store G}

theorem pointwise (simple:G.Simple)(p q:Sec G 4)(x:Points 3)(hx:x∈conf 3):
    connected x (Graph3.trip (Rose.toll G) (up (by decide:4≤6) p) (up (by decide:4≤6) q))=0 :=
  opposite_parity x hx _ _ _ Rose.t_odd
    (Subtype.ext (AxesTangent.same_low simple p.val p.property))
    (Subtype.ext (AxesTangent.same_low simple q.val q.property))

theorem lower_pair (K:Rose.Pick V)(simple:G.Simple)(p q:Sec G 4):
    payout K (Rose.toll G) p q=0 :=
  tested K _ (pointwise simple p q)

theorem original (K:Rose.Pick V)(simple:G.Simple)(du:Sec G 6)(dp dq:Sec G 4):
    correction K (Rose.toll G) du (lower G) dp (lower G) dq=0 := by
  have upper : payout K du (lower G) (lower G)=0 :=
    separate K simple du LinearMap.id LinearMap.id (fun _ _=>rfl) (fun _ _=>rfl)
  simp only [correction,upper,lower_pair K simple,add_zero]

end YM.Integration.WilsonObservedChiralFreeRoseTangent
