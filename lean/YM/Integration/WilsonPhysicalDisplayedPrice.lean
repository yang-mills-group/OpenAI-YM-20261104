import YM.Integration.WilsonOriginalTwoFlatPublicFare
import YM.Integration.WilsonReflectedPublicOrientedFaces
import YM.TraceExtension.Terrace.Knell

/-! The original finite factory transports the star and signed lattice action
at every enrolled station. Each turned cutoff source pays one finite frame cost. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalDisplayedPrice
open Function Filter Set Lattice RG Source Labels Wilson OPE Next.Rank Overlay Bid
open MergeProof Ribbons Accent ManyCopies Cells Extra.Histories RG16 RG16.Literal
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Trace.Terrace WilsonReflectedPublicOrientedFaces
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){lo wid teacher}(L:Package R.family wid lo teacher){d f N per:ℕ}
local notation "F₀" => R.family.labels.level d

private theorem turned (y:R.family.label d)(m:Motion):
    displayed R d y m=Motion.patch F₀ m y:=by
  unfold displayed Motion.patch
  split
  · exact Motion.act_conj F₀ y _
  · rfl

include L
theorem original (ready:R.family.ref d≤f)(live:f≤N)(y:R.family.label d)(m:Motion):
    Spindle.paid R.family d f N per (displayed R d y m) ≤
      Motion.orbitCost F₀*Spindle.paid R.family d f N per y:=by
  let q:=Price.columns R.family d f N per
  have issued (v:R.family.label d):q (star v)=star (q v) ∧
      q ((F₀).act m.1.ortho v)=(F₀).act m.1.ortho (q v):=
    Trace.Terrace.guarded R.family R.makes L.system ready live v m.1
  have same:q (displayed R d y m)=Motion.patch F₀ m (q y):=by
    rw [←turned R]
    unfold displayed
    split
    · exact ((issued (star y)).2).trans (congrArg ((F₀).act m.1.ortho) (issued y).1)
    · exact (issued y).2
  let c:=((R.family.S.a f:ℂ)^d)⁻¹
  change (F₀).coeffSize (c • q (displayed R d y m)) ≤ Motion.orbitCost F₀*(F₀).coeffSize (c • q y)
  rw [same,Size.smul,Size.smul,mul_left_comm]
  exact mul_le_mul_of_nonneg_left (Motion.patch_cost F₀ m (q y)) (norm_nonneg _)

theorem adjoint (ready:R.family.ref d≤f)(live:f≤N)(y:R.family.label d)(a:Axis):
    Spindle.paid R.family d f N per (R.family.book.adj d a y) ≤
      Motion.orbitCost F₀*Spindle.paid R.family d f N per y:=
  original R L ready live y (Signed.mirror a,true)

end YM.Integration.WilsonPhysicalDisplayedPrice
end
