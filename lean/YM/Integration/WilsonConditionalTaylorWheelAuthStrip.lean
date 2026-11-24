import YM.Integration.WilsonConditionalTaylorWheelRootedStrip
import YM.Integration.WilsonConditionalTaylorWheelTensors
import YM.Integration.WilsonConditionalTaylorWheelTensors
import YM.WilsonCoeffUV.Emit.RentedCapture
import YM.Integration.WilsonConditionalTaylorIndependentMarked

/-! True rank and anchored positive strip for the complete old marked scalar
file of a diagram. These come from its enrolled WUV packet, on all periods. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelAuthStrip
open Function Filter Matrix Lattice RG Laurent Wilson Exterior Precision
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof Lotus Mesa
open Next.Free Work.F03 Work.F05 Work.F08 Stationary Bloch Tree
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open scoped Classical BigOperators Topology
variable {G:Gauge} {q:ℕ} (S:Era G ℝ) (held:Auth q S)
include held

theorem finite (n:Side):Young (rancho (Blue.flash (S.1 n))) q:=by
  intro e r occupied
  change r≤q+e
  by_contra! distant
  apply occupied
  rw [WilsonConditionalTaylorWheelTensors.actual (S.1 n) q (held.span n) (held.pale n)]
  exact held.span n e r distant

theorem cover : Young S.2 q:=by
  intro e r occupied
  change r≤q+e
  by_contra! distant
  apply occupied
  funext x
  have point:=(held.wing e r).point x
  have none(n:Side):S.1 n e r=0:=held.span n e r distant
  simp only [none,Pi.zero_apply] at point
  exact tendsto_nhds_unique point tendsto_const_nhds

theorem original (a:Loc G 1) (e r:ℕ):
    ∃s:ℝ,0<s ∧ Kemp.Kalm s (0,a) (S.2 e r)
      (fun n=>rancho (Blue.flash (S.1 n)) e r):=by
  have recd(n:Side):rancho (Blue.flash (S.1 n)) e r=S.1 n e r:=
    WilsonConditionalTaylorWheelTensors.actual (S.1 n) q (held.span n) (held.pale n) e r
  simp only [recd]
  exact WilsonConditionalTaylorWheelRootedStrip.original (held.wing e r) a
end YM.Integration.WilsonConditionalTaylorWheelAuthStrip
end
