import YM.Integration.WilsonThermometerOriginalMeans
import YM.Integration.WilsonThermometerRegisteredCenteredWallet
import YM.Integration.WilsonThermometerFiniteConnectedCells

/-! A uniform restoration on paid ordinary material along the physical ordered limits.
The actual (6,4,4) singleton means are read at their independent finite sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredPhysicalMeans
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonPositionCorrectedCap WilsonSeparatedOriginalThermometerCells
open WilsonThermometerMarchProduct (field)
open Marker WilsonThermometerFiniteConnectedCells WilsonThermometerCenteredScalar Primitives.GCC.Anchor
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

variable {H : (Bel R.family.book).Hierarchy} {Y:Ultrafilter (ℕ×ℕ)}

variable (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (V : Store G) (A : ℝ→Group R.family 6)
local notation "Pθ" => WilsonPositionPrescribedFrame.positioned F J V

local notation "J₃" => Stock.census (Fin 3)

theorem original (simple:G.Simple) (lead:Leading F J)
    (obeys:∀d,∀ᶠ r in trail,PhysMS.Frame.obedient F H (J r) d)
    (book:Book (f:=f) (l:=Y) (H:=H) A J) (prior:(Y:Filter _)≤f.fuse):
    ∀ᶠ rz in trail.curry (Y:Filter _),let Z:=adjusted F J V A rz.1
      ∀(x:Fin 3→Site (R.family.side rz.2.1 rz.2.2)) (w:Fin 3→ℝ) (_pos:∀v,0<w v) (_cap:∀v,w v≤1)
        (Q:Poly J₃) (_unit:Q.part (J₃).quiet=1) (_funds:Poly.price w (inverseMass Q)≤WilsonFiniteOrdinaryInverse.fee J₃),
        WilsonThermometerRegisteredCenteredInvoice.restoration w (measured R Z rz.2 x) Q≤
          2*(1+WilsonFiniteOrdinaryInverse.fee (J₃)*(1+3*(1+WilsonFiniteOrdinaryInverse.fee (J₃))+2*(1+WilsonFiniteOrdinaryInverse.fee (J₃))^2)):=by
  have bought:=WilsonThermometerOriginalMeans.original F J V A simple lead obeys book prior (show (0:ℝ)<1 by norm_num)
  apply eventually_curry_iff.mpr
  filter_upwards [eventually_curry_iff.mp bought,WilsonPositionCorrectedCap.original F J V A book lead 0] with r at_r filed
  let Z:=adjusted F J V A r
  filter_upwards [at_r,prior (WilsonThermometerOriginalMeans.occupied Z filed.2.1 (fun j=>(filed.2.2.2.2.1 j).2.1))] with z cost same
  dsimp only
  intro x w pos cap Q qu funds
  apply WilsonThermometerRegisteredCenteredWallet.material w pos cap _ Q qu _ funds
  intro v
  change ‖row Z z x {v}‖≤1
  rw [same {v} x]
  simpa only [Finset.prod_singleton,WilsonThermometerOriginalMeans.one] using (cost v (x v)).le

end YM.Integration.WilsonThermometerRegisteredCenteredPhysicalMeans
