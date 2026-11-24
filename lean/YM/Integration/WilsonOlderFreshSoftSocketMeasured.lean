import YM.Integration.WilsonOlderFreshSoftSocketFlux
import YM.Integration.WilsonOlderFreshSoftSocketMeasuredCash

/-! The fitted physical vector, including every marked unit, is paid once on every actual child and received as its original joint q with its genuine planting pole. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketMeasured
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}
variable (κ:(i:I)→Knob (D i))(pt:I→Chamber)
local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O

theorem original (simple:G.Simple)(ratio:LocalRatio O_)(L:ℂ→L[ℝ]ℝ)(N per K:ℕ)
    (cells:Digits L_ I)(S:Finset I)(w:(i:I)→R.family.label (d i))
    (m:ℕ)(older:m≤K)(live:K≤N)(y:I → Cover):
    ∑b:Columns R (fun i:S=>d i),L (packet R d S w N per K b) •
      levelsO (itinerary L_ O_ d N cells (K-m) m
        (WilsonOlderFreshSoftFigures.stencil R D d (seats R d S b) κ pt) y) S=
    ∑q:(i:S)→Choice R d i,L (ticket R d S w N per K q) •
      levelsO (itinerary L_ O_ d N cells (K-m) m (raw R d κ pt (fill R d S q)) y) S:=by
  classical
  let Y (q:(i:S)→Choice R d i):=levelsO (itinerary L_ O_ d N cells (K-m) m (raw R d κ pt (fill R d S q)) y) S
  let W (b:Columns R (fun i:S=>d i))(q:(i:S)→Choice R d i):=
    packet R d S w N per K b*WilsonOlderFreshSoftSocketFaces.cash R d (seats R d S b) S N per K q
  calc
    _ = ∑b:Columns R (fun i:S=>d i),∑q:(i:S)→Choice R d i,L (W b q) • Y q:=by
      apply Finset.sum_congr rfl
      intro b _
      have h:=WilsonOlderFreshSoftSocketFlux.original R d (seats R d S b) κ pt simple ratio
        (L.comp (ContinuousLinearMap.mul ℝ ℂ (packet R d S w N per K b))) N per K cells S m older live y
      change L (packet R d S w N per K b*1) • _ = _ at h
      rw [mul_one] at h
      rw [h]
      apply Finset.sum_congr (by ext q;simp)
      intro q _
      rfl
    _ = ∑q:(i:S)→Choice R d i,∑b:Columns R (fun i:S=>d i),L (W b q) • Y q:=Finset.sum_comm
    _ = _:=by
      apply Finset.sum_congr rfl
      intro q _
      rw [←Finset.sum_smul,←map_sum]
      have h:=WilsonOlderFreshSoftSocketMeasuredCash.original R d S w (per:=per) live q
      change L (∑b:Columns R (fun i:S=>d i),W b q) • Y q=L (ticket R d S w N per K q) • Y q
      rw [show ∑b:Columns R (fun i:S=>d i),W b q=ticket R d S w N per K q from h]

end YM.Integration.WilsonOlderFreshSoftSocketMeasured
end
