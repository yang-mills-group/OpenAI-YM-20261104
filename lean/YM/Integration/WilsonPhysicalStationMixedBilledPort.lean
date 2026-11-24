import YM.Integration.WilsonPhysicalStationMixedChartCharge
import YM.Integration.WilsonPhysicalStationMixedListener
import YM.Integration.WilsonPhysicalStationMixedForeign
/-! The authentic signed, lower-subtracted Wilson two-field measurement against a registered
right probe of its own engineering grade and leg count. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedBilledPort
open Function Filter Finset Lattice RG Wilson Source Labels
open Next.Rank Next.Rank.East Next.Rank.Price MergeProof.East
open Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationRawReading (err)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationMeasuredCash (aperture)
open WilsonPhysicalStationRegisteredDiagonal (ratio)
open WilsonPhysicalStationWeightedAxis (purse)
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationThermalStart (entered)
open WilsonPhysicalStationThermalCoordinates (filed)
open WilsonPhysicalStationBasisRoof (rent)
open WilsonPhysicalStationMixedChartCharge (wage)
open WilsonPhysicalStationMixedListener (port value)
open WilsonPhysicalStationMixedWickPair (cell)
open WilsonPhysicalStationMixedWickTest (reference)
open WilsonPhysicalStationThermalRanks (probe)
open scoped Classical BigOperators Topology

variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D D' h e r N p:ℕ}(A:Vane R.family D)(B:Vane R.family D')
    (da:h<D+1)(db:h<D'+1)(ca:A.checked f H D)(cb:B.checked f H D')
local notation "d₀"=>(⟨h,da⟩:Fin (D+1))
local notation "d₁"=>(⟨h,db⟩:Fin (D'+1))
local notation "F₀"=>R.family.labels.level h
local notation "A₀"=>R.family.path.levels
local notation "M₀"=>Station.mag (A₀) A.b A.k
local notation "M₁"=>Station.mag (A₀) B.b B.k
local notation "T₀"=>(A₀).clock.monitor A.k
local notation "P₀"=>(shrink R.family A.k N p)⁻¹
local notation "P₁"=>(shrink R.family B.k N p)⁻¹


def base (h:ℕ){r:ℕ}(z:(standard R.family).Field r)(x:Points 2)(a:(R.family.labels.level h).Index):ℂ:=
  reference R.family (l:=h) (Pi.single a 1) z x

theorem original (dates:B.k=A.k ∨ B.k=A.k+1)(top:B.k<N)(warm:WilsonPhysicalStationBasisClock.Live R A.k)
    (window:aperture R A.k B.k h (M₀) (M₁)≤1)(a:(F₀).Index)(w:R.family.label h)
    (stamped:if B.k=A.k then WilsonPhysicalStationCoincidentLower.Receipt R A B h e da db (p:=p) ca cb top a w
      else WilsonPhysicalStationSelectedLower.Receipt R A B h e da db (p:=p) ca cb top a w)
    (dr:r<D+1)(b:(R.family.labels.level r).Index)(s:Signed)(side:Fin 2)(j:ℕ)(o:Fin 2 → Lattice.Cover)
    (x:Points 2)(J:ℝ)(jp:0≤J)
    (low:∀i,((F₀).grades i).2≤((R.family.labels.level r).grades b).2 →
      ‖cell R A (d₀) ⟨r,dr⟩ (p:=p) ca (show A.k<N by omega) j o (Pi.single i 1) (probe R.family b s side)
         -base R h (probe R.family b s side) x i‖*(T₀)^((R.family.labels.level r).grades b).2≤J*(T₀)^((F₀).grades i).2)
    (high:∀i,((R.family.labels.level r).grades b).2<((F₀).grades i).2 →
      ‖cell R A (d₀) ⟨r,dr⟩ (p:=p) ca (show A.k<N by omega) j o (Pi.single i 1) (probe R.family b s side)
         -base R h (probe R.family b s side) x i‖≤J):
    let q:=((F₀).grades a).2
    let Q:=((R.family.labels.level r).grades b).2
    let z:=probe R.family b s side
    let Z:=entered R B (d₁) (p:=p) cb top (Pi.single a 1)-(R.family.factory h N p).terminal w
    let χ:ℂ:=signal R N p A.k B.k h q (M₀) (M₁)
    ‖value R N p j o Z (A.wheel.atCut (N,p) ⟨r,dr⟩ z)-χ*base R h z x a‖*(T₀)^Q
      ≤wage R q Q J (∑i,‖base R h z x i‖) A.k h*(T₀)^q:=by
  intro q Q z Z χ
  let U:=A.wheel.atCut (N,p) ⟨r,dr⟩ z
  let read:=port R h N p j o U
  let born:=base R h z x
  have row (i:(F₀).Index):read (raw R A (d₀) (p:=p) ca (show A.k<N by omega) (Pi.single i 1))
       =cell R A (d₀) ⟨r,dr⟩ (p:=p) ca (show A.k<N by omega) j o (Pi.single i 1) z:=
    WilsonPhysicalStationMixedListener.seated R A (d₀) ⟨r,dr⟩ ca _ j o z (Pi.single i 1)
  have pay:=WilsonPhysicalStationMixedChartCharge.original R A B da db ca cb dates top warm window a w stamped
    read born Q J jp (fun i hi=>by rw [row i];exact low i hi) (fun i hi=>by rw [row i];exact high i hi)
    (fun i hi=>WilsonPhysicalStationMixedForeign.original R.family i b s side x hi)
  simpa only [read,WilsonPhysicalStationMixedListener.actual] using pay

end YM.Integration.WilsonPhysicalStationMixedBilledPort
end
