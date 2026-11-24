import YM.Integration.WilsonPhysicalStationMixedNativePorts
import YM.Integration.WilsonPhysicalStationMixedPortAllowance
import YM.Integration.WilsonPhysicalStationMixedSchurNamed
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedCourtFare
open Function Filter Lattice Wilson RG Source Cells Finset Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationMixedNamedProbe (coefficient)
open scoped Classical BigOperators
open WilsonMovingForkReporterMixedBasis (Slot)
open WilsonPhysicalStationMixedPortAllowance (fee)
open WilsonPhysicalStationMixedNativePorts (fare)
open scoped Topology
variable {G:Gauge}(R:Run G)(s:Slot R.family)(B:Deck G)(e:ℕ)
    {h:ℕ}(K:Set (Points 2))(compact:IsCompact K)(sep:K⊆conf 2)(u:(standard R.family).Field h)(q:ℕ)
set_option quotPrecheck false
local notation "I"=>Glyph B e
local notation "s₀" => WilsonPhysicalStationMixedSchurNamed.slot R e K compact sep h
def lower (j:I)(D m:ℕ):ℝ:=fare R B e j (fun b=>fee R (s₀ b) u q D m)
def total (cap:I→ℝ)(D m:ℕ):ℝ:=fee R s u q D m+∑j,cap j*lower R B e K compact sep u q j D m
variable (simple:G.Simple){A:Type*}{l:Filter A}{D m:A→ℕ}(deep:Tendsto D l atTop)(late:Tendsto m l atTop)
include simple deep late

theorem detector (j:I):Tendsto (fun i=>lower R B e K compact sep u q j (D i) (m i)) l (𝓝 0):=by
  simpa [lower,fare] using (tendsto_finsetSum Finset.univ (fun b _=>(WilsonPhysicalStationMixedPortAllowance.original R (s₀ b) u q simple deep late).const_mul ‖coefficient R B e j b‖))
theorem original (cap:I→ℝ):Tendsto (fun i=>total R s B e K compact sep u q cap (D i) (m i)) l (𝓝 0):=by
  have head:=WilsonPhysicalStationMixedPortAllowance.original R s u q simple deep late
  simpa [total] using head.add (tendsto_finsetSum Finset.univ (fun j _=>(detector R B e K compact sep u q simple deep late j).const_mul (cap j)))
theorem before (cap:I→ℝ){ε:ℝ}(positive:0<ε):
    ∀ᶠ i in l, total R s B e K compact sep u q cap (D i) (m i) < ε:=
  (original R s B e K compact sep u q simple deep late cap).eventually_lt_const positive
end YM.Integration.WilsonPhysicalStationMixedCourtFare
end
