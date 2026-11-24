import YM.Integration.WilsonThermometerInversionBirth
import YM.Integration.WilsonMaxwellThermometerInteracting

/-! The seven finite inversion moments use the inverse-fitted cutoff
fields at their separate sites. Take real and imaginary parts only
after forming each complete tensor, before the complex cumulant. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionStation
open Function Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Affinity
open Next.Rank PhysicalNext.Repeat.Legato MergeProof.East Trace.Pilot Next.UVStress
open PertExtension PertExtension.Orb PertExtension.Series PertExtension.Series.Tested
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonOriginalThermometerPalette
open XSpace.Rose PowerSeries
open scoped Classical BigOperators ContDiff Topology

variable {G:Gauge} (R:Run G) (A:Group R.family 6) (i per:ℕ)
local notation "N" => i+2
local notation "g" => Pert.Asymptotics.regulatorRun R.family (N) per (N)
local notation "τ" => (R.family.path.rep (N) per (N)).p.threshold
variable (o:Fin 3 → Site (R.family.side (i+2) per)) (x:Wallet disks)
local notation "top" => fun j=>A.station.wheel.atCut ((N),per) (index A (grade j)) (vector A univ j)
local notation "cash" => coordinates R A (N) (N) per

def placed (s:Finset (Fin 3)) (L:ℂ→L[ℝ]ℝ) :=
  WilsonThermometerInversionFaces.face R (fun j:↥s=>levels j.val)
    (fun j=>o j.val) (g) (τ) (fun j=>(cash) j.val) (fun j=>probe j.val) x L

def columns (s:Finset (Fin 3)) (L:ℂ→L[ℝ]ℝ) :=
  WilsonThermometerInversionFaces.series R (fun j:↥s=>levels j.val)
    (fun j=>o j.val) (g) (τ) (fun j=>(cash) j.val) (fun j=>probe j.val) x L

theorem measured (s:Finset (Fin 3)) (L:ℂ→L[ℝ]ℝ) (refs:∀j,R.family.ref (levels j)≤(N))
    (U:Config G (R.family.side (i+2) per)) : placed R A i per o x s L (g) U =
    L (∏j∈s,probe j x * R.family.O (N) per ((top) j) (o j) U) := by
  have h := WilsonThermometerInversionBirth.exact R (fun j:↥s=>levels j.val) (N) per
    (fun j=>o j.val) (fun j=>(top) j.val) (fun j=>probe j.val) x U L (fun j=>refs j.val)
  rw [←Finset.prod_attach]
  exact h

theorem finite (s:Finset (Fin 3)) (L:ℂ→L[ℝ]ℝ) :
    Aspiration (fun u=>preExpectation (placed R A i per o x s L u) u)
      (columns R A i per o x s L) := by
  let p:=ActualLeadingIR.actualPeriod R.family (N) per
  exact WilsonThermometerInversionFaces.finite R _ _ _ _ _ _ _ _ (even_iff_two_dvd.mpr p.even)

def panel (s:Finset (Fin 3)) : ℂ⟦X⟧ := PowerSeries.mk fun h=>
    (↑(columns R A i per o x s Complex.reCLM h):ℂ)+Complex.I*↑(columns R A i per o x s Complex.imCLM h)

theorem slope : coeff 1 (b3 (panel R A i per o x)) =
    WilsonMaxwellThermometerInteracting.first
      (fun s=>(↑(columns R A i per o x s Complex.reCLM 0):ℂ)+Complex.I*↑(columns R A i per o x s Complex.imCLM 0))
      (fun s=>(↑(columns R A i per o x s Complex.reCLM 1):ℂ)+Complex.I*↑(columns R A i per o x s Complex.imCLM 1)) := by
  simpa only [panel,coeff_mk] using WilsonMaxwellThermometerInteracting.coefficient (panel R A i per o x)

end YM.Integration.WilsonThermometerInversionStation
