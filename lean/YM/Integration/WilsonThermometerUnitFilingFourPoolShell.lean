import YM.Integration.WilsonThermometerUnitFilingFourPool
import YM.Integration.WilsonThermometerUnitFilingFourQuotient

/-! The original Wilson action on one nonzero row of the actual determining exterior.
The diploma and its two cutoff receipts are co-issued at the smaller physical length. -/
set_option autoImplicit false
set_option maxHeartbeats 240000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourPoolShell
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesNormalizedPivot
open WilsonThermometerUnitFilingFourPool
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
  {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
  {H : (Bel R.family.book).Hierarchy}

def radius (z : Trace.Terrace.Arch R.family) (T : ℕ) (r : ℝ) :=
  r * (wilson z r) ^ (2*T+4)

theorem smaller (simple : G.Simple) (bliss : Bliss F l z H) (T : ℕ) :
    Tendsto (radius z T) trail trail := by
  have link := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have small := link.conforms simple
  have r0 : Tendsto id trail (𝓝 (0:ℝ)) := nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · change Tendsto (fun r : ℝ=>r*(wilson z r)^(2*T+4)) trail (𝓝 0)
    simpa using r0.mul (small.pow (2*T+4))
  · filter_upwards [self_mem_nhdsWithin,link.positive] with r hr hg
    exact mul_pos hr (pow_pos hg _)

theorem original (simple : G.Simple) (bliss : Bliss F l z H) (lead : Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d)
    (D : Contacts.Foci (Bel R.family.book) 4) {h : ℕ} (seen : 4≤h) :
    ∃ (T : ℕ) (a : D.index),
      let c := (Bel R.family.book).spectra 4 (stepField R.family) (D.shell a)
      let v := fun r=>homogeneous F J Z r 4 (stepField R.family)
      c≠0 ∧ Tendsto (fun r=>probe F J Z (D.shell a) r 4 (v r)) trail (𝓝 c) ∧
      ∀ᶠ r in trail, ∃ j m,
        Receipt F l (radius z T r) j m h (dock (radius z T r)^T) ∧
        ‖probe F J Z (D.shell a) r 4 (v r) - c‖ < ‖c‖/2 ∧
        BookedArm F l (radius z T r) j m 4 (dock (radius z T r)^T) := by
  obtain ⟨T,room⟩ := WilsonThermometerUnitFilingFourPool.original F simple bliss h
  have occurs : ∃ a : D.index, (Bel R.family.book).spectra 4 (stepField R.family) (D.shell a)≠0 := by
    by_contra! gone
    apply scale_alive simple H
    change stepField R.family=0
    rw [← D.detects (stepField R.family),
      show (fun a=>(Bel R.family.book).spectra 4 (stepField R.family) (D.shell a))=0 from funext gone,map_zero]
  obtain ⟨a,live⟩ := occurs
  have read := WilsonMatrixTicketLanesNormalizedPivot.point F J Z lead paid simple (D.shell a) (stepField R.family)
  refine ⟨T,a,live,read,?_⟩
  have close := Metric.tendsto_nhds.1 read _ (half_pos (norm_pos_iff.mpr live))
  filter_upwards [(smaller F simple bliss T).eventually room,close] with r hr hc
  obtain ⟨j,m,menu⟩ := hr
  exact ⟨j,m,menu,by simpa only [dist_eq_norm] using hc,menu.budget 4 seen⟩

end YM.Integration.WilsonThermometerUnitFilingFourPoolShell
