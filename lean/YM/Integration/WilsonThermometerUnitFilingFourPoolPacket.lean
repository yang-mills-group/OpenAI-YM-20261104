import YM.Integration.WilsonThermometerUnitFilingFourPoolBill
import YM.Integration.WilsonInvariantActionCalibratedColumn

/-! A single compact separated determining packet for the actual action and its
actual grade-four exterior. Both labels and the optional farther diploma share one
finite factory and reflected card at the same smaller physical radius. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourPoolPacket
open Function Filter Set MeasureTheory Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonThermometerUnitFilingFourPool WilsonThermometerUnitFilingFourPoolShell
open WilsonThermometerUnitFilingFourPoolClock WilsonThermometerUnitFilingFourPoolBill
open private detected response from YM.Integration.WilsonInvariantActionCalibratedColumn
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
  {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
  {H : (Bel R.family.book).Hierarchy}

def wage (z : Trace.Terrace.Arch R.family) (T A : ℕ) (r : ℝ)
    (v : RG17.Free R.family 4) : ℝ :=
  let s := radius z T r
  (dock s^T*Ascent.cost F 4 s (homogeneous F J Z (outer z A r) 4 v))*
    (wilson z r)^(exponent T A 4)

theorem original (simple : G.Simple) (bliss : Bliss F l z H) (lead : Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d)
    {h : ℕ} (admit : 4≤h) :
    ∃ (T : ℕ) (D : Profiles R 4) (j : D.probes.index)
      (w : (standard R.family.labels).Ref 4) (place : D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 w)
      (K : ℝ), 0<K ∧
      let p := test D j
      let c := (WilsonInvariantActionCalibratedColumn.packet w place p).applyTo (WilsonInvariantActionPairProbe.reading R.family w)
      let v := stepField R.family
      let x := (Bel R.family.book).project 4 w
      c≠0 ∧ Tendsto (fun r=>row F J Z D r (homogeneous F J Z r 4 v) j) trail (𝓝 c) ∧
      ∀ A : ℕ, ∃ B : ℝ, 0≤B ∧ ∀ᶠ r in trail, ∃ j₀ m,
        let s := radius z T r
        Receipt F l s j₀ m h (dock s^T) ∧ BookedArm F l s j₀ m 4 (dock s^T) ∧
        (∀ y : S.Field 4, ‖(homogeneous F J Z r 4).symm y‖ ≤ K*‖row F J Z D r y‖) ∧
        ‖row F J Z D r (homogeneous F J Z r 4 v) j-c‖<‖c‖/2 ∧
        wage F J Z z T 0 r v ≤ B ∧ wage F J Z z T 0 r x ≤ B ∧ wage F J Z z T A r x ≤ B := by
  obtain ⟨T,ready⟩ := WilsonThermometerUnitFilingFourPool.original F simple bliss h
  obtain ⟨D,sites,K,kp,decode⟩ := WilsonMatrixTicketLanesSmearedPair.fixed F J Z lead paid simple 4
  obtain ⟨j,marked⟩ := detected F J Z lead paid simple D K decode
  obtain ⟨w,place⟩ := sites j
  let x := (Bel R.family.book).project 4 w
  let v := stepField R.family
  have literal := response (H:=H) w place (test D j)
  have signed := converges F J Z lead paid simple (D.probes.shell j) (test D j) v
  refine ⟨T,D,j,w,place,K,kp,?_⟩
  dsimp only
  rw [←literal]
  refine ⟨marked,signed,fun A=>?_⟩
  obtain ⟨B₀,h₀,f₀⟩ := WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead paid T 0 4 v
  obtain ⟨B₁,h₁,f₁⟩ := WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead paid T 0 4 x
  obtain ⟨B₂,h₂,f₂⟩ := WilsonThermometerUnitFilingFourPoolBill.original F J Z simple bliss lead paid T A 4 x
  refine ⟨B₀+B₁+B₂,by positivity,?_⟩
  have square : Tendsto (fun r=>row F J Z D r (homogeneous F J Z r 4 (stepField R.family)) j) trail
      (𝓝 (tree (D.probes.shell j) (test D j) H 4 (stepField R.family))) := signed
  have testClose := Metric.tendsto_nhds.1 square _ (half_pos (norm_pos_iff.mpr marked))
  filter_upwards [(smaller F simple bliss T).eventually ready,decode,testClose,f₀,f₁,f₂] with
    r hr rotation heard c₀ c₁ c₂
  obtain ⟨i,m,word⟩ := hr
  refine ⟨i,m,word,word.budget 4 admit,rotation,by simpa only [dist_eq_norm] using heard,?_,?_,?_⟩
  · exact c₀.trans (by linarith)
  · exact c₁.trans (by linarith)
  · exact c₂.trans (by linarith)

end YM.Integration.WilsonThermometerUnitFilingFourPoolPacket
