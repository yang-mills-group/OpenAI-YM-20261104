import YM.Integration.WilsonMeasuredPublicEntranceEnrollment
import YM.Integration.WilsonMeasuredPublicSlots

/-! The deposited original source is the literal public Slot.arm.source. A single
grade onset is chosen before all cutoffs, periods, input tests and placements. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceSelected
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    {D : ℕ} (l:Ultrafilter (ℕ×ℕ))
local notation "C₀" => R.family

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    :
    ∃ t ≥ D+3, ∀ᶠ j : ℕ in atTop, ∀ p N (deep : j < N),
    ∃ (V : (a : Fin (D+1)) → Sight C₀ a.val p) (u : (a : Fin (D+1)) → Emblems C₀ a.val)
      (est : ∀ a : Fin (D+1), Opened C₀ a.val (j) p),
    (∀ a, Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) (j) N p a.val
      (digits R N p 0) (V a) (u a)) ∧
    ∀ (I : Type) [Fintype I] [DecidableEq I] (d : I → Fin (D+1)) (radius wallet : ℝ) (v : (i : I) → S.Field (d i).val)
      (c : I → Site ((C₀).side (j) p)) (names : Census I),
    ∀ (L : (i:I) → WilsonMeasuredPublicSlots.Slot F l (d i).val (v i) radius wallet),
    (∀i,(L i).j=j) →
    (∀ i j' : I, i≠j' → ((C₀).path.levels.budget (j)).B^2 <
      separation (point R (N:=N) 0 (1,false) (c i) (j)) (point R (N:=N) 0 (1,false) (c j') (j))) →
    let x:=fun i=>(L i).arm.source (N,p)
    let y := fun i => offer R (x i) (est (d i)) deep.le
    let b := fun i => anchorAt R (c i) N
    let data := fun i => reduce (y i)
    (∀ i, charge (y i) ≤ max 1 (2*(wallet*GapsContact.Ascent.cost F (d i).val (radius) (v i)))) ∧
    WilsonThermometerReflectedRoster.filed R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
      data (fun i => V (d i)) (fun i => u (d i)) names deep.le t ∧
    ∀ j (hj : j ≤ N) (s : names.Mode) T,
      (WilsonThermometerReflectedRoster.density R (fun i => (d i).val) (fun _ => 0) (fun _ => (1,false)) c
        data (fun i => u (d i)) names deep.le hj T).part s =
      ((C₀).path.rep N p j).eval T • actualTransport C₀ (N:=N)
        (fun W => ∏ i∈s.val, ((charge (y i):ℝ):ℂ)⁻¹ * (C₀).O N p (x i) (b i) W) hj T := by
  obtain ⟨t,tp,cash⟩:=WilsonMeasuredPublicEntranceEnrollment.original (D:=D) R F simple shop
  refine ⟨t,tp,cash.mono ?_⟩
  intro j ready p N deep
  obtain ⟨V,u,est,applied,issued⟩:=ready p N deep
  refine ⟨V,u,est,applied,?_⟩
  intro I fi di d radius wallet v c names L atDate room
  apply issued I d radius wallet v c names (fun i=>(L i).arm.source (N,p)) _ room
  intro i
  simpa only [atDate i] using (L i).numerical N p (by simpa only [atDate i] using deep)

end YM.Integration.WilsonMeasuredPublicEntranceSelected
end
