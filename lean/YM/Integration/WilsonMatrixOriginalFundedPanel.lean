import YM.Integration.WilsonMatrixOriginalFiledPanel
import YM.Integration.WilsonFundedMeasuredWindow
import YM.RG17.Canvas
import YM.RG17.Pitch

/-! The first signed grade-four physical observation on a single funded Wilson run. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalFundedPanel
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionPairCovariance
open WilsonLimitConstruction WilsonMatrixOriginalSignedPanel WilsonInvariantActionCalibratedColumn
open WilsonMatrixOriginalSignedReading WilsonMatrixOriginalRealFields
open Trace.Sundial WilsonMatrixOriginalFiledPanel Next.Rank OPE.Orbits RG12 SharpGram
open scoped Classical Topology BigOperators

variable {G : Gauge} {R : Run G}

/-- The physical covariance observed through the two filed, cutoff-dependent labels,
with a fixed real or imaginary component and a common bound on their incoming charges. -/
def Observation {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (Z : WilsonPrescription G) (H : (Bel R.family.book).Hierarchy)
    (L : Layout F) : Prop :=
    ∃ (D:Profiles R 4) (j:D.probes.index) (v₀:(standard R.family.labels).Ref 4)
      (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)
      (e:ℕ) (deposit:ℝ→RG17.Free R.family 4→R.family.label 4) (χ:ℂ→L[ℝ]ℝ),
      let φ := WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
      let v := (Bel R.family.book).project 4 v₀
      let b := fun r => homogeneous F J Z r 4 v
      let c := tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
      (χ=Complex.reCLM ∨ χ=Complex.imCLM) ∧
      Filed (U:=L.lens) F J L (fun r => deposit r (stepField R.family)) (fun r => deposit r (freeInput F J Z 4 r v)) b φ c χ ∧
      (∀ᶠ r in trail,∀u:RG17.Free R.family 4,master L 4 r (deposit r u)=J r 4 u ∧
        ∀N n,L.level r ≤ N→quota R.family 4 (L.level r) N n (atRef L 4 r (N,n) (deposit r u)) ≤
          R.family.S.a (L.level r)^4*(R.family.path.levels.clock.hatBeta (L.level r)^e*‖u‖))

/-- The same run supplies its bank and its measured reporting level. -/
theorem measured_layout (simple : G.Simple) {ρ : ℝ} {T : Campaign R} (W : Campaign.Pillars R T)
    (funded : FundedOriginalProperties.{u} simple ρ W) (pace : WilsonWindowReportingPace.Slow R.kit)
    {B : ℕ} (hB : 0 < B) {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (fac : OPE.Facilities R.family f S) :
    ∃ (u₀ : Ultrafilter UVIndex) (bank : Mantle F (u₀ : Filter UVIndex)) (L : Layout F),
      Pegs bank L ∧ L.level = WilsonMeasuredWindow.stop R.family.path.levels simple B ∧
      L.lens ≤ f.fuse ∧ L.shift = (fun _ _ => LinearEquiv.refl ..) := by
  let u₀ := Ultrafilter.of f.fuse
  have hu : (u₀ : Filter UVIndex) ≤ f.fuse := Ultrafilter.of_le _
  obtain ⟨bank⟩ := Lenses.attains_mantle17 F fac.toServices u₀ hu funded.2.1.coverage
  let level := WilsonMeasuredWindow.stop R.family.path.levels simple B
  have height := WilsonMeasuredWindow.measured_stop_height R.family.path.levels simple B
    (WilsonFundedMeasuredWindow.paced R pace) hB RG17.ageLarge RG17.lengthRate
  have reached : Reach R.family level :=
    ⟨WilsonMeasuredWindow.stop_tendsto R.family.path.levels simple B hB,height.pace⟩
  obtain ⟨L,hl,hs,hp⟩ := RG17.installed (B:=bank) hu level reached (fun _ _ => LinearEquiv.refl ..)
  exact ⟨u₀,bank,L,hp,hl,hp.along.trans hu,hs⟩

/-- At every original extraction the paid run supplies the grade-four calibration,
the two signed filed labels, and the genuine cofinal lower measurement on their common lens. -/
theorem on_run (simple : G.Simple) {ρ : ℝ} {T : Campaign R} (W : Campaign.Pillars R T)
    (funded : FundedOriginalProperties.{u} simple ρ W) (pace : WilsonWindowReportingPace.Slow R.kit)
    (Z : WilsonPrescription G) {B : ℕ} (hB : 0 < B) (v : Extraction.Order) :
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (H : (Bel R.family.book).Hierarchy) (arch : Trace.Terrace.Arch R.family)
      (l : Ultrafilter (ℕ × ℕ)) (J : ℝ → tower S) (A : ℝ → Spin.change S 4) (δ : ℝ → ℝ)
      (u₀ : Ultrafilter UVIndex) (bank : Mantle F (u₀ : Filter UVIndex)) (L : Layout F),
      Bliss F l arch H ∧ Leading F J ∧ (∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d) ∧
      (∀ᶠ r in trail, J r 4 = A r) ∧ (∀ᶠ r in trail, AlignV F.room.kernel F.sector H (A r)) ∧
      TendC F A δ ∧ Coupling G (glo A) ∧ Pegs bank L ∧
      L.level = WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens ≤ (v.refine w).fuse ∧
      Observation F J Z H L := by
  have record := funded
  obtain ⟨_,_,_,_,_,_,_,_,_,selected,_⟩ := record
  obtain ⟨w,S,F,_,_,_,_,_,fac,_,H,arch,l,bliss,_,A,J,_,_,δ,_,same,_,comp,lead,obey⟩ := selected v
  obtain ⟨u₀,bank,L,pegs,level,lens,_⟩ := measured_layout simple W funded pace hB F fac
  letI : L.lens.NeBot := L.notbot
  refine ⟨w,S,F,H,arch,l,J,A,δ,u₀,bank,L,bliss,lead,obey,same,comp.alignment.spun,comp.leading,
    comp.coupling,pegs,level,lens,?_⟩
  exact WilsonMatrixOriginalFiledPanel.original (F:=F) (J:=J) (Z:=Z) (L:=L) (lead:=lead)
    (paid:=obey) (simple:=simple) (funded:=funded) (pace:=pace) (hB:=hB) (level:=level)
    (U:=L.lens) (chosen:=le_rfl) (bank:=bank) (E:=fac.toServices) (pegs:=pegs)
    same comp.alignment.spun comp.leading comp.coupling

end YM.Integration.WilsonMatrixOriginalFundedPanel
end
