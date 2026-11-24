import YM.Integration.WilsonMatrixOriginalEarlierPanel
import YM.Integration.WilsonMatrixOriginalFundedPanel

/-! One funded Wilson run and one set of deposits for the measured and inherited signed rows. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonMatrixOriginalFundedEarlierPanel
open Filter Function Set MeasureTheory Lattice Wilson RG RG17 Source Marker Extraction Extraction.Order
open Table Spec Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm
open Next.UVStress Next.Rank.Price PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register
open WilsonLimitConstruction Trace.Sundial Next.Rank OPE.Orbits RG12 SharpGram
open WilsonMatrixOriginalFundedPanel WilsonMatrixOriginalEarlierPanel
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G}

theorem upper {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    (J : ℝ → tower S) (Z : WilsonPrescription G) (H : (Bel R.family.book).Hierarchy)
    (L : Layout F) (δ g : ℝ → ℝ) (rec : Captured (H:=H) (U:=L.lens) F J Z L δ g) :
    Observation F J Z H L := by
  obtain ⟨D,j,v,hs,e,deposit,χ,_σ,member,_sign,_oriented,_gain,_limit,_ward,filed,paid,_lower⟩:=rec
  exact ⟨D,j,v,hs,e,deposit,χ,member,filed,paid⟩

theorem on_run (simple : G.Simple) {ρ : ℝ} {T : Campaign R} (W : Campaign.Pillars R T)
    (funded : FundedOriginalProperties.{u} simple ρ W) (subsidy : WilsonReportColumnSubsidy.Eligible R.kit)
    (pace : WilsonWindowReportingPace.Slow R.kit) (Z : WilsonPrescription G) {B : ℕ} (hB : 0 < B)
    (v : Extraction.Order) :
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (H : (Bel R.family.book).Hierarchy) (arch : Trace.Terrace.Arch R.family)
      (l : Ultrafilter (ℕ × ℕ)) (J : ℝ → tower S) (A : ℝ → Spin.change S 4) (δ : ℝ → ℝ)
      (u₀ : Ultrafilter UVIndex) (bank : Mantle F (u₀ : Filter UVIndex)) (L : Layout F),
      Bliss F l arch H ∧ Leading F J ∧ (∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d) ∧
      (∀ᶠ r in trail, J r 4 = A r) ∧ (∀ᶠ r in trail, AlignV F.room.kernel F.sector H (A r)) ∧
      TendC F A δ ∧ Coupling G (glo A) ∧ Pegs bank L ∧
      L.level = WilsonMeasuredWindow.stop R.family.path.levels simple B ∧ L.lens ≤ (v.refine w).fuse ∧
      Captured (H:=H) (U:=L.lens) F J Z L δ (glo A) := by
  have record := funded
  obtain ⟨_,_,_,_,_,_,_,_,_,selected,_⟩:=record
  obtain ⟨w,S,F,_,_,_,_,_,fac,_,H,arch,l,bliss,_,A,J,_,_,δ,_,same,_,comp,lead,obey⟩:=selected v
  obtain ⟨u₀,bank,L,pegs,level,lens,_⟩:=measured_layout simple W funded pace hB F fac
  letI : L.lens.NeBot := L.notbot
  refine ⟨w,S,F,H,arch,l,J,A,δ,u₀,bank,L,bliss,lead,obey,same,comp.alignment.spun,comp.leading,
    comp.coupling,pegs,level,lens,?_⟩
  exact WilsonMatrixOriginalEarlierPanel.original (F:=F) (J:=J) (Z:=Z) (L:=L) (lead:=lead)
    (paid:=obey) (simple:=simple) (funded:=funded) (subsidy:=subsidy) (pace:=pace) (hB:=hB) (level:=level)
    (U:=L.lens) (chosen:=le_rfl) (bank:=bank) (E:=fac.toServices) (pegs:=pegs)
    same comp.alignment.spun comp.leading comp.coupling

end YM.Integration.WilsonMatrixOriginalFundedEarlierPanel
