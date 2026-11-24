import YM.Integration.WilsonMatrixTicketLanesConnectedMargin

/-! One measured nonzero Maxwell panel, its deposited fields and its complete fresh physical test share the same original calibration. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedWitness
open Filter Function Set Finset MeasureTheory Lattice Wilson RG Tree Precision RG17 Source Marker Extraction Extraction.Order Spec
open Table Climb Maxwell Maxwell.Free Trace.Pilot Trace.Over Spin PhysMS OPE OPE.Therm Next.UVStress Next.Rank.Price
open PhysicalNext.Repeat.Legato SharpGram.Lenses FVA2 FVA2.Register Pert.Asymptotics
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot WilsonMatrixTicketLanesSmearedRows
open WilsonInvariantActionPairProbe WilsonInvariantActionSpectatorPrices WilsonInvariantActionCalibratedColumn WilsonInvariantActionPairCovariance
open Trace.Sundial WilsonLimitConstruction WilsonMatrixOriginalEarlierPanel WilsonMatrixOriginalLogarithmicRate WilsonMatrixOriginalReportingMargin
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book} (F:Final R.family f S)
  (J:ℝ→tower S) (Z:WilsonPrescription G) {H:(Bel R.family.book).Hierarchy} (L:Layout F)
  {U:Filter (ℕ×ℕ)}

def Fields (B:ℕ) (δ g:ℝ→ℝ) : Prop :=
  ∃(D:Profiles R 4)(j:D.probes.index)(v₀:(standard R.family.labels).Ref 4)
    (hs:D.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.labels 4 v₀)(e:ℕ)
    (deposit:ℝ→RG17.Free R.family 4→R.family.label 4)(χ:ℂ→L[ℝ]ℝ)(σ:ℝ),
    let φ:=WilsonInvariantActionCalibratedColumn.packet v₀ hs (test D j)
    let v:=(Bel R.family.book).project 4 v₀
    let a:=fun r=>deposit r (stepField R.family)
    let b:=fun r=>deposit r (freeInput F J Z 4 r v)
    let cov:=fun r=>tested (J r 4 (stepField R.family)) (homogeneous F J Z r 4 v) r φ
    let c:=tree (D.probes.shell j) (test D j) H 4 (stepField R.family)
    Row (H:=H) (U:=U) F J Z L δ g D j v₀ hs e deposit χ σ ∧ Rate (U:=U) F L B g a b φ cov ∧
    LeadingRow (U:=U) F L a b φ c χ σ ∧ WilsonMatrixOriginalCapturedInverse.Recovered (U:=U) F L g a b χ σ φ c ∧
    WilsonMatrixTicketLanesConnectedSigned.Negligible R F L U 4 4 g a b φ ∧
    WilsonMatrixTicketLanesConnectedMargin.Remaining (U:=U) R F L a b φ c χ σ

theorem original (simple:G.Simple) (connected:WilsonMatrixTicketLanesConnectedBudget.Paid G R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) (lead:Leading F J) (obey:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (chosen:U ≤ L.lens) {B:ℕ} (wide:17 ≤ B) (level:L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B)
    {δ g:ℝ→ℝ} (coupling:Coupling G g) (selected:WilsonGaussianRecoveredPanel.Observed (H:=H) (U:=U) F J Z L B δ g) :
    Fields (H:=H) (U:=U) R F J Z L B δ g:=by
  obtain ⟨D,j,v,hs,e,deposit,χ,σ,row,rate,margin,inverse,_⟩:=selected
  have fresh:=WilsonMatrixTicketLanesConnectedWard.on_row R F J Z L simple connected pace lead obey chosen wide level coupling D j v hs e deposit χ σ row
  exact ⟨D,j,v,hs,e,deposit,χ,σ,row,rate,margin,inverse,fresh,
    WilsonMatrixTicketLanesConnectedMargin.from_row R F L g _ _ _ _ χ σ row.1 row.2.1 row.2.2.2.1 margin fresh⟩

def Measured (simple:G.Simple) (Q:MS.Land.Prescription (Press.portDeck G)) : Prop :=
  ∀(B:ℕ),17 ≤ B → ∀ v:Extraction.Order,
    ∃(w:Extraction.Order)(S:Table R.family.book)(F:Final R.family (v.refine w) S)
      (H:(Bel R.family.book).Hierarchy)(J:ℝ→tower S)(A:ℝ→Spin.change S 4)(δ:ℝ→ℝ)(L:Layout F),
      Leading F J ∧ (∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d) ∧ (∀ᶠr in trail,J r 4=A r) ∧
      TendC F A δ ∧ Coupling G (glo A) ∧ L.level=WilsonMeasuredWindow.stop R.family.path.levels simple B ∧
      L.lens ≤ (v.refine w).fuse ∧ WilsonGaussianProbeMatrix.Filed F J L Q ∧ Fields (H:=H) (U:=L.lens) R F J Z L B δ (glo A)

theorem on_run (simple:G.Simple) (connected:WilsonMatrixTicketLanesConnectedBudget.Paid G R.kit)
    (pace:WilsonWindowReportingPace.Slow R.kit) (Q:MS.Land.Prescription (Press.portDeck G))
    (registered:WilsonGaussianProbeMatrix.Measured R simple Z Q) : Measured R Z simple Q:=by
  intro B large v
  obtain ⟨w,S,F,H,J,A,δ,L,lead,obey,grade,flow,coupling,level,within,booked,observed⟩:=registered B large v
  exact ⟨w,S,F,H,J,A,δ,L,lead,obey,grade,flow,coupling,level,within,booked,
    original R F J Z L simple connected pace lead obey le_rfl large level coupling observed⟩

end YM.Integration.WilsonMatrixTicketLanesConnectedWitness
