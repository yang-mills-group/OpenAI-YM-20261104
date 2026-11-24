import YM.Integration.WilsonOrdinaryUltravioletPair
import YM.Integration.WilsonMovingReportLedger

/-! The genuine fine Wilson configurations at the original physical
detectors. The spacing tends to zero on the same previously chosen lens. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryUltravioletLimit
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits OPE.Strobe RG12 RG17 RG17.Panoramic SharpGram Climb PhysMS
open OPE.Levy Push.FiniteDetection.Free Trace.Pilot
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open WilsonReportRegularMoments WilsonReportReflectedGram WilsonReportEarlySmearing WilsonReportColumnCut
open WilsonOrdinaryMixedGram WilsonOrdinaryNormalizedStep WilsonOrdinaryFourGram
open WilsonOrdinaryHomogeneousDetectors WilsonOrdinaryMeasuredMarch
open Cells Push.GridApprox
open scoped Topology Classical BigOperators
universe u
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

variable {F : Final R.family f S} (L : Layout F)

/-- At every fixed original, separated physical position the fine-grid
Wilson moment converges directly to the actual class moment. -/
theorem at_position (hG : G.Simple) {n : ℕ} (r : ℝ) (d : Caps n)
    (w : R.family.book.Vector d) (grade : ∀ j, R.family.ref (d j) ≤ L.level r)
    (X : Points n) (inside : X∈conf n) :
    Tendsto (fun z : UVIndex=>R.family.numeric z.1 z.2
      (fun j=>⟨d j,RG17.atRef L (d j) r z (w j)⟩)
      (wrap _ ∘ address (R.family.S.a z.1) X)) L.lens
      (𝓝 (S.classMoment S d X (fun j=>master L (d j) r (w j)))) := by
  let Y (z : UVIndex) : Points n := tag (R.family.S.a z.1) (address (R.family.S.a z.1) X)
  have calendar : Tendsto (fun z : UVIndex=>z.1) L.lens atTop :=
    tendsto_atTop.mpr fun k=>(large_mesh f k).filter_mono L.certified
  have narrow := R.family.S.shrinks.comp calendar
  have bound : Tendsto (fun z : UVIndex=>(4*n:ℝ)*R.family.S.a z.1) L.lens (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*n:ℝ))).mul narrow
  have near : Tendsto Y L.lens (𝓝 X) := by
    apply Metric.tendsto_nhds.mpr
    intro ε he
    filter_upwards [bound.eventually (gt_mem_nhds he)] with z fine
    exact (Extraction.approximate (R.family.S.a_pos z.1) X).trans_lt fine
  obtain ⟨δ,hδ,part⟩ := Metric.mem_nhds_iff.mp ((conf_open n).mem_nhds inside)
  let K := Metric.closedBall X (δ/2)
  have contains : K⊆conf n := (Metric.closedBall_subset_ball (half_lt_self hδ)).trans part
  have stays : ∀ᶠ z:UVIndex in L.lens,Y z∈K := near.eventually (Metric.closedBall_mem_nhds X (half_pos hδ))
  have regular : ContinuousAt (fun y=> S.classMoment S d y (fun j=>master L (d j) r (w j))) X :=
    ((F.room.kernel.smooth.on_conf d _).continuousOn).continuousAt ((conf_open n).mem_nhds inside)
  have target := regular.tendsto.comp near
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have half : 0<ε/2 := half_pos he
  have measured := WilsonMovingReportLedger.original R hG L r d w grade K (isCompact_closedBall _ _) contains (ε/2) half
  filter_upwards [measured,stays,Metric.tendsto_nhds.mp target (ε/2) half] with z buy stays close
  have exactCut := buy (address (R.family.S.a z.1) X) stays
  exact (dist_triangle _ (S.classMoment S d (Y z) (fun j=>master L (d j) r (w j))) _).trans_lt
    ((add_lt_add exactCut close).trans_eq (add_halves ε))

/-- The real signed coefficients of the two complete original microscopic
marks may themselves vary with both regulator parameters. Their normalized
Wilson sum has this exact separated physical limit. -/
theorem two (hG : G.Simple) (r : ℝ) (d : ℕ) (v w : R.family.label d)
    (grade : R.family.ref d ≤ L.level r) (X : Points 2) (inside : X∈conf 2)
    (coupling : UVIndex→ℝ) (admitted : ∀ z,coupling z≠0) :
    Tendsto (fun z : UVIndex=>let a := RG17.atRef L d r z v; let b := RG17.atRef L d r z w
      let x := wrap (R.family.side z.1 z.2) ∘ address (R.family.S.a z.1) X
      ∑ q,∑ t,(WilsonOrdinaryUltravioletPair.coefficient R d z.1 z.2 a (coupling z) q *
        WilsonOrdinaryUltravioletPair.coefficient R d z.1 z.2 b (coupling z) t) *
      Wilson.moment (R.family.beta z.1 z.2) (fun U=>
        WilsonOrdinaryUltravioletPair.enrolled R d z.1 z.2 (coupling z) q (x 0) U *
        WilsonOrdinaryUltravioletPair.enrolled R d z.1 z.2 (coupling z) t (x 1) U)) L.lens
      (𝓝 (S.classMoment S (fun _ : Fin 2=>d) X (fun j=>master L d r ((![v,w] : Fin 2→_) j)))) := by
  have known := at_position L hG r (fun _ : Fin 2=>d) ![v,w] (fun _=>grade) X inside
  apply known.congr
  intro z
  change (Wilson.moment (R.family.beta z.1 z.2) (fun U=>∏ j : Fin 2,
    R.family.O z.1 z.2 (atRef L d r z ((![v,w] : Fin 2→_) j))
      (wrap _ (address (R.family.S.a z.1) X j)) U))=_
  simp only [Fin.prod_univ_two]
  exact WilsonOrdinaryUltravioletPair.measured R d d z.1 z.2 _ _ (admitted z) _ _

end YM.Integration.WilsonOrdinaryUltravioletLimit
