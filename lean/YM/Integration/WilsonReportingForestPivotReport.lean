import YM.Integration.WilsonReportingForestPivots

/-! Measured full reporting field on the identical, larger forest-Jacobian
cells, through every registered placement and every earlier physical stop. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories RG16
open OPE.Therm RG05Readout Address Native Pulse MergeProof Accent Axial Work.E08
open PhysicalNext.Repeat.Legato WilsonReportingPlaquetteWindows WilsonReportingRegisteredWindows
open WilsonPositionSeparatedProfileReportingPrimary WilsonPositionSeparatedProfileReportingWindow
open WilsonPositionSeparatedProfileReportingCut WilsonPhysicalLocalPlaquetteForest WilsonReportingRegisteredAction WilsonReportingForestBlocks
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
theorem covers {m per:ℕ} (d:ℕ) (o:Site (R.family.side (m+1) per)) :
    cover ((R.family.localSection d).footprint o) ⊆ faces R m per d o := by
  intro z hz
  obtain ⟨a,ha,dx⟩:=halo_spec.mp (Finset.mem_product.mp hz).1
  have dist:=(separation_triangle o a z.1).trans (Nat.add_le_add (reaches R d o a ha) dx)
  let L:=(R.family.path.levels.clock.op m per).ratio.count.val
  have cap:depth R d+2≤radius (extent (depth R d+3) L) L:=by unfold radius extent;omega
  have cell:=WilsonAxialWindow.cell o _ (Work.E08.lift_mem_box (dist.trans cap)) z.2
  simpa only [faces,wrap_lift,sub_add_cancel] using cell

/-- This is the full measured fitted report, with the global placement sum
and every old spectator still in its actual normalized transport. -/
theorem measured (stoves:Poetry R.family.path.levels) (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (RG16.Lambda R.family.path.levels m))
    (D:I→ℕ) (ℓ:(i:I)→Letter (D i)) (φ:Wave I) (compact:HasCompactSupport φ.val)
    (s q:ℕ) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀N per,m<N→∀t:ℕ,(t:ℝ)≤R.family.path.levels.clock.hatBeta (m+1)^s→
    ∀(x:(i:I)→R.family.label (kept (ℓ i))) r ξ,
    let e:=fun i=>kept (ℓ i)
    let y:=fun i=>(WilsonReportingFactorySingleton.measured R.makes (ℓ i) (x i) (m+1) N per) (ℓ i)
    let cells:=fun (z:placements (V:=I) R.family (m+1) per t) i=>faces R m per (e i) (z.val i)
    ∀(n u:ℕ)(date:n+1 ≤ m+1)(span:u≤n)(g:Body),
      (∫V,‖field R.family N per date span (read R e (m+1) N per t y φ r ξ) g V-
        field R.family N per date span (primary R e (m+1) N per t y φ r ξ cells) g V‖ ∂scene R.family.path N per u)≤
      (∏i,mass R.family (e i) (x i))*(ε*Pert.Asymptotics.regulatorRun R.family N per (m+1)^q) := by
  let rad (i:I):=depth R (kept (ℓ i))+3
  filter_upwards [WilsonReportingForestBlocks.dates R.family simple slow (univ.sup rad) zero_lt_one,
    (tendsto_add_atTop_nat 1).eventually (WilsonPositionSeparatedProfileFittedPrimary.tested R stoves simple D ℓ φ compact 1 s q ep)] with m shape price N per now t ht x r ξ
  apply price N per now t ht x r ξ _ (fun z i=>covers R (kept (ℓ i)) (z.val i))
  intro z i
  simpa only [pow_one,rad,faces] using (shape per (rad i) (le_sup (f:=rad) (mem_univ i))).2.2 (z.val i)

end YM.Integration.WilsonReportingForestPivots
